import asyncio
import torch
from collections import defaultdict, OrderedDict

class LRUBackpropBufferCache:
    def __init__(self, device, pad_token_id, max_size=10):
        self.device = device
        self.pad_token_id = pad_token_id
        self.cache = OrderedDict()
        self.max_size = max_size

    def get_buffer(self, batch_size, seq_len):
        key = (batch_size, seq_len)
        if key in self.cache:
            self.cache.move_to_end(key)
            return self.cache[key]
        buffer = torch.empty(batch_size, seq_len, dtype=torch.long, device=self.device)
        self.cache[key] = buffer
        if len(self.cache) > self.max_size:
            self.cache.popitem(last=False)
        return buffer

    def prepare_backprop_batch(self, sequences):
        batch_size = len(sequences)
        seq_len = max(seq.shape[1] for seq in sequences)
        buffer = self.get_buffer(batch_size, seq_len)
        for i, seq in enumerate(sequences):
            length = seq.shape[1]
            buffer[i, :length] = seq[0]
            if length < seq_len:
                buffer[i, length:] = self.pad_token_id
        return buffer

class MicrobatchBackpropRunner:
    def __init__(self, model, optimizer, device, accum_steps):
        self.model = model.to(device)
        self.optimizer = optimizer
        self.device = device
        self.accum_steps = accum_steps
        self.grad_accum_counter = 0
        self.queue = asyncio.Queue()
        self.running = False

    async def add_microbatch(self, batch):
        await self.queue.put(batch)

    def compute_loss(self, batch):
        outputs = self.model(input_ids=batch['input_ids'], decoder_input_ids=batch['decoder_input_ids'])
        logits = outputs.logits
        logprobs = torch.nn.functional.log_softmax(logits, dim=-1)
        logprobs_taken = logprobs.gather(2, batch['decoder_input_ids'].unsqueeze(-1)).squeeze(-1)
        baseline = batch['rewards'].mean()
        advantages = batch['rewards'] - baseline
        loss = -(logprobs_taken.sum(dim=1) * advantages).mean()
        return loss

    async def run(self):
        self.running = True
        while self.running:
            batch = await self.queue.get()
            if self.grad_accum_counter == 0:
                self.optimizer.zero_grad()
            loss = self.compute_loss(batch)
            (loss / self.accum_steps).backward()
            self.grad_accum_counter += 1
            if self.grad_accum_counter == self.accum_steps:
                self.optimizer.step()
                self.optimizer.zero_grad()
                self.grad_accum_counter = 0
                print(f"Backprop training step done, loss: {loss.item():.4f}")
            self.queue.task_done()

    def stop(self):
        self.running = False

class BackpropScheduler:
    def __init__(self, model, backprop_runner, device,
                 micro_batch_size=8,
                 max_queue_size=1000):
        self.model = model
        self.device = device
        self.micro_batch_size = micro_batch_size
        self.rollout_queue = asyncio.Queue(maxsize=max_queue_size)
        self.backprop_runner = backprop_runner

        pad_token_id = model.config.pad_token_id
        self.input_cache = LRUBackpropBufferCache(device, pad_token_id)
        self.decoder_cache = LRUBackpropBufferCache(device, pad_token_id)

    async def add_microbatch(self, microbatch):
        await self.rollout_queue.put(microbatch)

    def _bucket_by_length(self, microbatches):
        buckets = defaultdict(list)
        for microbatch in microbatches:
            seq_len = microbatch['decoder_input_ids'].shape[1]
            bucket_key = (seq_len // 10) * 10
            buckets[bucket_key].append(microbatch)
        return buckets

    def _prepare_backprop_batch(self, batch_microbatches):
        input_seqs = [r['input_ids'] for r in batch_microbatches]
        decoder_seqs = [r['decoder_input_ids'] for r in batch_microbatches]
        rewards = torch.stack([r['reward'] for r in batch_microbatches]).to(self.device)

        input_ids = self.input_cache.prepare_backprop_batch(input_seqs)
        decoder_input_ids = self.decoder_cache.prepare_backprop_batch(decoder_seqs)

        return {'input_ids': input_ids, 'decoder_input_ids': decoder_input_ids, 'rewards': rewards}

    async def run(self):
        buffer = []
        while True:
            microbatch = await self.rollout_queue.get()
            buffer.append(microbatch)

            if len(buffer) >= self.micro_batch_size:
                buckets = self._bucket_by_length(buffer)
                for bucket_microbatches in buckets.values():
                    for i in range(0, len(bucket_microbatches), self.micro_batch_size):
                        batch_microbatches = bucket_microbatches[i:i+self.micro_batch_size]
                        batch = self._prepare_backprop_batch(batch_microbatches)
                        await self.backprop_runner.add_microbatch(batch)
                buffer.clear()
                self.rollout_queue.task_done()

from datasets import load_dataset
from transformers import AutoTokenizer, AutoModelForSeq2SeqLM
from transformers import Seq2SeqTrainer, Seq2SeqTrainingArguments


# ========== Step 1: Load and Process Dataset ==========

dataset = load_dataset("tasksource/leandojo", split="train")

def to_training_pairs(batch):
    inputs, targets = [], []
    for row in batch["traced_tactics"]:
        for tac in row:
            gb = tac.get("state_before")
            ga = tac.get("state_after")
            tactic = tac.get("tactic")

            if not (gb and ga and tactic):
                continue

            tactic = tactic.strip()
            gb = gb.strip()
            ga = ga.strip()

            if tactic.startswith("have"):
                # Replace the proof with `:= sorry`
                transformed = (":=".join(tactic.split(":=")[:-1]) + ":= sorry") if ":=" in tactic else tactic
                inputs.append(gb)
                targets.append(transformed)
                continue

            tactic.startswith("have")

            # Otherwise, extract new hypotheses and synthesize a `have`
            temp_gb = gb.split("⊢")
            temp_ga = ga.split("⊢")
            if len(temp_gb) != 2 or len(temp_ga) != 2:
                continue

            hyps_before, _ = temp_gb
            hyps_after, goal_after = temp_ga

            if not hyps_after.startswith(hyps_before):
                continue

            new_hyps = hyps_after[len(hyps_before):].strip().split("\n")
            new_hyps = [hyp.strip() for hyp in new_hyps if hyp.strip()]
            if not new_hyps:
                continue

            hyp_text = " ".join([f"({h})" for h in new_hyps])
            synthesized = f"have {hyp_text} : {goal_after.strip()} := sorry"
            inputs.append(gb)
            targets.append(synthesized)
    return {"input": inputs, "target": targets}

dataset = dataset.map(to_training_pairs, batched=True, remove_columns=dataset.column_names)

# ========== Step 2: Tokenization ==========

tokenizer = AutoTokenizer.from_pretrained("google/byt5-small")

def tokenize(batch):
    return tokenizer(batch["input"], text_target=batch["target"],
                     truncation=True, padding="max_length", max_length=512)

tokenized = dataset.map(tokenize, batched=True)
tokenized.set_format("torch")

# ========== Step 3: Train/Test Split ==========

split = tokenized.train_test_split(test_size=0.05)
train_ds = split["train"]
eval_ds = split["test"]

from datasets import Dataset

# Convert to HF Dataset object (it already is, but we ensure a clean copy)
clean_dataset = Dataset.from_dict({
    "input": dataset["input"],
    "target": dataset["target"]
})

# Save locally
clean_dataset.save_to_disk("lean-have-pairs")

# (Optional) Push to Hugging Face Hub
clean_dataset.push_to_hub("tactic-have-pairs")

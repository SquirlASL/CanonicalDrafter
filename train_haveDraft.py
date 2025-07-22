from datasets import load_dataset
from transformers import AutoTokenizer, AutoModelForSeq2SeqLM
from transformers import Seq2SeqTrainer, Seq2SeqTrainingArguments
import json

# ========== Step 1: Load Dataset ==========

dataset = load_dataset("UnluckyOrangutan/tactic-haveDraft", split="train")

# ========== Step 2: Process dataset into input/target pairs ==========

def to_training_pairs(batch):
    inputs = []
    targets = []
    # batch["goal"] is list of strings
    # batch["haveDrafts"] is list of lists or dicts -> convert to JSON string for text generation
    for goal, haveDrafts in zip(batch["goal"], batch["haveDrafts"]):
        inputs.append(goal)
        # Serialize haveDrafts to JSON string as the target
        targets.append(json.dumps(haveDrafts))
    return {"input": inputs, "target": targets}

dataset = dataset.map(to_training_pairs, batched=True, remove_columns=dataset.column_names)

# ========== Step 3: Tokenization ==========

tokenizer = AutoTokenizer.from_pretrained("google/byt5-small")

def tokenize(batch):
    # Use `text_target` arg for seq2seq models (since transformers v4.5+)
    return tokenizer(
        batch["input"],
        text_target=batch["target"],
        truncation=True,
        padding="max_length",
        max_length=512,
    )

tokenized = dataset.map(tokenize, batched=True)
tokenized.set_format("torch")

# ========== Step 4: Train/Test split ==========

split = tokenized.train_test_split(test_size=0.05)
train_ds = split["train"]
eval_ds = split["test"]

# ========== Step 5: Load Model ==========

model = AutoModelForSeq2SeqLM.from_pretrained("google/byt5-small")

# ========== Step 6: Training Arguments ==========

training_args = Seq2SeqTrainingArguments(
    output_dir="./byt5-tactic-haveDraft",
    eval_steps=500,
    logging_steps=100,
    save_steps=1000,
    per_device_train_batch_size=8,
    per_device_eval_batch_size=8,
    num_train_epochs=3,
    save_total_limit=2,
    predict_with_generate=True,
    logging_dir="./logs",
    report_to="none",
    push_to_hub=True,  # Optional: enable push to hub
    hub_model_id="UnluckyOrangutan/byt5-tactic-haveDraft",  # Change to your HF username/repo
    hub_strategy="every_save",
)

# ========== Step 7: Trainer ==========

trainer = Seq2SeqTrainer(
    model=model,
    args=training_args,
    train_dataset=train_ds,
    eval_dataset=eval_ds,
    tokenizer=tokenizer,
)

# ========== Step 8: Train ==========

trainer.train()

# ========== Step 9: Save model/tokenizer ==========

trainer.save_model("./byt5-tactic-haveDraft")
tokenizer.save_pretrained("./byt5-tactic-haveDraft")
trainer.push_to_hub()

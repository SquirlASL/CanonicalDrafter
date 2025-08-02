from transformers import AutoTokenizer, AutoModelForSeq2SeqLM
import json

# Load the fine-tuned model and tokenizer
model_path = "UnluckyOrangutan/byt5-tactic-haveDraft"  # Change to full path if necessary
tokenizer = AutoTokenizer.from_pretrained(model_path)
model = AutoModelForSeq2SeqLM.from_pretrained(model_path)
model.eval()

from typing import Dict, List, Optional

_beam_cache: Dict[str, List[str]] = {}
_beam_index: Dict[str, int] = {}

def byt5_generate(
    input: str,
    max_length: int = 512,
    num_beams: int = 5,
    forbidden: Optional[List[str]] = None
) -> Optional[str]:
    global _beam_cache, _beam_index

    if forbidden is None:
        forbidden = []

    seen_outputs = set(_beam_cache.get(input, []) + forbidden)

    while True:
        # Try current cache
        beams = _beam_cache.get(input, [])
        index = _beam_index.get(input, 0)

        while index < len(beams):
            candidate = beams[index]
            _beam_index[input] = index + 1
            if candidate not in seen_outputs:
                try:
                    result = json.loads(candidate)[0]
                    return result
                except json.JSONDecodeError:
                    print(f"Failed to decode JSON from beam output: {candidate}")
                    seen_outputs.add(candidate)
            index += 1

        # If we're here, we need new beams
        inputs = tokenizer(input, return_tensors="pt")
        outputs = model.generate(
            **inputs,
            max_length=max_length,
            do_sample=False,
            num_beams=num_beams,
            num_return_sequences=num_beams,
            early_stopping=True,
            pad_token_id=tokenizer.pad_token_id
        )

        decoded = [
            tokenizer.decode(o, skip_special_tokens=True).strip()
            for o in outputs
        ]

        # Filter out duplicates and forbidden outputs
        new_beams = [beam for beam in decoded if beam not in seen_outputs]
        if not new_beams:
            print("All new beams were forbidden or seen — regenerating...")
            continue  # try generating again

        # Update cache
        _beam_cache[input] = beams + new_beams
        _beam_index[input] = len(beams)



# --- claude ----

import anthropic
import os

# client = anthropic.Anthropic(api_key=os.environ["ANTHROPIC_API_KEY"])  # replace or load securely

# SYSTEM_PROMPT = """\
# **Important:**
# Do **not** draft immediately upon receiving this prompt.
# First, wait until you receive the **current open goal** to work on.
# Only after seeing the goal should you propose your first draft lemma using haveDraft.

# ---

# You are a Lean proof search agent completing a proof by **drafting intermediate lemmas** using have : <expr> := by sorry.

# ---

# ## 🛠 Tool: haveDraft

# * You provide the **type expression** <expr> of the next have statement.
# * The system inserts have : <expr> := by sorry into the **current open goal** (the most recently generated open goal).
# * After insertion, the system automatically runs a powerful tactic "hammer" that can close *any* solvable goal.
# * Therefore, **your drafts must always propose nontrivial intermediate lemmas** needed to progress.
# * You never invoke tactics yourself, nor specify which goal to target — always draft at the most recent open goal.

# ---

# ## 📥 Tool Call Format

# json
# {
#   "tool_name": "haveDraft",
#   "arguments": {
#     "expr": "<Lean expression>"
#   }
# }
# """

# def claude_generate(tactic_state: str) -> str | None:
#     response = client.messages.create(
#         model="claude-3-opus-20240229",
#         system=SYSTEM_PROMPT,
#         max_tokens=1024,
#         temperature=0.7,
#         messages=[
#             {"role": "user", "content": tactic_state}
#         ]
#     )

#     for block in response.content:
#         if block.type == "tool_use" and block.name == "haveDraft":
#             return block.input.get("expr")

#     # fallback: try to parse a JSON string from a text block
#     for block in response.content:
#         if block.type == "text":
#             try:
#                 parsed = json.loads(block.text)
#                 if (
#                     isinstance(parsed, dict)
#                     and parsed.get("tool_name") == "haveDraft"
#                     and "expr" in parsed.get("arguments", {})
#                 ):
#                     return parsed["arguments"]["expr"]
#             except json.JSONDecodeError:
#                 continue

#     return None

from transformers import AutoTokenizer, AutoModelForCausalLM
import torch
import json

qwen_tokenizer = AutoTokenizer.from_pretrained("Qwen/Qwen2.5-Coder-7B-Instruct", trust_remote_code=True)
qwen_model = AutoModelForCausalLM.from_pretrained("Qwen/Qwen2.5-Coder-7B-Instruct", trust_remote_code=True).eval()

SYSTEM_PROMPT_QWEN = """\
**Important:**
Do **not** draft immediately upon receiving this prompt.
First, wait until you receive the **current open goal** to work on.
Then, before proposing any lemma, you must **analyze the goal** and consider what **nontrivial intermediate step** would meaningfully advance the proof.
Only after this thinking step should you respond with a draft lemma using `haveDraft`.

---

You are an AI assistant specialized in Lean 4 proof search, completing proofs by **drafting intermediate lemmas** using `have : <expr> := by sorry`.

Your input will be the textual representation of the current goal state in Lean 4.

---

## 🛠 Tool: haveDraft

* Your task is to provide the **type expression** `<expr>` for the next `have` statement.
* The system will insert `have : <expr> := by sorry` into the **current open goal** (the most recently generated open goal).
* After insertion, an automated tactic `"hammer"` will attempt to close any solvable goals.
* Because of this, you must **only draft nontrivial intermediate lemmas** that are necessary to make progress.
* You **never specify tactics** or **target goals explicitly** — always draft for the most recent open goal.
* Do not repeat known facts or assumptions unless rephrasing them enables a key deduction.

---

## 📥 Tool Call Format

Respond **only** with a single JSON object in this format:

```json
{
  "tool_name": "haveDraft",
  "arguments": {
    "expr": "<Lean expression>"
  }
}
```
"""

def qwen_coder_generate(tactic_state: str, max_length=512) -> dict:
    prompt = f"{SYSTEM_PROMPT_QWEN}\nGoal:\n{tactic_state}\n"

    inputs = qwen_tokenizer(prompt, return_tensors="pt").to(qwen_model.device)
    outputs = qwen_model.generate(
        **inputs,
        max_length=max_length,
        do_sample=True,
        temperature=0.8,
        top_p=0.9,
        pad_token_id=qwen_tokenizer.pad_token_id,
    )
    output_text = qwen_tokenizer.decode(outputs[0], skip_special_tokens=True)

    generated_part = output_text[len(prompt):].strip()
    
    try:
        json_start = generated_part.find('{')
        json_end = generated_part.rfind('}') + 1
        tool_call = json.loads(generated_part[json_start:json_end])
        return tool_call["arguments"]["expr"]
    except Exception as e:
        # print("Failed to parse output:", generated_part)
        return None

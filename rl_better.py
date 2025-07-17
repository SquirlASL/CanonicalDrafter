import json
import subprocess
import os
import sys
from typing import List, Any

def split_proof_header(proof: str) -> tuple[str, str]:
    """
    From https://github.com/project-numina/kimina-lean-server/blob/069576742afb4ca6c086898787a0e91abf91893c/utils/proof_utils.py#L6
    Splits `proof` into:
    - header: the consecutive `import ...` lines at the beginning of the proof,
              with "import Mathlib." lines removed and "import Mathlib" added if necessary.
    - context: rest of the proof

    Args:
        proof (str): The proof code to split

    Returns:
        tuple[str, str]: The modified header and context of the proof
    """
    proof = proof.strip()
    lines = proof.splitlines()
    header_lines = []
    body_start_index = 0
    mathlib_imported = False

    for i, line in enumerate(lines):
        if line.startswith("import"):
            if line.startswith("import Mathlib."):
                mathlib_imported = True
            else:
                header_lines.append(line)
            body_start_index = i + 1
        else:
            break

    # Add "import Mathlib" at the beginning if any "import Mathlib." was found
    if mathlib_imported:
        header_lines.insert(0, "import Mathlib")

    header = "\n".join(header_lines).strip()
    body = "\n".join(lines[body_start_index:]).strip()

    return header, body

process = subprocess.Popen(
    ["lake", "env", "repl/.lake/build/bin/repl"],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    text=True,
    bufsize=1,
    env=os.environ,
)

from transformers import AutoTokenizer, AutoModelForSeq2SeqLM
import torch

# Load the fine-tuned model and tokenizer
model_path = "UnluckyOrangutan/byt5-lean-goals"  # Change to full path if necessary
tokenizer = AutoTokenizer.from_pretrained(model_path)
model = AutoModelForSeq2SeqLM.from_pretrained(model_path)
model.eval()

def generate_valid_tactic(tactic_state: str, proof_state: Any, max_attempts=5) -> str:
    for attempt in range(max_attempts):
        inputs = tokenizer(tactic_state, return_tensors="pt")
        outputs = model.generate(
            **inputs,
            max_length=256,
            do_sample=True,
            top_p=0.9,
            temperature=1,
            pad_token_id=tokenizer.pad_token_id
        )
        suggestion = tokenizer.decode(outputs[0], skip_special_tokens=True).strip()
        print(f"[Attempt {attempt + 1}] Suggestion: {suggestion!r}")

        if not suggestion.startswith(("have", "let", "suffices")):
            continue

        response = send_command({"tactic": suggestion, "proofState": proof_state})
        print(response)
        if "error" not in response and "message" not in response:
            return suggestion
    return None

def send_command(command):
    json_command = json.dumps(command, ensure_ascii=False) + "\n\n"
    process.stdin.write(json_command)
    process.stdin.flush()

    response_lines = []
    while True:
        stdout_line = process.stdout.readline()
        if stdout_line.strip() == "":
            break
        response_lines.append(stdout_line)

    return json.loads("".join(response_lines))

lol = send_command({ "cmd" : "import Canonical\nimport Mathlib\n" })
print(lol)
env_import = lol["env"]
print(env_import)
def run_canonicaldraft(statement):
    header, stmt_body = split_proof_header(statement)
    print(stmt_body)
    root = send_command({"cmd" : stmt_body, "env": env_import})
    print(root)
    sorry_states : List[Any] = [root["sorries"][0]]
    while sorry_states:
        sorry_state = sorry_states.pop()
        res = send_command({"tactic" : "canonical", "proofState": sorry_state["proofState"]})
        if "error" in res or "message" in res:
            temp = send_command({"tactic" : generate_valid_tactic(sorry_state["goal"], sorry_state["proofState"]), "proofState": sorry_state["proofState"]})["sorries"][0]
            sorry_states.append(temp)

if __name__ == "__main__":
    run_canonicaldraft("import Mathlib\ntheorem womp (a b c d e f g h : Nat) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := sorry")
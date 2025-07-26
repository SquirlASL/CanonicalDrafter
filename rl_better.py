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
model_path = "UnluckyOrangutan/byt5-tactic-haveDraft"  # Change to full path if necessary
tokenizer = AutoTokenizer.from_pretrained(model_path)
model = AutoModelForSeq2SeqLM.from_pretrained(model_path)
model.eval()

def generate_valid_tactic(tactic_state: str, proof_state: Any, max_attempts=5) -> str:
    for attempt in range(max_attempts):
        inputs = tokenizer(tactic_state, return_tensors="pt")
        outputs = model.generate(
            **inputs,
            max_length=512,
            do_sample=True,
            top_p=0.9,
            temperature=1,
            pad_token_id=tokenizer.pad_token_id
        )
        suggestion = tokenizer.decode(outputs[0], skip_special_tokens=True).strip()
        print(f"[Attempt {attempt + 1}] Suggestion: {suggestion!r}")

        try:
            draft = json.loads(suggestion)[0]
        except:
            return None

        response = send_command({"tactic": f"have : {draft} := by sorry", "proofState": proof_state})
        
        if "error" not in response and "message" not in response:
            return draft, response
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
def run_canonicaldraft(statement, max_depth=20, max_iterations=40):
    header, stmt_body = split_proof_header(statement)
    print(stmt_body)
    root = send_command({"cmd" : stmt_body, "env": env_import})
    print(root)
    proof_states : List[Any] = [root["sorries"][0]]
    iteration = 0
    while proof_states:
        print(proof_states)
        if iteration >= max_iterations:
            return False
        if len(proof_states) >= max_depth:
            proof_states.pop()
            continue
        proof_state = proof_states[-1]
        res = send_command({"tactic" : "canonical", "proofState": proof_state["proofState"]})
        if "error" in res or "message" in res:
            gen = generate_valid_tactic(proof_state["goal"], proof_state["proofState"])
            if gen != None:
                temp = gen[1]["sorries"][0]
                temp["new_parent_proofState"] = gen[1]["proofState"]
                temp["new_parent_goal"] = gen[1]["goals"][0]
                proof_states.append(temp)
        else:
            proof_states.pop()
            if len(proof_states) >= 1:
                parent_state = proof_states[-1]
                # change parent proofstate to include drafted have statement
                parent_state["proofState"] = proof_state["new_parent_proofState"]
                parent_state["goal"] = proof_state["new_parent_goal"]
        iteration += 1
    return True      

if __name__ == "__main__":
    q = run_canonicaldraft("import Mathlib\ntheorem womp (a b c d e f g h : Nat) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := sorry")
    print(q)
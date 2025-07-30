import json
import subprocess
import os
import sys
from typing import List, Any

from generators import byt5_generate, qwen_coder_generate

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
    cwd="CanonicalDrafter",
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    text=True,
    bufsize=1,
    env=os.environ,
)

def generate_valid_tactic(tactic_state: str, proof_state: Any, max_attempts=5, generate: callable = qwen_coder_generate) -> str:
    for attempt in range(max_attempts):
        suggestion = generate(tactic_state)
        print(f"[Attempt {attempt + 1}] Suggestion: {suggestion!r}")

        if not suggestion:
            print("Model failed to propose a valid expr.")
            continue

        response = send_command({"tactic": f"have : {suggestion} := by sorry", "proofState": proof_state})
        
        if "error" not in response and "message" not in response:
            return suggestion, response
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

def close_goal(proof_state, tactics):
    # special logic for canonical
    res = send_command({"tactic" : "canonical", "proofState": proof_state["proofState"]})
    print("canonical", res)
    if not "message" in res:
        return True
    
    for tactic in tactics:
        res = send_command({"tactic" : tactic, "proofState": proof_state["proofState"]})
        print(tactic, res)
        if not ("error" in res or "message" in res and res["message"] != "no goals" or "proofStatus" in res and res["proofStatus"] != "Completed"):
            return True

lol = send_command({ "cmd" : "import Canonical\nimport Mathlib\n" })
print(lol)
env_import = lol["env"]
print(env_import)
def run_canonicaldraft(statement, max_depth=2, max_iterations=40, tactics=["ring", "linarith"]):
    header, stmt_body = split_proof_header(statement)
    print(stmt_body)
    root = send_command({"cmd" : stmt_body, "env": env_import})
    print(root)
    proof_states : List[Any] = [root["sorries"][0]]
    iteration = 0
    while proof_states:
        # print(proof_states)
        if iteration >= max_iterations:
            return False
        if len(proof_states) > max_depth:
            proof_states.pop()
            continue
        proof_state = proof_states[-1]
        print("------")
        print(proof_state["goal"])
        if not close_goal(proof_state, tactics):
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
    proofs = ["import Mathlib\ntheorem womp (a b c d e f g h : Nat) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := sorry", "import Mathlib\ntheorem q.le_mul_right (a b : Nat) (h : a * b ≠ 0) : a ≤ (a * b) := sorry"]
    for proof in proofs:
        print(run_canonicaldraft(proof))
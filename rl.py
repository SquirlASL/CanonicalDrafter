import json
import subprocess
import os
import sys

process = subprocess.Popen(
    ["lake", "exe", "repl"],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    text=True,
    bufsize=1,
    env=os.environ,
)

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

# Example usage
print(send_command({ "cmd" : "import Mathlib" }))
print(send_command({ "cmd" : "theorem womp : 2 + 2 = 4 := by sorry", "env": 0 }))
print(send_command({ "tactic": "have : 2 + 1 = 3 := by sorry", "proofState": 0 }))
print(send_command({ "tactic": "have : 1 + 1 = 2 := by rfl", "proofState": 1 }))

import json
import subprocess
import os
import sys

process = subprocess.Popen(
    ["lake", "env", "repl/.lake/build/bin/repl"],
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

print(send_command({ "cmd" : "import Mathlib\ntheorem womp (a b c d e f g h : Nat) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := sorry" }))
print(send_command({ "tactic": "have : a + b + c + d + e + f + g + h = a + b + c + d + e + f + g + h := sorry", "proofState": 0 }))
print(send_command({ "tactic": "sorry", "proofState": 1 }))

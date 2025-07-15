import json
import subprocess
import os
import sys
from typing import List, Any

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

lol = send_command({ "cmd" : "import Canonical\n\ntheorem womp : (2:Nat) + 2 = 4 := by canonical" })
print(lol)
env_import = lol["env"]
print(env_import)
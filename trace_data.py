import json
import os
from datasets import Dataset
from concurrent.futures import ThreadPoolExecutor, as_completed
from threading import Lock
import shutil
import subprocess

root = "/home/frederick/mathlib4"
initial_path = f"{root}/Mathlib.lean"

seen = set()
seen_lock = Lock()
all_have_pairs = []
all_have_pairs_lock = Lock()

count = 0
submitted = 0

def process(path):
    rel_path = path[len(root):-len(".lean")]
    prefix = f".lake/build/ir/{rel_path}"

    local_pairs = []
    new_paths = []

    try:
        with open(root + "/" + prefix + ".ast.json", "r") as f:
            data = json.load(f)
            local_pairs = data.get("haveDrafts", [])
    except FileNotFoundError:
        pass

    try:
        with open(root + "/" + prefix + ".dep_paths", "r") as f:
            content = f.read()
            if content:
                new_paths = content.split("\n")
    except FileNotFoundError:
        pass

    return path, local_pairs, new_paths

# shutil.copy2('CanonicalDrafter/ExtractData.lean', root)

# # result = subprocess.run(
# #     ["lake", "env", "lean", "--run", "ExtractData.lean"], 
# #     capture_output=True, 
# #     text=True,
# #     cwd=root
# # )
# # print(result.stdout)

with ThreadPoolExecutor(max_workers=os.cpu_count() * 2) as executor:
    futures = {}
    # Submit initial path
    future = executor.submit(process, initial_path)
    futures[future] = initial_path
    with seen_lock:
        seen.add(initial_path)
    submitted = 1

    while futures:
        for future in as_completed(futures):
            path, have_pairs, new_paths = future.result()
            count += 1
            print(f"Processed: {path}, pairs: {len(have_pairs)}, new deps: {len(new_paths)}")

            with all_have_pairs_lock:
                all_have_pairs.extend(have_pairs)

            # Submit new dependencies
            for new_path in new_paths:
                with seen_lock:
                    if new_path not in seen:
                        seen.add(new_path)
                        new_future = executor.submit(process, new_path)
                        futures[new_future] = new_path
                        submitted += 1

            del futures[future]
            break  # important: re-enter as_completed() after adding futures

print(f"Total files processed: {count}")
print(f"Total havePairs collected: {len(all_have_pairs)}")

if all_have_pairs:
    Dataset.from_list(all_have_pairs).save_to_disk("./haveDrafts_dataset2")
    print("Dataset saved to ./haveDrafts_dataset2")
else:
    print("No havePairs found. Dataset not saved.")

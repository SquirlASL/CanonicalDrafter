import json

def extract_goals_to_json(input_file, output_file):
    """
    Reads a JSON file and writes a new JSON file containing a list of 'goal' strings.
    """
    with open(input_file, "r", encoding="utf-8") as f:
        data = json.load(f)

    out = {}

    for item in data:
        draft = item.get("haveDraft")
        goal = item.get("goal")
        out[goal] = draft

    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, ensure_ascii=False)

    print(f"Extracted {len(out)} goals and wrote to {output_file}")

# Example usage:
if __name__ == "__main__":
    extract_goals_to_json("Test/names.ast.json", "data.json")
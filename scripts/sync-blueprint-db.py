#!/usr/bin/env python3
import json
import os
import re

DB_FILE = "sorries.jsonl"
SCHEMA_KEYS = ["@ver", "i", "f", "k", "s", "n", "o", "r", "e", "u", "d", "a", "c", "b", "t"]

def load_db():
    items = []
    header = None
    if os.path.exists(DB_FILE):
        with open(DB_FILE, "r") as f:
            for line in f:
                if not line.strip(): continue
                obj = json.loads(line)
                if obj.get("i") == "ID":
                    header = obj
                    continue
                items.append(obj)
    return header, items

def crawl_tex():
    labels = {} # label -> {file, kind, uses, lean_names}
    env_pattern = re.compile(r'\\begin\{(?P<env>lemma|theorem|definition|proposition|corollary|remark|classicalinput)\}(?P<content>.*?)\\end\{(?P=env)\}', re.DOTALL)
    
    for root, _, files in os.walk("tex"):
        for file in files:
            if file.endswith(".tex"):
                path = os.path.join(root, file)
                with open(path, encoding='utf-8') as f:
                    text = f.read()
                
                for match in env_pattern.finditer(text):
                    content = match.group('content')
                    kind = match.group('env')
                    lm = re.search(r'\\label\{([^}]+)\}', content)
                    if not lm: continue
                    label = lm.group(1)
                    um = re.search(r'\\uses\{([^}]+)\}', content)
                    uses = [u.strip() for u in um.group(1).split(',')] if um else []
                    ln = re.search(r'\\lean\{([^}]+)\}', content)
                    lean_names = [n.strip() for n in ln.group(1).split(',')] if ln else []
                    labels[label] = {"f": path, "k": kind, "u_labels": uses, "lean": lean_names}
    return labels

def main():
    header, old_items = load_db()
    tex_labels = crawl_tex()
    
    # 1. Map labels to existing IDs
    label_to_existing_ids = {}
    for obj in old_items:
        if obj.get("b"):
            if obj["b"] not in label_to_existing_ids: label_to_existing_ids[obj["b"]] = []
            label_to_existing_ids[obj["b"]].append(obj["i"])
            
    # Ensure challenge-api is ID 0
    CHALLENGE_API = "thm:challenge-api"
    if CHALLENGE_API not in label_to_existing_ids:
        label_to_existing_ids[CHALLENGE_API] = [0]
    else:
        # If it was already there with a different ID, we might have a conflict.
        # For now, just ensure 0 is in the list.
        if 0 not in label_to_existing_ids[CHALLENGE_API]:
            label_to_existing_ids[CHALLENGE_API].append(0)
            
    # 2. Assign IDs to new TeX labels
    max_id = 124
    for obj in old_items:
        if isinstance(obj.get("i"), int):
            max_id = max(max_id, obj["i"])
            
    next_id = max_id + 1
    for label in sorted(tex_labels.keys()):
        if label not in label_to_existing_ids:
            label_to_existing_ids[label] = [next_id]
            next_id += 1
            
    # 3. Construct the new database
    new_db = []
    processed_ids = set()
    
    # Step A: Start with all old items, updating their TeX-derived metadata
    for obj in old_items:
        label = obj.get("b")
        if label and label in tex_labels:
            info = tex_labels[label]
            # Use TeX path for the record (or keep Lean path if it is code-rich?)
            # Actually, f is currently the TeX path in my previous runs for non-sorries.
            # For sorries, we prefer the Lean path.
            # If obj["n"] > 0, keep obj["f"].
            if obj.get("n", 0) == 0:
                obj["f"] = info["f"]
            obj["k"] = info["k"]
        new_db.append(obj)
        processed_ids.add(obj["i"])
        
    # Step B: Add new TeX labels that weren't in the DB
    for label, info in tex_labels.items():
        for jid in label_to_existing_ids[label]:
            if jid not in processed_ids:
                obj = {
                    "@ver": None,
                    "i": jid,
                    "f": info["f"],
                    "k": info["k"],
                    "s": label,
                    "n": 0,
                    "o": 1,
                    "r": 0,
                    "e": None,
                    "u": [],
                    "d": [],
                    "a": "",
                    "c": "done",
                    "b": label,
                    "t": ""
                }
                new_db.append(obj)
                processed_ids.add(jid)

    # 4. Re-link the graph
    id_to_obj = {obj["i"]: obj for obj in new_db}
    label_to_ids = label_to_existing_ids # already covers all
    
    # Clear existing links
    for obj in new_db:
        obj["u"] = []
        obj["d"] = []
        
    for obj in new_db:
        label = obj.get("b")
        if not label or label not in tex_labels: continue
        
        for u_label in tex_labels[label]["u_labels"]:
            if u_label in label_to_ids:
                for uid in label_to_ids[u_label]:
                    obj["u"].append(uid)
                    if uid in id_to_obj:
                        id_to_obj[uid]["d"].append(obj["i"])

    # Unique and sort
    for obj in new_db:
        obj["u"] = sorted(list(set(obj["u"])))
        obj["d"] = sorted(list(set(obj["d"])))

    # 5. Reachability from ID 0
    reachable = {0}
    stack = [0]
    while stack:
        curr = stack.pop()
        curr_obj = id_to_obj.get(curr)
        if not curr_obj: continue
        for uid in curr_obj.get("u", []):
            if uid not in reachable:
                reachable.add(uid)
                stack.append(uid)
    for obj in new_db:
        obj["r"] = 1 if obj["i"] in reachable else 0

    # 6. Write back
    with open(DB_FILE, "w") as f:
        if header:
            f.write(json.dumps(header, separators=(",", ":")) + "\n")
        for obj in sorted(new_db, key=lambda x: x["i"]):
            row = {k: obj.get(k) for k in SCHEMA_KEYS}
            f.write(json.dumps(row, separators=(",", ":")) + "\n")

    print(f"Database synchronized: {len(new_db)} nodes total.")
    print(f"Reachable from challenge-api: {len(reachable)}")

if __name__ == "__main__":
    main()

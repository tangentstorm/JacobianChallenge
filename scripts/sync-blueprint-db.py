#!/usr/bin/env python3
import json
import os
import re
import subprocess

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

def get_current_sorries():
    res = subprocess.run(["python3", "scripts/list-sorries.py"], capture_output=True, text=True)
    sorries = {} # name -> {f, n, o, r}
    for line in res.stdout.splitlines():
        if line.startswith("{"):
            try:
                obj = json.loads(line)
                sorries[obj["s"]] = obj
            except: pass
    return sorries

def main():
    header, old_items = load_db()
    tex_labels = crawl_tex()
    live_sorries = get_current_sorries()
    
    # 1. Map labels and statement names to existing IDs
    label_to_existing_ids = {}
    name_to_existing_ids = {}
    for obj in old_items:
        jid = obj["i"]
        label = obj.get("b")
        name = obj.get("s")
        
        if label:
            if label not in label_to_existing_ids: label_to_existing_ids[label] = []
            label_to_existing_ids[label].append(jid)
        
        if name:
            if name not in name_to_existing_ids: name_to_existing_ids[name] = []
            name_to_existing_ids[name].append(jid)
            
    # Ensure challenge-api is ID 0
    CHALLENGE_API = "thm:challenge-api"
    if CHALLENGE_API not in label_to_existing_ids:
        label_to_existing_ids[CHALLENGE_API] = [0]
    else:
        if 0 not in label_to_existing_ids[CHALLENGE_API]:
            label_to_existing_ids[CHALLENGE_API].append(0)
            
    # 2. Assign IDs to new TeX labels
    # Find current max ID to ensure new ones are truly new
    max_id = 0
    for obj in old_items:
        if isinstance(obj.get("i"), int):
            max_id = max(max_id, obj["i"])
            
    next_id = max_id + 1
    for label in sorted(tex_labels.keys()):
        if label in label_to_existing_ids:
            continue
            
        # Fallback: check if any Lean names for this label already have IDs
        found_id = None
        for ln in tex_labels[label]["lean"]:
            if ln in name_to_existing_ids:
                # Use the first existing ID found for this Lean name
                found_id = name_to_existing_ids[ln][0]
                break
        
        if found_id is not None:
            label_to_existing_ids[label] = [found_id]
        else:
            label_to_existing_ids[label] = [next_id]
            next_id += 1
            
    # 3. Construct the new database
    new_db = []
    processed_ids = set()
    
    # Map from ID to old item
    id_to_old = {obj["i"]: obj for obj in old_items}
    
    # Process TeX labels
    for label, info in tex_labels.items():
        for jid in label_to_existing_ids[label]:
            old_obj = id_to_old.get(jid, {})
            
            # Determine status and sorry count from live code
            is_sorry = False
            num_sorries = 0
            obligations = 1
            lean_file = old_obj.get("f") or info["f"]
            statement_name = old_obj.get("s") or (info["lean"][0] if info["lean"] else label)
            
            has_lean = False
            for ln in info["lean"]:
                has_lean = True
                if ln in live_sorries:
                    is_sorry = True
                    num_sorries = live_sorries[ln]["n"]
                    obligations = live_sorries[ln]["o"]
                    lean_file = live_sorries[ln]["f"]
                    statement_name = ln
                    break
            
            if has_lean:
                status = "open" if is_sorry else "done"
            else:
                status = old_obj.get("c") or "open"
                
            obj = {
                "@ver": None,
                "i": jid,
                "f": lean_file,
                "k": info["k"],
                "s": statement_name,
                "n": num_sorries,
                "o": obligations,
                "r": 0,
                "e": old_obj.get("e"),
                "u": [],
                "d": [],
                "a": old_obj.get("a") or "",
                "c": status,
                "b": label,
                "t": old_obj.get("t") or ""
            }
            new_db.append(obj)
            processed_ids.add(jid)
            
    # Add items from old DB that were not in TeX
    for jid, old_obj in id_to_old.items():
        if jid not in processed_ids:
            new_db.append(old_obj)

    # 4. Re-link the graph
    id_to_obj = {obj["i"]: obj for obj in new_db}
    
    # Clear existing links
    for obj in new_db:
        obj["u"] = []
        obj["d"] = []
        
    for obj in new_db:
        label = obj.get("b")
        if not label or label not in tex_labels: continue
        
        for u_label in tex_labels[label]["u_labels"]:
            if u_label in label_to_existing_ids:
                for uid in label_to_existing_ids[u_label]:
                    if uid in id_to_obj:
                        obj["u"].append(uid)
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

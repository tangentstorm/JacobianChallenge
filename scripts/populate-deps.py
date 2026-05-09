#!/usr/bin/env python3
import re
import os
import json

# 1. Parse TeX files for \label and \uses
label_uses = {}

for root, _, files in os.walk("tex"):
    for file in files:
        if file.endswith(".tex"):
            with open(os.path.join(root, file)) as f:
                content = f.read()
                envs = re.findall(r"\\begin\{[^}]+\}(.*?)\\end\{[^}]+\}", content, re.DOTALL)
                for env in envs:
                    labels = re.findall(r"\\label\{([^}]+)\}", env)
                    if not labels: continue
                    label = labels[0]
                    
                    uses_lists = re.findall(r"\\uses\{([^}]+)\}", env)
                    used_labels = []
                    for u_str in uses_lists:
                        for u in u_str.split(","):
                            u = u.strip()
                            if u: used_labels.append(u)
                    
                    if used_labels:
                        label_uses[label] = list(set(used_labels))

print(f"Found dependencies for {len(label_uses)} blueprint labels.")

# 2. Load sorries database and map labels to IDs
db_items = []
header = None
label_to_ids = {}

with open("sorries.jsonl", "r") as f:
    for i, line in enumerate(f):
        if not line.strip(): continue
        obj = json.loads(line)
        if i == 0 and obj.get("i") == "ID":
            header = obj
            continue
        
        db_items.append(obj)
        b = obj.get("b")
        if b:
            if b not in label_to_ids:
                label_to_ids[b] = []
            label_to_ids[b].append(obj["i"])

# 3. Calculate 'u' (upstream) and build 'd' (downstream) inverses
id_to_u = {obj["i"]: set() for obj in db_items}
id_to_d = {obj["i"]: set() for obj in db_items}

for obj in db_items:
    b = obj.get("b")
    if not b or b not in label_uses: continue
    
    # What labels does this blueprint item use?
    upstream_labels = label_uses[b]
    for u_label in upstream_labels:
        if u_label in label_to_ids:
            upstream_ids = label_to_ids[u_label]
            for uid in upstream_ids:
                if uid != obj["i"]: # no self edges
                    id_to_u[obj["i"]].add(uid)
                    id_to_d[uid].add(obj["i"])

# 4. Update objects
updates = 0
for obj in db_items:
    i = obj["i"]
    new_u = sorted(list(id_to_u[i]))
    new_d = sorted(list(id_to_d[i]))
    
    if obj.get("u") != new_u or obj.get("d") != new_d:
        obj["u"] = new_u
        obj["d"] = new_d
        updates += 1

# 5. Write back maintaining exact schema order
SCHEMA_KEYS = ["@ver", "i", "f", "k", "s", "n", "o", "r", "e", "u", "d", "a", "c", "b", "t"]

with open("sorries.jsonl", "w") as f:
    f.write(json.dumps(header, separators=(',', ':')) + "\n")
    for obj in db_items:
        row = {}
        for k in SCHEMA_KEYS:
            if k in obj: row[k] = obj[k]
        for k in obj:
            if k not in row: row[k] = obj[k]
        f.write(json.dumps(row, separators=(',', ':')) + "\n")

print(f"Updated upstream/downstream edges for {updates} tracking records.")

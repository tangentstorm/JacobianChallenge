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

# 2. Load sorries database and map labels to IDs
db_items = []
header = None
label_to_ids = {}
for line in open("sorries.jsonl"):
    obj = json.loads(line)
    if obj.get("i") == "ID":
        header = obj
        continue
    db_items.append(obj)
    b = obj.get("b")
    if b:
        if b not in label_to_ids: label_to_ids[b] = []
        label_to_ids[b].append(obj["i"])

# 3. Calculate dependencies
# REFINEMENT FLOW: Goal (u:[]) -> Implementation (d:[])
# u = parent (higher level), d = child (lower level)
id_to_u = {obj["i"]: set() for obj in db_items}
id_to_d = {obj["i"]: set() for obj in db_items}

for obj in db_items:
    b = obj.get("b")
    if not b or b not in label_uses: continue
    
    # TeX "\uses{X}" means "this node refines into X"
    # So X is DOWNSTREAM (d) of this node.
    for leaf_label in label_uses[b]:
        if leaf_label in label_to_ids:
            for lid in label_to_ids[leaf_label]:
                if lid != obj["i"]:
                    id_to_d[obj["i"]].add(lid)
                    id_to_u[lid].add(obj["i"])

# 4. Update and write back
SCHEMA_KEYS = ["@ver", "i", "f", "k", "s", "n", "o", "r", "e", "u", "d", "a", "c", "b", "t"]
with open("sorries.jsonl", "w") as f:
    f.write(json.dumps(header, separators=(",", ":")) + "\n")
    for obj in db_items:
        i = obj["i"]
        obj["u"] = sorted(list(set(obj.get("u", [])) | id_to_u[i]))
        obj["d"] = sorted(list(set(obj.get("d", [])) | id_to_d[i]))
        row = {k: obj.get(k) for k in SCHEMA_KEYS}
        f.write(json.dumps(row, separators=(",", ":")) + "\n")

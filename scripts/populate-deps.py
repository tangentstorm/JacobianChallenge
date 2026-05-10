#!/usr/bin/env python3
import re
import os
import json

# 1. Parse TeX files for \label, \uses, and \lean
label_uses = {}
lean_to_label = {}
all_labels = set()

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
                    all_labels.add(label)
                    
                    leans = re.findall(r"\\lean\{([^}]+)\}", env)
                    for l_str in leans:
                        for l_name in l_str.split(","):
                            l_name = l_name.strip()
                            if l_name:
                                short_name = l_name.split(".")[-1]
                                lean_to_label[short_name] = label

                    uses_lists = re.findall(r"\\uses\{([^}]+)\}", env)
                    used_labels = []
                    for u_str in uses_lists:
                        for u in u_str.split(","):
                            u = u.strip()
                            if u: used_labels.append(u)
                    if used_labels:
                        label_uses[label] = list(set(used_labels))

print(f"Parsed Blueprint: {len(all_labels)} nodes, {len(label_uses)} edges.")

# 2. Build Transitive Closure of dependencies in Blueprint
# Goal: For any label X, what is the set of all labels Y such that X is downstream of Y?
# We want to find the first *sorry* node downstream of X.
downstream_closure = {l: set() for l in all_labels}
for consumer, sources in label_uses.items():
    for src in sources:
        if src in all_labels:
            downstream_closure[src].add(consumer)

# Transitive closure
changed = True
while changed:
    changed = False
    for node in all_labels:
        current_ds = downstream_closure[node]
        new_ds = current_ds.copy()
        for ds in current_ds:
            new_ds.update(downstream_closure[ds])
        if len(new_ds) > len(current_ds):
            downstream_closure[node] = new_ds
            changed = True

# 3. Load sorries database
db_items = []
header = None
with open("sorries.jsonl", "r") as f:
    for i, line in enumerate(f):
        if not line.strip(): continue
        obj = json.loads(line)
        if i == 0 and obj.get("i") == "ID":
            header = obj
            continue
        # Auto-update label mapping
        if obj["s"] in lean_to_label:
            obj["b"] = lean_to_label[obj["s"]]
        db_items.append(obj)

label_to_ids = {}
for obj in db_items:
    if obj.get("b"):
        if obj["b"] not in label_to_ids: label_to_ids[obj["b"]] = []
        label_to_ids[obj["b"]].append(obj["i"])

# 4. Calculate dependencies using transitive closure
# Truth Flow: Leaf -> Root
id_to_u = {obj["i"]: set() for obj in db_items}
id_to_d = {obj["i"]: set() for obj in db_items}

BLACKLIST = {"thm:challenge-api", "def:analytic-jacobian", "def:abel-jacobi", "thm:push-pull-functoriality", "thm:genus-zero-classification"}

for obj in db_items:
    b = obj.get("b")
    if not b or b in BLACKLIST: continue
    
    # Direct Upstream (from \uses)
    if b in label_uses:
        for src_label in label_uses[b]:
            if src_label in label_to_ids and src_label not in BLACKLIST:
                for sid in label_to_ids[src_label]:
                    if sid != obj["i"]:
                        id_to_u[obj["i"]].add(sid)
                        id_to_d[sid].add(obj["i"])

    # Transitive Downstream
    # For every label 'ds' that is downstream of 'b' in the blueprint:
    # if 'ds' has a sorry ID, then that ID is downstream of obj.
    for ds_label in downstream_closure.get(b, []):
        if ds_label in label_to_ids and ds_label not in BLACKLIST:
            for did in label_to_ids[ds_label]:
                if did != obj["i"]:
                    id_to_d[obj["i"]].add(did)
                    id_to_u[did].add(obj["i"])

# 5. Write back maintaining order
SCHEMA_KEYS = ["@ver", "i", "f", "k", "s", "n", "o", "r", "e", "u", "d", "a", "c", "b", "t"]
with open("sorries.jsonl", "w") as f:
    f.write(json.dumps(header, separators=(',', ':')) + "\n")
    for obj in db_items:
        i = obj["i"]
        obj["u"] = sorted(list(id_to_u[i]))
        obj["d"] = sorted(list(id_to_d[i]))
        row = {k: obj.get(k) for k in SCHEMA_KEYS}
        f.write(json.dumps(row, separators=(",", ":")) + "\n")

print(f"Database fully re-synchronized with transitive Blueprint paths.")

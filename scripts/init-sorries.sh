#!/usr/bin/env bash
set -e

DB_FILE="sorries.jsonl"

if [ -f "$DB_FILE" ]; then
  echo "WARNING: $DB_FILE already exists!"
  echo "This database contains manual tracking data (effort, assignees, notes) that took time to gather."
  echo "Running this script will completely wipe it out. You probably do not want to run this more than once ever."
  echo "If you are absolutely sure you want to reset the database, delete $DB_FILE first."
  exit 1
fi

echo "Initializing $DB_FILE..."

# Write schema header
echo '{"i":"ID","f":"File","k":"Keyword","s":"Statement","n":"Num Sorries","o":"Obligations","r":"Reachable (0|1)","e":"Effort [1..10]","u":"Upstream IDs","d":"Downstream IDs","a":"Assignee","c":"Status","b":"Blueprint Ref","t":"Type"}' > "$DB_FILE"

# Run list-sorries.py and enrich the output with jq
python3 scripts/list-sorries.py | jq -c -s '
  to_entries | map(.value + {
    i: (.key + 1),
    e: null,
    u: [],
    d: [],
    a: "",
    c: "open",
    b: "",
    t: ""
  }) | map({
    i: .i,
    f: .f,
    k: .k,
    s: .s,
    n: .n,
    o: .o,
    r: .r,
    e: .e,
    u: .u,
    d: .d,
    a: .a,
    c: .c,
    b: .b,
    t: .t
  }) | .[]
' >> "$DB_FILE"

# Count the number of records added (excluding header)
COUNT=$(($(wc -l < "$DB_FILE") - 1))
echo "Successfully created $DB_FILE with $COUNT records."

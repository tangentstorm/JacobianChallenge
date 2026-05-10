#!/bin/bash
# scripts/trace-unreachable.sh
# Finds unreachable open nodes and walks downstream (.d) to find the first reachable nodes.

# 1. Resolve the file path
if [ -n "$1" ]; then
    JSONL_FILE="$1"
elif [ -f "sorries.jsonl" ]; then
    JSONL_FILE="sorries.jsonl"
elif [ -f "$(git rev-parse --show-toplevel 2>/dev/null)/sorries.jsonl" ]; then
    JSONL_FILE="$(git rev-parse --show-toplevel)/sorries.jsonl"
else
    echo "Error: Could not find sorries.jsonl in current directory or project root."
    echo "Usage: $0 [path/to/sorries.jsonl]"
    exit 1
fi

echo "Processing: $JSONL_FILE" >&2

# 2. Execute JQ logic
jq -s '
  # Build an index of all valid nodes (skipping header)
  (map(select(.i | type == "number")) | reduce .[] as $item ({}; .[$item.i | tostring] = $item)) as $index |
  
  # Select start nodes: must be open, have obligations, and currently unreachable (r=0)
  .[] | select((.i | type == "number") and .c == "open" and .o > 0 and .r == 0) |
  
  . as $start |
  {
    id: .i,
    statement: .s,
    file: .f,
    # Recursively walk the downstream (.d) links
    first_reachable_downstream: [
      .d[] | 
      recurse(
        ($index[tostring]) as $node |
        # Continue recursion only if the current node is still unreachable
        if ($node and $node.r == 0) then $node.d[] else empty end
      ) |
      # Filter for the first reachable nodes we hit
      $index[tostring] | select(. and .r == 1) |
      {id: .i, statement: .s, file: .f}
    ] | unique_by(.id)
  } | 
  # Only show nodes that actually have a path to a reachable node
  select(.first_reachable_downstream | length > 0)
' "$JSONL_FILE"

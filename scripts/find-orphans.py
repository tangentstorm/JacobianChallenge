"""Audit the blueprint dep graph in tex/.

Reports:
  1. Sink orphans   — labels nothing uses or refs (other than the root
     `thm:challenge-api` and any deliberately-bonus theorems).
  2. Source orphans — nodes the challenge root cannot reach
     transitively through `\\uses{...}` edges (i.e. nodes that don't
     contribute to the challenge proof).
"""
import re
import glob

labels = {}                # label -> [files]
uses_edges = {}            # label -> set of labels it uses

for path in glob.glob('tex/**/*.tex', recursive=True):
    with open(path, encoding='utf-8') as f:
        text = f.read()
    # Find each labelled block + its associated \uses{...} (within ~30 lines)
    for m in re.finditer(r'\\label\{([^}]+)\}', text):
        label = m.group(1)
        labels.setdefault(label, []).append(path)
        # Look for \uses{...} in the surrounding 1500 chars
        ctx = text[max(0, m.start() - 800): m.end() + 800]
        deps = set()
        for um in re.finditer(r'\\uses\{([^}]+)\}', ctx):
            for d in um.group(1).split(','):
                deps.add(d.strip())
        uses_edges.setdefault(label, set()).update(deps)

# Collect the in-graph reverse edges
incoming = {l: set() for l in labels}
for src, dsts in uses_edges.items():
    for d in dsts:
        if d in incoming:
            incoming[d].add(src)

dep_labels = {l for l in labels if l.startswith(('def:', 'lem:', 'thm:', 'prop:', 'input:'))}

# 1. Sink orphans
sink_orphans = sorted(l for l in dep_labels if not incoming[l])
print('=== Sink orphans (no uses/ref points at them) ===')
for o in sink_orphans:
    print(f'  {o}  |  {labels[o][0]}')
print(f'  TOTAL: {len(sink_orphans)}')

# 2. Source orphans — BFS from `thm:challenge-api` BACKWARDS through uses
ROOT = 'thm:challenge-api'
reachable = set()
if ROOT in dep_labels:
    queue = [ROOT]
    reachable.add(ROOT)
    while queue:
        n = queue.pop()
        for d in uses_edges.get(n, ()):
            if d in dep_labels and d not in reachable:
                reachable.add(d)
                queue.append(d)

unreachable = sorted(dep_labels - reachable)
print()
print(f'=== Source orphans (cannot be reached from {ROOT} via uses) ===')
for o in unreachable:
    print(f'  {o}  |  {labels[o][0]}')
print(f'  TOTAL: {len(unreachable)}')
print(f'  REACHABLE: {len(reachable)} / {len(dep_labels)}')

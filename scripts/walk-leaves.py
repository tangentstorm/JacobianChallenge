"""Walk the leaves of the blueprint dep graph and report gap status.

A "leaf" here is a node with no outgoing \\uses{...} edge — the bottom
of the dep tree, where the proof either grounds out in Mathlib or
identifies a real classical-analysis hole.

For each leaf we report:
  - label
  - section file
  - blueprint flag (\\leanok / \\notready / unflagged)
  - whether the named \\lean{...} target appears in Mathlib namespace
    (`Mathlib.*` — purely heuristic) or is project-local
"""
import re, glob

nodes = {}  # label -> dict(file, uses, leanok, notready, lean_target, depends)

for path in glob.glob('tex/**/*.tex', recursive=True):
    with open(path, encoding='utf-8') as f:
        text = f.read()
    for m in re.finditer(r'\\label\{([^}]+)\}', text):
        label = m.group(1)
        ctx = text[m.end(): m.end() + 1500]
        uses_m = re.search(r'\\uses\{([^}]+)\}', ctx)
        lean_m = re.search(r'\\lean\{([^}]+)\}', ctx)
        depends_m = re.search(r'\\depends\{', ctx)
        leanok = bool(re.search(r'\\leanok\b', ctx))
        notready = bool(re.search(r'\\notready\b', ctx))
        nodes[label] = dict(
            file=path.replace('\\','/').split('tex/')[-1],
            uses=[u.strip() for u in uses_m.group(1).split(',')] if uses_m else [],
            lean=lean_m.group(1).strip() if lean_m else None,
            leanok=leanok, notready=notready,
            has_depends=bool(depends_m),
        )

dep_labels = {l for l in nodes if l.startswith(('def:', 'lem:', 'thm:', 'prop:', 'input:'))}
leaves = [l for l in dep_labels if not nodes[l]['uses']]

# Bucket
gap_inputs = []        # input:* — known classical-analysis gaps
gap_notready = []      # \notready non-input leaves
mathlib_grounded = []  # \leanok leaves that ground out
unflagged = []         # neither flag

for l in sorted(leaves):
    n = nodes[l]
    if l.startswith('input:'):
        gap_inputs.append(l)
    elif n['notready']:
        gap_notready.append(l)
    elif n['leanok']:
        mathlib_grounded.append(l)
    else:
        unflagged.append(l)

print(f'=== Total dep-graph nodes: {len(dep_labels)}')
print(f'=== Leaves (no \\uses edges): {len(leaves)}')
print()

print(f'## Mathlib-grounded leaves (\\leanok): {len(mathlib_grounded)}')
for l in mathlib_grounded:
    n = nodes[l]
    target = n['lean'] or '(no \\lean{} target)'
    print(f'  {l}')
    print(f'    target: {target}')

print()
print(f'## Classical-input umbrellas (real gaps to Mathlib): {len(gap_inputs)}')
for l in gap_inputs:
    n = nodes[l]
    target = n['lean'] or '(no \\lean{} target)'
    print(f'  {l}')
    print(f'    file:   {n["file"]}')
    print(f'    target: {target}')
    print(f'    flag:   {"\\notready" if n["notready"] else ("\\leanok" if n["leanok"] else "(none)")}')

print()
print(f'## Other \\notready leaves: {len(gap_notready)}')
for l in gap_notready:
    n = nodes[l]
    target = n['lean'] or '(no \\lean{} target)'
    print(f'  {l}')
    print(f'    file:   {n["file"]}')
    print(f'    target: {target}')

print()
print(f'## Unflagged leaves: {len(unflagged)}')
for l in unflagged:
    n = nodes[l]
    target = n['lean'] or '(no \\lean{} target)'
    print(f'  {l}: {target}')

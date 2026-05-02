"""Quick gap-state summary of the blueprint dep graph."""
import re, glob

notready, leanok, unflagged, inputs = [], [], [], []
for path in glob.glob('tex/**/*.tex', recursive=True):
    with open(path, encoding='utf-8') as f:
        text = f.read()
    for m in re.finditer(r'\\label\{([^}]+)\}', text):
        label = m.group(1)
        if not label.startswith(('def:', 'lem:', 'thm:', 'prop:', 'input:')):
            continue
        ctx = text[m.end(): m.end() + 1500]
        if re.search(r'\\notready\b', ctx):
            notready.append(label)
        elif re.search(r'\\leanok\b', ctx):
            leanok.append(label)
        else:
            unflagged.append(label)
        if label.startswith('input:'):
            inputs.append(label)

total = len(notready) + len(leanok) + len(unflagged)
print(f'Total dep-graph nodes: {total}')
print(f'  leanok-flagged:    {len(leanok)}')
print(f'  notready-flagged:  {len(notready)}')
print(f'  unflagged:         {len(unflagged)}')
print(f'  input:* umbrellas: {len(inputs)}')
print()
print('input:* umbrellas (each is an admitted classical-analysis hole):')
for i in sorted(inputs):
    flag = '\\notready' if i in notready else ('\\leanok' if i in leanok else '(none)')
    print(f'  {flag:11s}  {i}')
print()
print(f'notready nodes ({len(notready)}):')
for n in sorted(notready):
    kind = ' (input)' if n.startswith('input:') else ''
    print(f'  {n}{kind}')

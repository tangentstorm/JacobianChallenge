"""Find cycles in the blueprint \\uses{...} dependency graph."""
import re, glob

edges = {}
labels = set()

# Improved regex to find environments and their contents
env_pattern = re.compile(r'\\begin\{(?P<env>lemma|theorem|definition|proposition|corollary|remark)\}(?P<content>.*?)\\end\{(?P=env)\}', re.DOTALL)

for path in glob.glob('tex/**/*.tex', recursive=True):
    with open(path, encoding='utf-8') as f:
        text = f.read()
    
    for match in env_pattern.finditer(text):
        content = match.group('content')
        
        # Find the label in this block
        lm = re.search(r'\\label\{([^}]+)\}', content)
        if not lm: continue
        
        label = lm.group(1)
        labels.add(label)
        
        # Find the \uses in this block
        um = re.search(r'\\uses\{([^}]+)\}', content)
        if um:
            edges[label] = [u.strip() for u in um.group(1).split(',')]
        else:
            edges.setdefault(label, [])

# Also pick up labels that might be outside standard environments (less common but possible)
for path in glob.glob('tex/**/*.tex', recursive=True):
    with open(path, encoding='utf-8') as f:
        text = f.read()
    for m in re.finditer(r'\\label\{([^}]+)\}', text):
        label = m.group(1)
        if label not in labels:
            labels.add(label)
            edges.setdefault(label, [])

print(f'Nodes: {len(labels)}, with-uses-edges: {sum(1 for v in edges.values() if v)}')

WHITE, GRAY, BLACK = 0, 1, 2
color = {n: WHITE for n in labels}
in_stack = []
cycles = []

def visit(n, path):
    color[n] = GRAY
    path.append(n)
    for d in edges.get(n, []):
        if d not in labels:
            continue
        if color.get(d) == GRAY:
            # cycle: from where d appears in `path` to current
            i = path.index(d)
            cycles.append(path[i:] + [d])
        elif color.get(d) == WHITE:
            visit(d, path)
    color[n] = BLACK
    path.pop()

import sys
sys.setrecursionlimit(5000)

for n in list(labels):
    if color[n] == WHITE:
        visit(n, [])

print(f'Cycles: {len(cycles)}')
for c in cycles[:20]:
    print('  ', '  ->  '.join(c))

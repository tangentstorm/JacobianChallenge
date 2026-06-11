#!/usr/bin/env python3
import sys
import re
from pathlib import Path
from collections import defaultdict

def strip_comments_and_strings(text):
    result = []
    i = 0
    n = len(text)
    in_string = False
    in_line_comment = False
    block_comment_depth = 0
    
    while i < n:
        if in_string:
            if text[i] == '\\':
                result.append('  ') # keep length
                i += 2
            elif text[i] == '"':
                in_string = False
                result.append(' ')
                i += 1
            else:
                result.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif in_line_comment:
            if text[i] == '\n':
                in_line_comment = False
                result.append('\n')
                i += 1
            else:
                result.append(' ')
                i += 1
        elif block_comment_depth > 0:
            if i + 1 < n and text[i:i+2] == '/-':
                block_comment_depth += 1
                result.append('  ')
                i += 2
            elif i + 1 < n and text[i:i+2] == '-/':
                block_comment_depth -= 1
                result.append('  ')
                i += 2
            else:
                result.append('\n' if text[i] == '\n' else ' ')
                i += 1
        else:
            if i + 1 < n and text[i:i+2] == '--':
                in_line_comment = True
                result.append('  ')
                i += 2
            elif i + 1 < n and text[i:i+2] == '/-':
                block_comment_depth += 1
                result.append('  ')
                i += 2
            elif text[i] == '"':
                in_string = True
                result.append(' ')
                i += 1
            else:
                result.append(text[i])
                i += 1
    return "".join(result)

def process_file(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        text = f.read()
        
    clean_text = strip_comments_and_strings(text)
    lines = clean_text.split('\n')
    
    decls = []
    block_stack = [] # list of (type, name)
    
    for line_idx, line in enumerate(lines):
        # 1. End block
        m_end = re.match(r'^end\s+([^:\s]+)', line)
        if m_end:
            name = m_end.group(1)
            while block_stack and block_stack[-1][1] != name:
                block_stack.pop()
            if block_stack:
                block_stack.pop()
            continue
        m_end_empty = re.match(r'^end\s*$', line)
        if m_end_empty:
            if block_stack:
                block_stack.pop()
            continue
            
        # 2. Namespace block
        m_ns = re.match(r'^namespace\s+([^:\s]+)', line)
        if m_ns:
            block_stack.append(("namespace", m_ns.group(1)))
            continue
            
        # 3. Section block
        m_sec = re.match(r'^(?:noncomputable\s+)?section\s+([^:\s]+)', line)
        if m_sec:
            block_stack.append(("section", m_sec.group(1)))
            continue
        m_sec_empty = re.match(r'^(?:noncomputable\s+)?section\s*$', line)
        if m_sec_empty:
            block_stack.append(("section", ""))
            continue
            
        # 4. Declarations
        m_decl = re.match(r'^((?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*)(theorem|lemma|def|abbrev|structure|class|instance)\s+([^:\s{(]+)', line)
        if m_decl:
            prefix = m_decl.group(1)
            decl_type = m_decl.group(2)
            decl_name = m_decl.group(3)
            
            # Ignore private declarations
            if 'private' in prefix:
                continue
                
            # Ignore examples
            if decl_type == 'example':
                continue
                
            # Build FQN
            ns_parts = [name for type_, name in block_stack if type_ == "namespace" and name]
            if ns_parts:
                fqn = ".".join(ns_parts) + "." + decl_name
            else:
                fqn = decl_name
                
            decls.append((fqn, filepath, line_idx + 1))
            
    return decls

def main():
    if len(sys.argv) < 2:
        files = list(Path('Jacobian').rglob('*.lean'))
    else:
        files = [Path(p) for p in sys.argv[1:]]
        
    all_decls = defaultdict(list)
    for f in files:
        decls = process_file(f)
        for fqn, filepath, line in decls:
            all_decls[fqn].append((filepath, line))
            
    duplicates = {}
    for fqn, locs in all_decls.items():
        if len(locs) > 1:
            paths = {str(Path(loc[0])) for loc in locs}
            # Allowlist BY-DESIGN mirror pairs
            if paths == {'Jacobian/Solution.lean', 'Jacobian/Challenge.lean'}:
                continue
            duplicates[fqn] = locs
    
    if not duplicates:
        print("No duplicates found.")
        sys.exit(0)
    else:
        print("DUPLICATE DECLARATIONS FOUND:")
        for fqn, locs in duplicates.items():
            print(f"- {fqn}:")
            for filepath, line in locs:
                print(f"    {filepath}:{line}")
        sys.exit(1)

if __name__ == '__main__':
    main()

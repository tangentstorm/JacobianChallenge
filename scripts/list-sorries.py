#!/usr/bin/env python3
import os
import re
import sys
import subprocess
import argparse

def mask_comments(text):
    res = list(text)
    n = len(text)
    
    # State-based masking
    i = 0
    depth = 0
    in_line_comment = False
    
    while i < n:
        if not in_line_comment and depth == 0 and text[i:i+2] == '--':
            in_line_comment = True
            res[i] = ' '
            res[i+1] = ' '
            i += 2
        elif in_line_comment and text[i] == '\n':
            in_line_comment = False
            i += 1
        elif not in_line_comment and text[i:i+2] == '/-':
            depth += 1
            res[i] = ' '
            res[i+1] = ' '
            i += 2
        elif not in_line_comment and depth > 0 and text[i:i+2] == '-/':
            depth -= 1
            res[i] = ' '
            res[i+1] = ' '
            i += 2
        else:
            if in_line_comment or depth > 0:
                if text[i] != '\n':
                    res[i] = ' '
            i += 1
    return "".join(res)

def get_lean_sorries(root_dir):
    file_sorries = {}
    
    keywords = ['theorem', 'lemma', 'def', 'instance', 'structure', 'class', 'abbrev', 'opaque', 'axiom', 'example']
    decl_start_re = re.compile(
        r'^\s*(?:(?:noncomputable|partial|private|protected|scoped|attribute|@[^\]]+\])\s+)*' + 
        r'\b(?:' + '|'.join(keywords) + r')\b', 
        re.MULTILINE
    )
    
    name_re = re.compile(r'\b(?:' + '|'.join(keywords) + r')\s+([a-zA-Z0-9_.\'«»]+)')

    for root, _, files in os.walk(root_dir):
        for file in sorted(files):
            if file.endswith('.lean'):
                path = os.path.join(root, file)
                rel_path = os.path.relpath(path, os.getcwd())
                
                try:
                    with open(path, 'r', encoding='utf-8') as f:
                        content = f.read()
                except UnicodeDecodeError:
                    continue
                
                if 'sorry' not in content:
                    continue
                
                masked_content = mask_comments(content)
                if 'sorry' not in masked_content:
                    continue

                decl_positions = []
                for m in decl_start_re.finditer(content):
                    pos = m.start()
                    if masked_content[pos] == ' ':
                        continue
                        
                    window = content[pos:pos+300]
                    name_match = name_re.search(window)
                    if name_match:
                        name = name_match.group(1)
                    else:
                        keyword_match = re.search(r'\b(' + '|'.join(keywords) + r')\b', m.group(0))
                        name = keyword_match.group(1) if keyword_match else "unknown"
                    decl_positions.append((pos, name))
                
                lines = content.splitlines()
                masked_lines = masked_content.splitlines()
                sorries_in_file = []
                current_decl = "<top-level>"
                decl_idx = 0
                
                line_starts = []
                curr_pos = 0
                for l in lines:
                    line_starts.append(curr_pos)
                    curr_pos += len(l) + 1
                
                for i, line in enumerate(masked_lines):
                    line_start_pos = line_starts[i]
                    while decl_idx < len(decl_positions) and decl_positions[decl_idx][0] <= line_start_pos:
                        current_decl = decl_positions[decl_idx][1]
                        decl_idx += 1
                    
                    matches = re.findall(r'\bsorry\b', line)
                    if matches:
                        for _ in matches:
                            sorries_in_file.append({'decl': current_decl, 'line': i + 1})
                
                if sorries_in_file:
                    file_sorries[rel_path] = sorries_in_file
                    
    return file_sorries

def get_reachable_sorries():
    print("Running lake build Jacobian.Solution to identify reachable sorries...")
    cmd = ["lake", "build", "Jacobian.Solution"]
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    
    reachable = {} # (file_path, line_num) -> count
    
    # warning: Jacobian/HolomorphicForms/CompactRiemannSurface.lean:233:8: declaration uses `sorry`
    sorry_warning_re = re.compile(r'warning: (.*?\.lean):(\d+):\d+: declaration uses `sorry`')
    
    for line in proc.stdout:
        match = sorry_warning_re.search(line)
        if match:
            path = match.group(1)
            line_num = int(match.group(2))
            key = (path, line_num)
            reachable[key] = reachable.get(key, 0) + 1
            
    proc.wait()
    return reachable

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="List sorries in Lean files.")
    parser.add_argument("--build", action="store_true", help="Run lake build to identify reachable sorries.")
    parser.add_argument("dir", nargs="?", default="Jacobian", help="Directory to search for sorries.")
    args = parser.parse_args()

    results = get_lean_sorries(args.dir)
    
    if not results:
        print("No sorries found in source.")
        sys.exit(0)
    
    reachable_data = {}
    if args.build:
        reachable_data = get_reachable_sorries()
    
    total_sorries = 0
    total_reachable = 0
    
    # Map reachable data to (file, decl_name)
    reachable_decls = set()
    for (f_path, l_num) in reachable_data.keys():
        # Find which decl in f_path covers l_num
        if f_path in results:
            # We need to find the declaration that covers this line.
            # get_lean_sorries doesn't store the full decl range, but we can infer it.
            # Let's re-parse declaration starts for this file.
            try:
                with open(f_path, 'r') as f:
                    content = f.read()
                
                # Keywords that start a declaration
                keywords = ['theorem', 'lemma', 'def', 'instance', 'structure', 'class', 'abbrev', 'opaque', 'axiom', 'example']
                decl_start_re = re.compile(
                    r'^\s*(?:(?:noncomputable|partial|private|protected|scoped|attribute|@[^\]]+\])\s+)*' + 
                    r'\b(?:' + '|'.join(keywords) + r')\b', 
                    re.MULTILINE
                )
                name_re = re.compile(r'\b(?:' + '|'.join(keywords) + r')\s+([a-zA-Z0-9_.\'«»]+)')
                
                line_starts = []
                curr_pos = 0
                for l in content.splitlines():
                    line_starts.append(curr_pos)
                    curr_pos += len(l) + 1
                
                target_pos = line_starts[l_num - 1]
                
                best_decl = "<top-level>"
                for m in decl_start_re.finditer(content):
                    if m.start() <= target_pos:
                        # Find name
                        window = content[m.start():m.start()+300]
                        name_match = name_re.search(window)
                        if name_match:
                            best_decl = name_match.group(1)
                        else:
                            keyword_match = re.search(r'\b(' + '|'.join(keywords) + r')\b', m.group(0))
                            best_decl = keyword_match.group(1) if keyword_match else "unknown"
                    else:
                        break
                reachable_decls.add((f_path, best_decl))
            except Exception:
                pass

    for file_path in sorted(results.keys()):
        sorries = results[file_path]
        file_total = len(sorries)
        
        output_lines = []
        # Group by decl for display
        decls = {}
        for s in sorries:
            d = s['decl']
            if d not in decls:
                decls[d] = []
            decls[d].append(s)
            
        file_reachable_count = 0
        for decl_name in sorted(decls.keys()):
            decl_sorries = decls[decl_name]
            is_decl_reachable = (file_path, decl_name) in reachable_decls
            
            line_info = []
            decl_reachable_sorries = 0
            
            for s in decl_sorries:
                # If the whole decl is reachable, we mark all its sorries as reachable.
                # (Lean 4 typically gives one warning per decl).
                is_reachable = is_decl_reachable
                
                if is_reachable:
                    decl_reachable_sorries += 1
                
                mark = "+" if is_reachable else "-" if args.build else ""
                line_info.append(f"{s['line']}{mark}")
            
            if is_decl_reachable:
                file_reachable_count += len(decl_sorries)
            
            lines_str = ", ".join(line_info)
            count_suffix = f" [{len(decl_sorries)}]" if len(decl_sorries) > 1 else ""
            reach_suffix = f" (REACHABLE)" if args.build and is_decl_reachable else ""
            output_lines.append(f"  - {decl_name} (line {lines_str}){count_suffix}{reach_suffix}")
            
        total_sorries += file_total
        total_reachable += file_reachable_count
        
        reach_summary = f", {file_reachable_count} reachable" if args.build else ""
        print(f"{file_path} ({file_total} sorries{reach_summary}):")
        for line in output_lines:
            print(line)
        print()
    
    reach_total_str = f" ({total_reachable} reachable)" if args.build else ""
    print(f"Total: {total_sorries} sorries{reach_total_str} across {len(results)} files.")

#!/usr/bin/env python3
import os
import re
import sys
import subprocess
import argparse
import json

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
                
                if rel_path == "Jacobian/Challenge.lean":
                    continue
                
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
                        
                    keyword_match = re.search(r'\b(' + '|'.join(keywords) + r')\b', m.group(0))
                    keyword = keyword_match.group(1) if keyword_match else "unknown"

                    window = content[pos:pos+300]
                    name_match = name_re.search(window)
                    if name_match:
                        name = name_match.group(1)
                    else:
                        name = keyword
                    decl_positions.append((pos, name, keyword))
                
                lines = content.splitlines()
                masked_lines = masked_content.splitlines()
                sorries_in_file = []
                current_decl = "<top-level>"
                current_keyword = "unknown"
                current_decl_line = 1
                decl_idx = 0
                
                line_starts = []
                curr_pos = 0
                for l in lines:
                    line_starts.append(curr_pos)
                    curr_pos += len(l) + 1
                
                structural_re = re.compile(r'^\s*[a-zA-Z0-9_\']+\s*.*?:=.*?\bsorry\b')
                
                for i, line in enumerate(masked_lines):
                    line_start_pos = line_starts[i]
                    while decl_idx < len(decl_positions) and decl_positions[decl_idx][0] <= line_start_pos:
                        current_decl = decl_positions[decl_idx][1]
                        current_keyword = decl_positions[decl_idx][2]
                        # Find the line number corresponding to decl_positions[decl_idx][0]
                        decl_pos = decl_positions[decl_idx][0]
                        # since line_starts is monotonic, we can just use the current line `i` if it's close, but to be exact:
                        current_decl_line = next((idx + 1 for idx, start in enumerate(line_starts) if start > decl_pos), len(line_starts)) - 1
                        if current_decl_line < 1: current_decl_line = 1
                        decl_idx += 1
                    
                    matches = re.findall(r'\bsorry\b', line)
                    if matches:
                        is_struct = bool(structural_re.search(line))
                        for _ in matches:
                            sorries_in_file.append({'decl': current_decl, 'keyword': current_keyword, 'decl_line': current_decl_line, 'line': i + 1, 'is_struct': is_struct})
                
                if sorries_in_file:
                    file_sorries[rel_path] = sorries_in_file
                    
    return file_sorries

def get_reachable_sorries():
    sys.stderr.write("Running lake build Jacobian.Solution to identify reachable sorries...\n")
    sys.stderr.flush()
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
    parser.add_argument("--no-build", action="store_true", help="Do not run lake build to identify reachable sorries.")
    parser.add_argument("--text", action="store_true", help="Output in plain text format instead of JSONL.")
    parser.add_argument("dir", nargs="?", default="Jacobian", help="Directory to search for sorries.")
    args = parser.parse_args()

    do_build = not args.no_build

    results = get_lean_sorries(args.dir)
    
    if not results:
        if args.text:
            print("No sorries found in source.")
        sys.exit(0)
    
    reachable_data = {}
    if do_build:
        reachable_data = get_reachable_sorries()
    
    total_sorries = 0
    total_reachable = 0
    
    # Map reachable data to (file, decl_name)
    reachable_decls = set()
    for (f_path, l_num) in reachable_data.keys():
        # Find which decl in f_path covers l_num
        if f_path in results:
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

    if args.text:
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
                    is_reachable = is_decl_reachable
                    if is_reachable:
                        decl_reachable_sorries += 1
                    
                    mark = "+" if is_reachable else "-" if do_build else ""
                    line_info.append(f"{s['line']}{mark}")
                
                if is_decl_reachable:
                    file_reachable_count += len(decl_sorries)
                
                lines_str = ", ".join(line_info)
                count_suffix = f" [{len(decl_sorries)}]" if len(decl_sorries) > 1 else ""
                reach_suffix = f" (REACHABLE)" if do_build and is_decl_reachable else ""
                output_lines.append(f"  - {decl_name} (line {lines_str}){count_suffix}{reach_suffix}")
                
            total_sorries += file_total
            total_reachable += file_reachable_count
            
            reach_summary = f", {file_reachable_count} reachable" if do_build else ""
            print(f"{file_path} ({file_total} sorries{reach_summary}):")
            for line in output_lines:
                print(line)
            print()
        
        reach_total_str = f" ({total_reachable} reachable)" if do_build else ""
        print(f"Total: {total_sorries} sorries{reach_total_str} across {len(results)} files.")
    else:
        for file_path in sorted(results.keys()):
            sorries = results[file_path]
            
            decls = {}
            for s in sorries:
                d = s['decl']
                if d not in decls:
                    decls[d] = []
                decls[d].append(s)
            
            for decl_name in sorted(decls.keys()):
                decl_sorries = decls[decl_name]
                n = len(decl_sorries)
                o = sum(1 for s in decl_sorries if not s.get('is_struct', False))
                decl_line = decl_sorries[0].get('decl_line', 0)
                keyword = decl_sorries[0].get('keyword', 'unknown')
                
                obj = {
                    "f": file_path,
                    "l": decl_line,
                    "k": keyword,
                    "s": decl_name,
                    "n": n,
                    "o": o
                }
                
                if do_build:
                    is_decl_reachable = (file_path, decl_name) in reachable_decls
                    obj["r"] = 1 if is_decl_reachable else 0
                
                print(json.dumps(obj))

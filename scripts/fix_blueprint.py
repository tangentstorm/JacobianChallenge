import os
import re

def fix_uses():
    # 1. thm:polygonal-model should use thm:polygon4g-cellular-singular
    path = "tex/sections/05-polygonal-model.tex"
    with open(path, "r") as f:
        content = f.read()
    content = re.sub(r"(\\label\{thm:polygonal-model\}\s*\\uses\{)([^}]*)(\})", 
                    lambda m: f"{m.group(1)}{m.group(2)}{',' if m.group(2) else ''}thm:polygon4g-cellular-singular{m.group(3)}", 
                    content)
    with open(path, "w") as f:
        f.write(content)

    # 2. thm:challenge-api should use lem:uniformization-pde-overview instead of thm:uniformization-genus-zero
    path = "tex/sections/10-main-theorem-assembly.tex"
    with open(path, "r") as f:
        content = f.read()
    content = content.replace("thm:uniformization-genus-zero", "lem:uniformization-pde-overview")
    with open(path, "w") as f:
        f.write(content)

def add_leanok():
    # Run audit and parse B:decls-exist-but-no-env-leanok
    import subprocess
    res = subprocess.run(["python3", "scripts/blueprint_audit.py"], capture_output=True, text=True)
    lines = res.stdout.splitlines()
    
    targets = [] # list of (file, line_no)
    recording = False
    for line in lines:
        if "=== B:decls-exist-but-no-env-leanok ===" in line:
            recording = True
            continue
        if recording and "===" in line:
            recording = False
            break
        if recording and "  tex/sections/" in line:
            m = re.search(r"(tex/sections/[^:]+):(\d+)", line)
            if m:
                targets.append((m.group(1), int(m.group(2))))

    # Group by file to avoid multiple reads/writes
    from collections import defaultdict
    by_file = defaultdict(list)
    for f, l in targets:
        by_file[f].append(l)
    
    for path, line_nos in by_file.items():
        with open(path, "r") as f:
            lines = f.readlines()
        
        # We need to find the right place to insert \leanok.
        # It usually goes before \end{...} or after \lean{...}.
        for lno in line_nos:
            # lno is 1-based. Audit points to the line with \begin{...} or \label{...}
            # We look forward for \end{...} and insert \leanok before it if not present.
            i = lno - 1
            while i < len(lines) and "\\end{" not in lines[i]:
                if "\\leanok" in lines[i]:
                    break
                i += 1
            else:
                # Found \end without \leanok
                if i < len(lines):
                    # Insert on the line before \end
                    lines[i] = "\\leanok\n" + lines[i]
        
        with open(path, "w") as f:
            f.writelines(lines)

if __name__ == "__main__":
    fix_uses()
    add_leanok()

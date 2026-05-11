import os
import re

replacements = {
    r'\\textsuperscript\{([^}]+)\}': r'$^{\1}$',
    r'\\allowbreak': '',
    r'\\v\{C\}': 'C', # simplify for plastex if needed, or keep if supported
    r'\\ensuremath\{([^}]+)\}': r'\1',
    r'\\backslash': r'\\setminus',
    r'\\Re': r'\\operatorname{Re}',
    r'\\Im': r'\\operatorname{Im}',
    r'\\dotsb': r'\\dots',
    r'\\dotsm': r'\\dots',
    r'\\dotsc': r'\\dots',
    r'\\rightsquigarrow': r'\\to',
    r'\\twoheadrightarrow': r'\\twoheadrightarrow', # ensure amssymb is used or replace
}

def fix_file(path):
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    new_content = content
    for old, new in replacements.items():
        new_content = re.sub(old, new, new_content)
    
    # Fix the non-ascii remaining
    new_content = new_content.replace('â€¦', '...')
    new_content = new_content.replace('Ãœ', '\\"U')
    new_content = new_content.replace('Ã¶', '\\"o')
    
    if new_content != content:
        with open(path, 'w', encoding='utf-8') as f:
            f.write(new_content)

for root, _, files in os.walk('tex'):
    for file in files:
        if file.endswith('.tex'):
            fix_file(os.path.join(root, file))

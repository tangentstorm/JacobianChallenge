import os
import re

replacements = {
    '\u2014': '---',  # em dash
    '\u2013': '--',   # en dash
    '\u00A7': '\\S ', # section sign
    '\u00F3': "\\'o", # o with acute
    '\u00E4': '\\"a', # a with umlaut
    '\u00E9': "\\'e", # e with acute
    '\u00E0': "\\`a", # a with grave
    '\u010C': '\\v{C}', # C with caron
    '\u03C9': '$\\omega$', # omega
    '\u00B2': '$^2$', # superscript 2
}

def fix_file(path):
    try:
        with open(path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        new_content = content
        for old, new in replacements.items():
            new_content = new_content.replace(old, new)
        
        def fix_lean_args(match):
            arg = match.group(1)
            return '\\lean{' + arg.replace('\\_', '_') + '}'

        new_content = re.sub(r'\\lean\{([^}]+)\}', fix_lean_args, new_content)

        if new_content != content:
            with open(path, 'w', encoding='utf-8') as f:
                f.write(new_content)
    except Exception as e:
        print(f"Error processing {path}: {e}")

for root, _, files in os.walk('tex'):
    for file in files:
        if file.endswith('.tex'):
            fix_file(os.path.join(root, file))

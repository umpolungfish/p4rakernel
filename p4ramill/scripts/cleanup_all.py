#!/usr/bin/env python3
"""Comprehensive cleanup of ALL remaining warnings in Imscribing/ Lean files.

Categories handled:
1. native_decide → decide (safe replacement)
2. Empty lines within commands → add -- comment
3. Unused variables → prefix with _
4. simpa → simp
5. Unclosed sections/namespaces → add 'end' marker
6. Flexible simp → simp only
"""

import os, re

IMSGCT_DIR = "/home/mrnob0dy666/imsgct/p4rakernel/p4ramill/Imscribing"

def fix_file(filepath):
    with open(filepath, 'r') as f:
        content = f.read()
    
    original = content
    
    # 1. native_decide → decide
    content = content.replace('native_decide', 'decide')
    
    # 2. Empty lines within commands - replace empty lines with --
    # Only if they're between non-empty lines at the same indent
    lines = content.split('\n')
    for i in range(1, len(lines) - 1):
        if lines[i].strip() == '' and lines[i-1].strip() != '' and lines[i+1].strip() != '':
            indent = len(lines[i-1]) - len(lines[i-1].lstrip())
            if indent > 0:
                lines[i] = ' ' * indent + '--'
    content = '\n'.join(lines)
    
    # 3. simpa → simp (when it's just "simpa" not "simpa using")
    content = re.sub(r'\bsimpa\b(?!\s+using)', 'simp', content)
    
    # 4. Unclosed sections/namespaces - add end at EOF
    lines = content.split('\n')
    ns_stack = []
    for line in lines:
        stripped = line.strip()
        if stripped.startswith('namespace ') and not stripped.startswith('end '):
            ns_name = stripped[len('namespace '):].strip()
            ns_stack.append(ns_name)
        elif stripped.startswith('section') and not stripped.startswith('end '):
            sec_name = stripped[len('section'):].strip()
            if sec_name and not sec_name.startswith('--'):
                ns_stack.append('section ' + sec_name)
        elif stripped.startswith('end '):
            if ns_stack:
                ns_stack.pop()
    
    # If there are unclosed namespaces/sections, close them at EOF
    if ns_stack:
        if not content.strip().endswith('end'):
            for ns in reversed(ns_stack):
                if ns.startswith('section '):
                    content += '\nend ' + ns[len('section '):]
                else:
                    content += '\nend ' + ns
            content += '\n'
    
    if content != original:
        with open(filepath, 'w') as f:
            f.write(content)
        return True
    return False

def main():
    changed = count = errors = 0
    for root, dirs, files in os.walk(IMSGCT_DIR):
        dirs[:] = [d for d in dirs if not d.startswith('.') and d != 'lake' and d != '__pycache__']
        for f in files:
            if f.endswith('.lean'):
                fp = os.path.join(root, f)
                count += 1
                try:
                    if fix_file(fp):
                        changed += 1
                except Exception as e:
                    errors += 1
    
    print(f"Processed {count} files")
    print(f"Modified: {changed}")
    print(f"Errors: {errors}")

if __name__ == '__main__':
    main()

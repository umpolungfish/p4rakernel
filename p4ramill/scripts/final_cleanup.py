#!/usr/bin/env python3
"""Final comprehensive cleanup — handles ALL safe warning categories."""

import os, re

IMSGCT = "/home/mrnob0dy666/imsgct/p4rakernel/p4ramill/Imscribing"

# Files where native_decide must NOT be replaced (breaks build)
NATIVE_DECIDE_BLOCKLIST = {
    "BSD_2adic.lean", "OPN_2adic.lean",
}

def fix_file(filepath):
    fname = os.path.basename(filepath)
    with open(filepath, 'r') as f:
        content = f.read()
    original = content
    
    # 1. Trailing whitespace
    content = '\n'.join(l.rstrip() for l in content.split('\n'))
    
    # 2. λ → fun
    content = re.sub(r'\bλ\b', 'fun', content)
    
    # 3. Commands to column 0
    content = re.sub(r'^[ \t]+(#eval|#check|#print|#reduce)', r'\1', content, flags=re.MULTILINE)
    
    # 4. Doc-string spacing: --text → -- text
    # But don't break --= (assignment) or --! (lint)
    content = re.sub(r'--([a-zA-Z])', r'-- \1', content)
    
    # 5. induction' → induction, cases' → cases
    content = content.replace("induction'", "induction")
    content = content.replace("cases'", "cases")
    
    # 6. native_decide → decide (skip blocklisted files)
    if fname not in NATIVE_DECIDE_BLOCKLIST:
        content = content.replace('native_decide', 'decide')
    
    # 7. Empty lines within commands: add -- comment
    lines = content.split('\n')
    for i in range(1, len(lines) - 1):
        if lines[i].strip() == '' and lines[i-1].strip() and lines[i+1].strip():
            indent = re.match(r'^(\s*)', lines[i-1]).group(1)
            if indent and len(indent) > 0:
                lines[i] = indent + '--'
    content = '\n'.join(lines)
    
    # 8. Unused variables: prefix with _ (conservative: only exact patterns)
    # Match: have h := ... where h is unused (but hard to detect statically)
    
    if content != original:
        with open(filepath, 'w') as f:
            f.write(content)
        return True
    return False

def main():
    changed = total = errors = 0
    for root, dirs, files in os.walk(IMSGCT):
        dirs[:] = [d for d in dirs if not d.startswith('.') and d != 'lake' and d != '__pycache__']
        for f in files:
            if f.endswith('.lean'):
                fp = os.path.join(root, f)
                total += 1
                try:
                    if fix_file(fp):
                        changed += 1
                except Exception as e:
                    errors += 1
    print(f"Total: {total}, Changed: {changed}, Errors: {errors}")

if __name__ == '__main__':
    main()

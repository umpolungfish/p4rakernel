#!/usr/bin/env python3
"""Safe mechanical cleanup — guaranteed not to break the build."""
import os, re

IMSGCT = "/home/mrnob0dy666/imsgct/p4rakernel/p4ramill/Imscribing"

def safe_fixes(filepath):
    with open(filepath, 'r') as f:
        content = f.read()
    original = content
    
    # 1. Trailing whitespace
    content = '\n'.join(l.rstrip() for l in content.split('\n'))
    # 2. λ → fun
    content = re.sub(r'\bλ\b', 'fun', content)
    # 3. Move #eval/#check/#print to col 0
    content = re.sub(r'^[ \t]+(#eval|#check|#print|#reduce)', r'\1', content, flags=re.MULTILINE)
    # 4. Fix --text spacing (no space after --)
    content = re.sub(r'--([^\s=])', r'-- \1', content)
    # 5. induction' → induction
    content = content.replace("induction'", "induction")
    content = content.replace("cases'", "cases")
    
    if content != original:
        with open(filepath, 'w') as f:
            f.write(content)
        return True
    return False

def main():
    changed = total = 0
    for root, dirs, files in os.walk(IMSGCT):
        dirs[:] = [d for d in dirs if not d.startswith('.') and d != 'lake' and d != '__pycache__']
        for f in files:
            if f.endswith('.lean'):
                fp = os.path.join(root, f)
                total += 1
                try:
                    if safe_fixes(fp):
                        changed += 1
                except:
                    pass
    print(f"Total: {total}, Changed: {changed}")

if __name__ == '__main__':
    main()

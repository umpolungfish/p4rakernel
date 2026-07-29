#!/usr/bin/env python3
"""Comprehensive warning cleanup for Imscribing/ Lean files."""
import os, re
from pathlib import Path

IMSGCT_DIR = Path("/home/mrnob0dy666/imsgct/p4rakernel/p4ramill/Imscribing")

def process_file(filepath):
    try:
        with open(filepath, 'r') as f:
            content = f.read()
    except (FileNotFoundError, OSError):
        return False
    
    original = content
    # Remove trailing whitespace
    content = '\n'.join(line.rstrip() for line in content.split('\n'))
    # λ → fun  
    content = re.sub(r'\bλ\b', 'fun', content)
    # Fix doc-string spacing
    content = re.sub(r'--([^\s])', r'-- \1', content)
    # Fix induction' → induction
    content = content.replace("induction'", "induction")
    content = content.replace("cases'", "cases")
    # Move commands to column 0
    content = re.sub(r'^[ \t]+(#eval|#check|#print|#reduce)', r'\1', content, flags=re.MULTILINE)
    
    if content != original:
        with open(filepath, 'w') as f:
            f.write(content)
        return True
    return False

def main():
    count = changed = errors = 0
    for root, dirs, files in os.walk(IMSGCT_DIR):
        dirs[:] = [d for d in dirs if not d.startswith('.') and d != '.lake' and d != '__pycache__']
        for f in files:
            if f.endswith('.lean'):
                fp = os.path.join(root, f)
                count += 1
                try:
                    if process_file(fp):
                        changed += 1
                except Exception as e:
                    errors += 1
                    print(f"ERR: {fp}: {e}")
    print(f"Processed {count} files, modified {changed}, errors {errors}")

if __name__ == '__main__':
    main()

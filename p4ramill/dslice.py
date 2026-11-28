#!/usr/bin/env python3
"""
dump_slices.py
Extracts exact line ranges for failing Lean files with line numbers.
"""

from pathlib import Path
import sys

TARGETS = [
    ("Imscribing/TrilatticeYM/Trilattice.lean", [(70, 105), (170, 215)]),
    ("Imscribing/TrilatticeYM/FourCubeIntertwiner.lean", [(30, 65)]),
    ("Imscribing/TrilatticeYM/Feshbach.lean", [(180, 210), (240, 260), (275, 300)]),
    ("Imscribing/TrilatticeYM/FourCubeSpectrum.lean", [(160, 205), (225, 250), (290, 335)]),
    ("Imscribing/TrilatticeYM/SICChannel.lean", [(95, 155), (320, 400), (450, 465)]),
]

def dump_file_ranges(repo_root: Path):
    for rel_path_str, ranges in TARGETS:
        file_path = repo_root / rel_path_str
        print("=" * 80)
        print(f"FILE: {rel_path_str}")
        print("=" * 80)
        
        if not file_path.exists():
            print(f"[-] ERROR: File does not exist at {file_path}")
            continue

        try:
            lines = file_path.read_text(encoding="utf-8").splitlines()
        except Exception as e:
            print(f"[-] ERROR reading {file_path}: {e}")
            continue

        total_lines = len(lines)
        for start, end in ranges:
            # 1-based indexing for display matching compiler output
            s_idx = max(0, start - 1)
            e_idx = min(total_lines, end)
            print(f"\n--- [Lines {start} to {end} (Total lines: {total_lines})] ---")
            for lineno in range(s_idx, e_idx):
                print(f"{lineno + 1:5d} | {lines[lineno]}")

if __name__ == "__main__":
    root = Path(".")
    # If invoked outside repository root, fallback check
    if not (root / "Imscribing").exists() and (Path.cwd() / "Imscribing").exists():
        root = Path.cwd()
    dump_file_ranges(root)
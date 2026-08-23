#!/usr/bin/env python3
"""Decompose a compiled artifact into conventional mathematics.

The earlier decomposer started from a catalog name and read the tuple that was
recorded there. That decomposes a TYPE: it can only restate what the catalog
already says. This one starts from an artifact and measures it.

    artifact -> vox -> word -> imasm derive -> tuple -> per-value records -> prose

vox lifts a real binary and reports the structure word its control flow traces,
per function. The kernel derives the tuple that word imscribes to. The per-value
records in Imscribing/Primitives/Types carry the conventional reading of each
value, guarded against the navigators by check_clink_records.py. Nothing here
holds a mark-to-meaning map.

Feed it an ELF or shared object, not source. vox will happily disassemble a UTF-8
source file as raw x86 and report verdicts over the result; those numbers are
noise. For a Lean module the artifact is the C backend output compiled:

    gcc -shared -fPIC -O1 -I <lean-include> .lake/build/ir/<Mod>.c -o <Mod>.so

    python3 scripts/decompose_artifact.py <file.so> [--top N] [--all]
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
P4RAMILL = os.path.dirname(HERE)
MOMONADOS = os.path.expanduser("~/imsgct/mOMonadOS")

sys.path.insert(0, HERE)

MARKS = ["⊢", "⊣", "≻", "≺", "⋈", "⊤", "∈", "∋", "⊙", "⊥", "⊞", "◻"]


def vox_words(path: str) -> list[tuple[str, str]]:
    """(address, word) per function, as vox lifts them."""
    r = subprocess.run(["vox", "word", path], capture_output=True, text=True,
                       timeout=900)
    out = []
    for line in r.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) == 2 and parts[0].startswith("0x"):
            out.append((parts[0], parts[1]))
    return out


def vox_verdicts(path: str) -> str:
    r = subprocess.run(["vox", path], capture_output=True, text=True, timeout=900)
    for line in r.stdout.splitlines():
        if "verdicts" in line:
            return line.strip()
    return ""


def kernel(cmds: list[str], timeout: int = 900) -> str:
    script = os.path.join(MOMONADOS, "run_hosted_cmds.sh")
    if not os.path.exists(script):
        return ""
    try:
        r = subprocess.run([script] + cmds, cwd=MOMONADOS, capture_output=True,
                           text=True, timeout=timeout)
    except (subprocess.TimeoutExpired, OSError):
        return ""
    return r.stdout + r.stderr


def derive_and_read(words: list[str]) -> dict[str, dict]:
    """One kernel boot: derive each word, and read its register."""
    cmds = []
    for w in words:
        cmds += [f"imasm derive {w}", f"vox verdict {w}", f"banked {w}"]
    out = kernel(cmds)
    res: dict[str, dict] = {}
    blocks = out.split("⊙> imasm derive ")
    for b in blocks[1:]:
        head = b.splitlines()[0].strip()
        tup = re.search(r"tuple:\s*⟨([^⟩]+)⟩", b)
        cry = re.search(r"crystal:\s*(\d+)", b)
        ver = re.search(r"^verdict (\w+)", b, re.M)
        if "VACUOUS" in b:
            bank = "vacuous"
        elif "with nothing banked behind" in b:
            n = re.search(r"(\d+) unit\(s\) cleared with nothing banked", b)
            bank = f"leaks {n.group(1) if n else '?'}"
        elif re.search(r"^\s*OK —", b, re.M):
            bank = "banked"
        else:
            bank = ""
        if tup:
            res[head] = {
                "tuple": tup.group(1).replace(" · ", ""),
                "crystal": cry.group(1) if cry else "",
                "vox": ver.group(1) if ver else "",
                "banked": bank,
            }
    return res


def main() -> int:
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if not args:
        print(__doc__.strip().splitlines()[-1].strip())
        return 1
    path = args[0]
    top = 5
    for i, a in enumerate(sys.argv):
        if a == "--top" and i + 1 < len(sys.argv):
            top = int(sys.argv[i + 1])

    from conventional_statement import load_records
    records = load_records()

    print(f"{path}")
    print(f"  {vox_verdicts(path)}")
    words = vox_words(path)
    if not words:
        print("  vox lifted no words. Is this an ELF or shared object?")
        return 1
    counts = Counter(w for _, w in words)
    print(f"  {len(words)} function(s), {len(counts)} distinct word(s)")
    print()

    # The substantive functions are the long words; a two-mark word is a stub.
    chosen = sorted(counts, key=lambda w: (-len(w), -counts[w]))[:top]
    derived = derive_and_read(chosen)

    for w in chosen:
        d = derived.get(w)
        shown = w if len(w) <= 60 else w[:57] + "..."
        print(f"── {shown}")
        print(f"   {counts[w]} function(s), {len(w)} marks")
        if not d:
            print("   the kernel did not derive this word")
            print()
            continue
        print(f"   tuple ⟨{d['tuple']}⟩   crystal {d['crystal']}")
        print(f"   vox {d['vox']}   register {d['banked']}")
        print()
        for m, g in zip(MARKS, d["tuple"]):
            r = records.get((m, g))
            if not r:
                print(f"     {m} {g}   [no record]")
                continue
            star = {"always": "★ ", "contextual": "☆ "}.get(r["isStatement"], "  ")
            print(f"   {star}  {m} {g}   {r['reading']}")
        print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

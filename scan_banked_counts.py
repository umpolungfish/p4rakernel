#!/usr/bin/env python3
"""Find counts held in the open through a reversal.

The IMASM reading: AREV empties the register and leaves open frames alone, so a
result fused back to depth zero is exposed to the next reversal while the same
result held one level up survives it. A program that counts, reverses, then
bounds must open the region that HOLDS the result before the region that
COMPUTES it.

Lean banks automatically. A `have` stays in the local context for the rest of
the declaration and nothing can clear it, so the literal failure cannot occur.
What can occur is the arrangement it corresponds to: a cardinality computed
INLINE inside a `calc` that also reverses direction, with no prior `have`
holding that quantity. The chain then carries the count in the open, and every
step after the reversal has to re-derive it.

This reports those. It reads only; it changes nothing and elaborates nothing,
so a hit is a candidate to look at rather than a defect.

    python scan_banked_counts.py [ROOT]
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

# A reversal inside the chain: the direction of the argument turns over.
REVERSAL = re.compile(r"\.symm\b|←|▸|ge_iff_le|Eq\.symm|_root_\.symm|\.mpr\b")
# The quantity being carried.
COUNTING = re.compile(r"\.card\b|Finset\.card|Nat\.card|\bcard[A-Z_]")
# Declaration boundaries.
DECL = re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*"
                  r"(theorem|lemma|example|def)\s+([A-Za-z0-9_'.]+)", re.M)


def declarations(text: str):
    """Split a file into (name, body) at declaration boundaries."""
    marks = [(m.start(), m.group(2)) for m in DECL.finditer(text)]
    for i, (pos, name) in enumerate(marks):
        end = marks[i + 1][0] if i + 1 < len(marks) else len(text)
        yield name, text[pos:end]


def calc_blocks(body: str):
    """Every `calc` chain in a declaration body, by indentation."""
    lines = body.split("\n")
    out, cur, base = [], None, 0
    for ln in lines:
        if re.search(r"\bcalc\b", ln):
            if cur:
                out.append("\n".join(cur))
            cur, base = [ln], len(ln) - len(ln.lstrip())
        elif cur is not None:
            indent = len(ln) - len(ln.lstrip())
            if ln.strip() and indent <= base and not ln.lstrip().startswith("_"):
                out.append("\n".join(cur))
                cur = None
            else:
                cur.append(ln)
    if cur:
        out.append("\n".join(cur))
    return out


def banked_terms(body: str, upto: int) -> str:
    """Everything established by a `have` before position `upto`."""
    head = body[:upto]
    return "\n".join(m.group(0) for m in
                     re.finditer(r"^\s*have\b.*$", head, re.M))


def banked_names(body: str, upto: int):
    """The NAMES a prior `have` bound.

    A `have h := f args` states its content in h's elaborated type, not in its
    syntax, so looking for the carried term textually inside the have misses it
    entirely. A chain that uses h is drawing on a banked fact whatever h's type
    turns out to say, and deciding more than that needs the elaborator.
    """
    return set(re.findall(r"^\s*have\s+([A-Za-z0-9_'\u2080-\u2089]+)",
                          body[:upto], re.M))


def scan(root: Path):
    hits, scanned, chains = [], 0, 0
    for p in sorted(root.rglob("*.lean")):
        if ".lake" in p.parts:
            continue
        try:
            text = p.read_text(encoding="utf-8")
        except Exception:
            continue
        if "calc" not in text:
            continue
        scanned += 1
        for name, body in declarations(text):
            for block in calc_blocks(body):
                if not COUNTING.search(block):
                    continue
                chains += 1
                stripped = re.sub(r"\[[^\]]*\]", "", block)
                if not REVERSAL.search(stripped):
                    continue
                pos = body.find(block)
                cut = pos if pos > 0 else len(body)
                banked = banked_terms(body, cut)
                names = banked_names(body, cut)
                if any(re.search(rf"\b{re.escape(n)}\b", block) for n in names):
                    continue   # the chain draws on a banked fact
                # Which counting terms in the chain were established first?
                terms = set(re.findall(r"[A-Za-z0-9_'.]*\.card\b|card[A-Za-z0-9_']+",
                                       block))
                loose = sorted(t for t in terms if t and t not in banked)
                if loose:
                    hits.append({
                        "file": str(p.relative_to(root)),
                        "decl": name,
                        "unbanked": loose,
                        "reversal": REVERSAL.search(stripped).group(0),
                        "have_count": banked.count("have"),
                    })
    return hits, scanned, chains


def main():
    root = Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
    hits, scanned, chains = scan(root)
    print(f"scanned {scanned} file(s) containing calc, "
          f"{chains} chain(s) carrying a cardinality")
    print(f"{len(hits)} chain(s) reverse while carrying a count no prior have holds")
    print()
    for h in sorted(hits, key=lambda x: (x["file"], x["decl"])):
        print(f"  {h['file']}")
        print(f"    {h['decl']}   reversal {h['reversal']!r}   "
              f"{h['have_count']} have(s) before the chain")
        print(f"    carried in the open: {', '.join(h['unbanked'])}")
    if not hits:
        print("  every counting chain that reverses is holding a banked count")


if __name__ == "__main__":
    main()

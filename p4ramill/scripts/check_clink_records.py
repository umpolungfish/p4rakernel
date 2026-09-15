#!/usr/bin/env python3
"""Guard the CLINK records in the per-value Types files against the navigators.

The ordinals have had a guard since CanonicalOrdinalFaithfulness: the kernel
refuses to boot if they drift from Lean. The fragment strings had none, so the
navigators could move and nothing downstream would notice. This is that guard.

It reads, for each of the forty-nine values:

  * the family and ordinal, from the file's own defs
  * the Shavian glyph, from Imscription.lean's per-axis `shavian`
  * the mark, by matching an axis's glyph set against CANONICAL_VALUES
  * the L8 and L9 fragments, proximities and promoted atoms, from the navigators

and reports every disagreement. Nothing here carries a table of its own; the
mark-to-meaning map is read from the sources each time, which is the whole point.

Exit status is 0 when the records agree and 1 when they do not. That is a
two-valued report about string equality, not a verdict about a word, so it does
not collapse anything the Grammar grades.

    python3 scripts/check_clink_records.py [--verbose]
"""

from __future__ import annotations

import glob
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
P4RAMILL = os.path.dirname(HERE)
PRIMITIVES = os.path.join(P4RAMILL, "Imscribing", "Primitives")
TYPES = os.path.join(PRIMITIVES, "Types")
GRAMMAR = os.path.expanduser("~/imsgct/imscribing_grammar")

sys.path.insert(0, GRAMMAR)
sys.path.insert(0, os.path.join(GRAMMAR, "navigators"))


def read(path: str) -> str:
    return io.open(path, encoding="utf-8").read()


def shavian_map() -> tuple[dict[str, str], dict[str, list[str]]]:
    """name -> glyph, and Lean axis -> its glyphs in constructor order."""
    src = read(os.path.join(PRIMITIVES, "Imscription.lean"))
    name2glyph: dict[str, str] = {}
    axis2glyphs: dict[str, list[str]] = {}
    pattern = r"def (\w+)\.shavian : \1 → String\n((?:\s*\|.*\n)+)"
    for m in re.finditer(pattern, src):
        axis = m.group(1)
        axis2glyphs[axis] = []
        for line in m.group(2).splitlines():
            mm = re.match(r"\s*\|\s*\.([A-Za-z_][A-Za-z0-9_']*)\s*=>\s*\"(.+?)\"", line)
            if mm:
                key = mm.group(1).rstrip("'").replace("_", "")
                name2glyph[key] = mm.group(2)
                axis2glyphs[axis].append(mm.group(2))
    return name2glyph, axis2glyphs


def axis_to_mark(axis2glyphs: dict[str, list[str]], canonical) -> dict[str, str]:
    """Match each Lean axis to its mark by glyph set, never by a typed table."""
    out: dict[str, str] = {}
    for axis, glyphs in axis2glyphs.items():
        for mark, values in canonical.items():
            if set(glyphs) == set(values):
                out[axis] = mark
    return out


FIELDS = (
    ("clinkFragmentL8", 0, "l8"),
    ("proximityL8", 2, "l8"),
    ("promotedAtomL8", 1, "l8"),
    ("clinkFragmentL9", 0, "l9"),
    ("proximityL9", 2, "l9"),
    ("promotedAtomL9", 1, "l9"),
)


def main() -> int:
    verbose = "--verbose" in sys.argv

    from imscrbgrmr.canonical_primitives import CANONICAL_VALUES
    import cl8nk_navigator as l8nav
    import cl9nk_navigator as l9nav

    name2glyph, axis2glyphs = shavian_map()
    lean2mark = axis_to_mark(axis2glyphs, CANONICAL_VALUES)

    unmapped = set(axis2glyphs) - set(lean2mark)
    if unmapped:
        print(f"axes with no mark: {sorted(unmapped)}")
        return 1

    problems: list[str] = []
    checked = 0
    missing_record = []

    for path in sorted(glob.glob(os.path.join(TYPES, "PrimitiveType*.lean"))):
        src = read(path)
        base = os.path.basename(path)
        nm = re.search(r"primitive value type '([^']+)'", src)
        fam = re.search(r'_family : String := "(\w+)"', src)
        if not (nm and fam):
            continue
        name = nm.group(1)
        key = name.rstrip("'").replace("_", "")
        glyph = name2glyph.get(key)
        mark = lean2mark.get(fam.group(1))
        if glyph is None or mark is None:
            problems.append(f"{base}: cannot place '{name}' on an axis")
            continue

        tables = {
            "l8": l8nav.CL8NK_FORMULAE[mark].get(glyph),
            "l9": l9nav.CL9NK_FORMULAE[mark].get(glyph),
        }
        for layer, row in tables.items():
            if row is None:
                problems.append(f"{base}: {mark} has no {layer.upper()} row for {glyph}")

        prefix = f"the_primitive_type_called_{name}"
        if f"{prefix}_clinkFragmentL8" not in src:
            missing_record.append(base)
            continue

        checked += 1
        for field, index, layer in FIELDS:
            row = tables[layer]
            if row is None:
                continue
            want = row[index] or ""
            got = re.search(
                re.escape(f"def {prefix}_{field} : String := ") + r'"(.*?)"\n', src
            )
            if got is None:
                problems.append(f"{base}: no {field}")
            elif got.group(1) != want:
                problems.append(
                    f"{base}: {field}\n     record: {got.group(1)}\n     source: {want}"
                )
        if verbose:
            print(f"  {base:32} {mark} {glyph}  ok")

    for base in missing_record:
        problems.append(f"{base}: carries no CLINK record")

    print(f"values checked: {checked} of 49")
    if problems:
        print(f"disagreements: {len(problems)}")
        for p in problems:
            print(f"  {p}")
        return 1
    print("records agree with the navigators on every field.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

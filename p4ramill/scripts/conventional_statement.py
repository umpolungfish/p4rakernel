#!/usr/bin/env python3
"""Decompose a catalog entry into the statement a conventional mathematician reads.

This runs the direction that had never been run. Every prior decomposition in the
tree went mathematics to English to ob3ect to word to address, then read the
address back as commentary. This goes the other way: address to twelve fragments
to twelve conventional hypotheses to an assembled statement.

Nothing here holds a mark-to-meaning map. The readings come from the per-value
records in Imscribing/Primitives/Types, which are guarded against the navigators
by check_clink_records.py. The tuple comes from the catalog. The word and its
verdict come from the kernel.

L8 and L9 are read together rather than chosen between. Where both layers give
the same value the reading is settled; where L9 annotates, the annotation is the
transcendence content and is printed with it; where the layers disagree on the
value itself that is a promotion, and it is stated as a gap rather than resolved.

    python3 scripts/conventional_statement.py NAME [NAME...] [--vox] [--json]
"""

from __future__ import annotations

import glob
import io
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
P4RAMILL = os.path.dirname(HERE)
PRIMITIVES = os.path.join(P4RAMILL, "Imscribing", "Primitives")
TYPES = os.path.join(PRIMITIVES, "Types")
GRAMMAR = os.path.expanduser("~/imsgct/imscribing_grammar")
MOMONADOS = os.path.expanduser("~/imsgct/mOMonadOS")
CATALOG = os.path.join(GRAMMAR, "IG_catalog.json")

MARKS = ["⊢", "⊣", "≻", "≺", "⋈", "⊤", "∈", "∋", "⊙", "⊥", "⊞", "◻"]

sys.path.insert(0, GRAMMAR)
sys.path.insert(0, os.path.join(GRAMMAR, "navigators"))


def read(path: str) -> str:
    return io.open(path, encoding="utf-8").read()


def load_records() -> dict[tuple[str, str], dict]:
    """(mark, glyph) -> the value's record, read out of scripture."""
    from imscrbgrmr.canonical_primitives import CANONICAL_VALUES

    src = read(os.path.join(PRIMITIVES, "Imscription.lean"))
    name2glyph: dict[str, str] = {}
    axis2glyphs: dict[str, list[str]] = {}
    for m in re.finditer(r"def (\w+)\.shavian : \1 → String\n((?:\s*\|.*\n)+)", src):
        axis = m.group(1)
        axis2glyphs[axis] = []
        for line in m.group(2).splitlines():
            mm = re.match(r"\s*\|\s*\.([A-Za-z_][A-Za-z0-9_']*)\s*=>\s*\"(.+?)\"", line)
            if mm:
                name2glyph[mm.group(1).rstrip("'").replace("_", "")] = mm.group(2)
                axis2glyphs[axis].append(mm.group(2))

    lean2mark = {}
    for axis, glyphs in axis2glyphs.items():
        for mark, values in CANONICAL_VALUES.items():
            if set(glyphs) == set(values):
                lean2mark[axis] = mark

    records: dict[tuple[str, str], dict] = {}
    for path in sorted(glob.glob(os.path.join(TYPES, "PrimitiveType*.lean"))):
        s = read(path)
        nm = re.search(r"primitive value type '([^']+)'", s)
        fam = re.search(r'_family : String := "(\w+)"', s)
        if not (nm and fam):
            continue
        name = nm.group(1)
        glyph = name2glyph.get(name.rstrip("'").replace("_", ""))
        mark = lean2mark.get(fam.group(1))
        if glyph is None or mark is None:
            continue
        prefix = f"the_primitive_type_called_{name}"

        def field(f: str, default: str = "") -> str:
            m = re.search(
                re.escape(f"def {prefix}_{f} : String := ") + r'"(.*?)"\n', s
            )
            return m.group(1) if m else default

        star = re.search(
            re.escape(f"def {prefix}_fragmentIsStatement : String := ") + r'"(\w+)"', s
        )
        records[(mark, glyph)] = {
            "name": name,
            "family": fam.group(1),
            "fragmentL8": field("clinkFragmentL8"),
            "proximityL8": field("proximityL8"),
            "atomL8": field("promotedAtomL8"),
            "fragmentL9": field("clinkFragmentL9"),
            "proximityL9": field("proximityL9"),
            "atomL9": field("promotedAtomL9"),
            "reading": field("conventionalReading"),
            "isStatement": star.group(1) if star else "never",
            "isStatementEvidence": field("fragmentIsStatementEvidence"),
        }
    return records


def load_catalog() -> dict[str, dict]:
    return {e["name"]: e for e in json.load(io.open(CATALOG, encoding="utf-8"))}


def kernel(cmds: list[str], timeout: int = 900) -> str:
    """One boot, whatever was asked. Empty string if the kernel is unavailable."""
    script = os.path.join(MOMONADOS, "run_hosted_cmds.sh")
    if not os.path.exists(script):
        return ""
    try:
        r = subprocess.run(
            [script] + cmds, cwd=MOMONADOS, capture_output=True, text=True,
            timeout=timeout,
        )
    except (subprocess.TimeoutExpired, OSError):
        return ""
    return r.stdout + r.stderr


def word_and_verdict(tuple_glyphs: str) -> tuple[str, str, str]:
    """The word a tuple composes to, its vox verdict, and its banked reading."""
    out = kernel([f"imasm write {tuple_glyphs}"])
    m = re.search(r"^word:\s*(\S+)", out, re.M)
    if not m:
        return "", "", ""
    word = m.group(1)
    out2 = kernel([f"vox verdict {word}", f"banked {word}"])
    v = re.search(r"^verdict (\w+)", out2, re.M)
    b = re.search(r"^\s{2}(OK —.*|VACUOUS.*|LEAK.*)$", out2, re.M)
    return word, (v.group(1) if v else ""), (b.group(1).strip() if b else "")


def decompose(name: str, records, catalog, want_vox: bool) -> dict:
    entry = catalog.get(name)
    if entry is None:
        return {"name": name, "error": "not in catalog"}
    glyphs = [entry[m] for m in MARKS]
    tup = "".join(glyphs)

    marks = []
    for mark, glyph in zip(MARKS, glyphs):
        rec = records.get((mark, glyph))
        if rec is None:
            marks.append({"mark": mark, "glyph": glyph, "error": "no record"})
            continue
        lateral = ""
        if rec["fragmentL9"] != rec["fragmentL8"] and "—" in rec["fragmentL9"]:
            lateral = rec["fragmentL9"].split("—", 1)[1].strip()
        marks.append(
            {
                "mark": mark,
                "glyph": glyph,
                "value": rec["name"],
                "reading": rec["reading"],
                "fragment": rec["fragmentL8"],
                "isStatement": rec["isStatement"],
                "isStatementEvidence": rec["isStatementEvidence"],
                "lateral": lateral,
                "atomL8": rec["atomL8"],
                "atomL9": rec["atomL9"],
                "settled": rec["proximityL8"] == rec["proximityL9"],
            }
        )

    out = {
        "name": name,
        "description": entry.get("description", ""),
        "tuple": tup,
        "marks": marks,
    }
    if want_vox:
        word, verdict, banked = word_and_verdict(tup)
        out["word"] = word
        out["vox"] = verdict
        out["banked"] = banked
    return out


def render(d: dict) -> str:
    if "error" in d:
        return f"## {d['name']}\n\n  {d['error']}\n"
    lines = [f"## {d['description'] or d['name']}  ⟨{d['tuple']}⟩", ""]
    for m in d["marks"]:
        if "error" in m:
            lines.append(f"    {m['mark']} {m['glyph']}   [{m['error']}]")
            continue
        star = {"always": "★ ", "contextual": "☆ "}.get(m["isStatement"], "  ")
        lines.append(f"{star}  {m['mark']} {m['glyph']}   {m['reading']}")
        if m["lateral"]:
            lines.append(f"        L9: {m['lateral']}")
    starred = [m for m in d["marks"] if m.get("isStatement") == "always"]
    maybe = [m for m in d["marks"] if m.get("isStatement") == "contextual"]
    if starred:
        lines += ["", "**The fragments that are the statement.**"]
        for m in starred:
            lines.append(f"    {m['mark']} {m['glyph']}   {m['fragment']}")
    if maybe:
        lines += ["", "**Contextual — the statement in some domains, not in others.**"]
        for m in maybe:
            lines.append(f"    {m['mark']} {m['glyph']}   {m['fragment']}")
            lines.append(f"        {m['isStatementEvidence']}")
    if d.get("vox"):
        lines += [
            "",
            f"    word {d['word']}",
            f"    vox {d['vox']}   {d['banked']}",
        ]
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    want_vox = "--vox" in sys.argv
    as_json = "--json" in sys.argv
    if not args:
        print(__doc__.strip().splitlines()[-1].strip())
        return 1

    records = load_records()
    catalog = load_catalog()
    results = [decompose(n, records, catalog, want_vox) for n in args]
    if as_json:
        json.dump(results, sys.stdout, ensure_ascii=False, indent=1)
        print()
    else:
        for d in results:
            print(render(d))
    return 0 if all("error" not in d for d in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Regression: the generated decomposition against the seven written by hand.

ig-docs/OVMs/conventional_statements.md states the seven Millennium theorems as
conventional mathematics, one hypothesis per mark, with ★ on the fragments that
ARE the statement rather than a picture of it. That document was written by hand
before any generator existed, so it is the fixture: a generator that reproduces
it has run the decomposition in the direction nothing in the tree had run.

The comparison is deliberately not equality of star sets, because the stars are
not all the same kind of fact. Of the eight starred values, seven are starred in
every sampled theorem that carries them. One, ⊡ 𐑭, is starred in three of the
five that carry it: the integer winding is the statement for Riemann (the
argument principle), Birch and Swinnerton-Dyer (the regulator) and Hodge (the
first Chern class), and is not the statement for Navier-Stokes or P versus NP.
That is a domain fact the coordinate does not carry, so the record grades it
"contextual" and the generator flags it ☆ rather than asserting it either way.

Two conditions, and both must hold for every section:

  covered — every ★ in the document is flagged by the generator, as ★ or ☆.
            A hand star the generator does not see at all is a miss.
  sound   — every ★ the generator asserts is starred in the document.
            An unconditional claim the document does not support is an overreach.

    python3 scripts/check_conventional_seven.py [--verbose]
"""

from __future__ import annotations

import io
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
P4RAMILL = os.path.dirname(HERE)
FIXTURE = os.path.expanduser("~/imsgct/ig-docs/OVMs/conventional_statements.md")
GENERATOR = os.path.join(HERE, "conventional_statement.py")

SEVEN = [
    "riemann_theorem",
    "birch_and_swinnerton_dyer_theorem_",
    "yang–mills_existence_and_mass_gap_theorem_",
    "navier_stokes_theorem",
    "p_versus_np_theorem",
    "hodge_lefschetz_11_theorem",
    "collatz_theorem_proven",
]


def hand_written() -> dict[tuple[str, str], set[tuple[str, str]]]:
    """(title, tuple) -> the ★ marks the document carries for it."""
    out: dict[tuple[str, str], set[tuple[str, str]]] = {}
    cur = None
    for line in io.open(FIXTURE, encoding="utf-8"):
        head = re.match(r"^##\s+(.+?)\s\s+⟨(\S+)⟩", line)
        if head:
            cur = (head.group(1).strip(), head.group(2))
            out[cur] = set()
            continue
        star = re.match(r"\s*★\s+(\S+)\s+(\S+)\s", line)
        if star and cur:
            out[cur].add((star.group(1), star.group(2)))
    return out


def generated() -> dict[str, dict]:
    r = subprocess.run(
        [sys.executable, GENERATOR, *SEVEN, "--json"],
        capture_output=True, text=True, cwd=P4RAMILL,
    )
    if r.returncode != 0 and not r.stdout.strip():
        print(r.stderr.strip())
        return {}
    return {g["tuple"]: g for g in json.loads(r.stdout)}


def main() -> int:
    verbose = "--verbose" in sys.argv
    hand = hand_written()
    gen = generated()
    if not gen:
        print("the generator produced nothing")
        return 1
    if not hand:
        print(f"no sections parsed from {FIXTURE}")
        return 1

    failures = 0
    for (title, tup), stars in hand.items():
        g = gen.get(tup)
        if g is None:
            print(f"  {title:34} tuple {tup} was not generated")
            failures += 1
            continue
        always = {
            (m["mark"], m["glyph"])
            for m in g["marks"] if m.get("isStatement") == "always"
        }
        ctx = {
            (m["mark"], m["glyph"])
            for m in g["marks"] if m.get("isStatement") == "contextual"
        }
        missed = stars - (always | ctx)
        over = always - stars
        good = not missed and not over
        failures += not good
        note = f"  ☆ {sorted(g_ for g_ in ctx)}" if (ctx and verbose) else ""
        print(
            f"  {title:34} hand ★{len(stars)}   generated ★{len(always)} ☆{len(ctx)}"
            f"   {'ok' if good else 'FAIL'}{note}"
        )
        if missed:
            print(f"      not flagged at all: {sorted(missed)}")
        if over:
            print(f"      asserted without support: {sorted(over)}")

    print(f"\nsections: {len(hand)}   failing: {failures}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())

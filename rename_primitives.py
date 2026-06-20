#!/usr/bin/env python3
"""
Rename IG primitive constructor names in p4rakernel to canonical Shavian glyph names.

Each old name is replaced with its SNS_PRIME.md Shavian letter-name, using the
ordinal position from the idx_* functions in Core.lean as the mapping key.

Run dry-run first:   python3 rename_primitives.py --dry-run
Apply:               python3 rename_primitives.py
"""
import re, sys, os
from pathlib import Path

# (old, new) — longer/more-specific strings listed before any prefix they share
RENAMES = [
    # Ð Dimensionality (F4): dead ash array if'
    ('D_wedge',         'dead'),
    ('D_triangle',      'ash'),
    ('D_infty',         'array'),
    ('D_odot',          "if'"),
    # Þ Topology (F5): judge eat mime oil are
    ('T_network',       'judge'),
    ('T_in',            'eat'),
    ('T_bowtie',        'mime'),
    ('T_box',           'oil'),
    ('T_odot',          'are'),
    # Ř Relational/Coupling (F4): ado tot ear ian
    ('R_super',         'ado'),
    ('R_cat',           'tot'),
    ('R_dagger',        'ear'),
    ('R_lr',            'ian'),
    # Φ Parity/Polarity (F5): church yew out nun or'  (P_pm_sym before P_pm)
    ('P_pm_sym',        "or'"),
    ('P_asym',          'church'),
    ('P_psi',           'yew'),
    ('P_pm',            'out'),
    ('P_sym',           'nun'),
    # ⊙ Criticality (F5): woe monad roar err haha  (Phi_c_complex before Phi_c)
    ('Phi_c_complex',   'roar'),
    ('Phi_sub',         'woe'),
    ('Phi_c',           'monad'),
    ('Phi_EP',          'err'),
    ('Phi_super',       'haha'),
    # Ç Kinetics (F5): yea loll egg on air
    ('K_fast',          'yea'),
    ('K_mod',           'loll'),
    ('K_slow',          'egg'),
    ('K_trap',          'on'),
    ('K_MBL',           'air'),
    # ƒ Fidelity (F3): age they peep
    ('F_ell',           'age'),
    ('F_eth',           'they'),
    ('F_hbar',          'peep'),
    # Γ Granularity (F3): bib thigh ice
    ('G_beth',          'bib'),
    ('G_gimel',         'thigh'),
    ('G_aleph',         'ice'),
    # ɢ Grammar/Coupling (F4): vow gag measure ooze
    ('Gamma_and',       'vow'),
    ('Gamma_or',        'gag'),
    ('Gamma_seq',       'measure'),
    ('Gamma_broad',     'ooze'),
    # Ħ Chirality (F4): fee kick sure wool  (H_inf before H0/H1/H2)
    ('H_inf',           'wool'),
    ('H0',              'fee'),
    ('H1',              'kick'),
    ('H2',              'sure'),
    # Ω Protection/Winding (F4): awe oak ah zoo  (Omega_Z2 before Omega_Z)
    ('Omega_Z2',        'oak'),
    ('Omega_0',         'awe'),
    ('Omega_Z',         'ah'),
    ('Omega_NA',        'zoo'),
    # Σ Stoichiometry (F3): hung so up
    ('one_one',         'hung'),
    ('n_n',             'so'),
    ('n_m',             'up'),
]

EXTS = {'.lean', '.py'}

# Directories to skip entirely (external packages, caches, venvs)
SKIP_DIRS = {'.lake', '.venv', '__pycache__', '.git', 'node_modules', 'src', 'tests'}

def rename_in_text(text: str) -> tuple[str, list[tuple[str,str,int]]]:
    changes = []
    for old, new in RENAMES:
        pattern = r'\b' + re.escape(old) + r'\b'
        def replacer(m, _old=old, _new=new):
            changes.append((_old, _new, m.start()))
            return _new
        text = re.sub(pattern, replacer, text)
    return text, changes

def process(root: Path, dry: bool):
    total_files = 0
    total_changes = 0
    for path in sorted(root.rglob('*')):
        # Skip any path that has a skip-dir component
        if any(part in SKIP_DIRS for part in path.parts):
            continue
        if path.suffix not in EXTS:
            continue
        if path.name == 'rename_primitives.py':
            continue
        try:
            original = path.read_text(encoding='utf-8')
        except Exception:
            continue
        updated, changes = rename_in_text(original)
        if not changes:
            continue
        total_files += 1
        total_changes += len(changes)
        rel = path.relative_to(root)
        print(f"\n{'[DRY]' if dry else '[EDIT]'} {rel}  ({len(changes)} changes)")
        # show unique substitutions made in this file
        seen = {}
        for old, new, _ in changes:
            seen.setdefault(old, 0)
            seen[old] += 1
        for old, count in sorted(seen.items()):
            new = dict(RENAMES)[old]
            print(f"    {old:20s} -> {new}  ({count}x)")
        if not dry:
            path.write_text(updated, encoding='utf-8')
    print(f"\n{'DRY RUN' if dry else 'DONE'}: {total_changes} substitutions across {total_files} files.")

if __name__ == '__main__':
    dry = '--dry-run' in sys.argv
    root = Path(__file__).parent
    process(root, dry)

#!/usr/bin/env python3
"""Append the ConventionalExpr register to every auto-generated ob3ect scaffold.

For each file in Imscribing/Ob3ects/*.lean carrying the
"-- IGProtocol scaffold: OP → OP → ..." header:
  1. extract the opcode word and the stage prefix (<prefix>_s0 ...),
  2. inject `import Imscribing.ConventionalRegister`,
  3. append a register section mapping each opcode to its conventional
     expression plus a conventional fixed-point protocol and its theorems.

Idempotent: files already carrying `_conventional_register` are skipped.
Files without the scaffold header (hand-written ob3ects) are skipped.
"""
import os, re, sys

DIR = os.path.join(os.path.dirname(__file__), '..', 'Imscribing', 'Ob3ects')

GLYPH = {
    'VINIT': '⊢', 'TANCH': '⊣', 'AFWD': '≻', 'AREV': '≺', 'CLINK': '⋈',
    'EVALT': '⊤', 'EVALF': '⊥', 'FSPLIT': '∈', 'FFUSE': '∋',
    'IMSCRIB': '⊙', 'ENGAGR': '⊞', 'IFIX': '⊡',
}


def valid_ident(s):
    return re.match(r'^[A-Za-z][A-Za-z0-9_]*$', s) is not None

def idbase_of(prefix, stem):
    if valid_ident(prefix):
        return prefix
    return 'ob_' + re.sub(r'[^A-Za-z0-9_]', '_', stem).strip('_')

HEADER_RE = re.compile(r'IGProtocol scaffold:\s*(.*)')
CLASS_RE = re.compile(r'Class:\s*(.*)')
PREFIX_RE = re.compile(r'private def (\w+)_s0 : Imscription :=')

def parse(fn, text):
    m = HEADER_RE.search(text)
    if not m:
        return None
    ops = [t.strip() for t in m.group(1).split('→') if t.strip()]
    if not ops:
        return None
    # stage prefix from the ground imscription
    pm = PREFIX_RE.search(text)
    prefix = pm.group(1) if pm else None
    cm = CLASS_RE.search(text)
    cls = cm.group(1).strip() if cm else fn.replace('_scaffold.lean', '')
    glyph_word = ''.join(GLYPH.get(o, '?') for o in ops)
    stem = fn.replace('_scaffold.lean', '').replace('.lean', '')
    return {'ops': ops, 'prefix': prefix, 'cls': cls, 'glyph_word': glyph_word,
            'idbase': idbase_of(prefix if prefix else stem, stem)}

def build_section(d):
    prefix, ops = d['prefix'], d['ops']
    n = len(ops)
    stage = f'{prefix}_s0'
    idb = d['idbase']
    stage_ok = valid_ident(stage)
    op_lit = ', '.join(f'"{o}"' for o in ops)
    lines = []
    lines.append('')
    lines.append('-- ─────────────────────────────────────────────────────────────────────────────')
    lines.append(f"-- Conventional-expression register (Class: {d['cls']})")
    lines.append(f"--   Word: {d['glyph_word']}")
    lines.append('-- ─────────────────────────────────────────────────────────────────────────────')
    lines.append('')
    lines.append(f'def {idb}_opcodes : List String := [{op_lit}]')
    lines.append('')
    lines.append(f'def {idb}_conventional_register : List ConventionalExpr :=')
    lines.append(f'  conventionalRegisterOf {idb}_opcodes')
    lines.append('')
    lines.append(f'def {idb}_glyph_word : String := glyphWordOf {idb}_opcodes')
    lines.append('')
    lines.append(f'/-- The register has exactly one entry per opcode. -/')
    lines.append(f'theorem {idb}_register_length : {idb}_conventional_register.length = {n} := by')
    lines.append('  native_decide')
    lines.append('')
    lines.append(f'/-- The register\'s opcode column reproduces the glyph word exactly. -/')
    lines.append(f'theorem {idb}_register_matches_word : {idb}_glyph_word = "{d["glyph_word"]}" := by')
    lines.append('  native_decide')
    lines.append('')
    if stage_ok:
        lines.append(f'/-- The conventional protocol: a fixed-point walk over the ground imscription,')
        lines.append('    each arrow annotated by its conventional expression. -/')
        lines.append(f'def {idb}_conventional_protocol : IGProtocol {stage} {stage} :=')
        lines.append('  .withGram Grammar.measure <|')
        lines.append('  .withMem wool <|')
        # linear chain: n arrows, n-1 seqs, n-1 closing parens
        for i, o in enumerate(ops):
            if i < n - 1:
                lines.append(f'  (.seq (.arrow {stage} {stage} {stage})  -- {o}')
            else:
                lines.append(f'  (.arrow {stage} {stage} {stage})' + ')' * (n - 1) + f'  -- {o}')
        lines.append('')
        lines.append(f'/-- The conventional protocol carries all {n} arrows. -/')
        lines.append(f'theorem {idb}_conventional_protocol_depth : {idb}_conventional_protocol.depth = {n} := by')
        lines.append('  native_decide')
        lines.append('')
    else:
        lines.append('-- protocol omitted: ground stage identifier is not a valid Lean identifier')
        lines.append('')
    return '\n'.join(lines)

def transform(fn, text):
    d = parse(fn, text)
    if d is None:
        return None, 'skip:no-header'
    if '_conventional_register' in text:
        return None, 'skip:already'
    if d['prefix'] is None:
        return None, 'skip:no-prefix'
    # inject import
    if 'import Imscribing.ConventionalRegister' not in text:
        # after the last import line
        lines = text.split('\n')
        last_import = max(i for i, l in enumerate(lines) if l.startswith('import '))
        lines.insert(last_import + 1, 'import Imscribing.ConventionalRegister')
        text = '\n'.join(lines)
    section = build_section(d)
    # place before `end Imscribing` if present, else append
    if text.rstrip().endswith('end Imscribing'):
        idx = text.rfind('end Imscribing')
        text = text[:idx] + section + '\n' + text[idx:]
    else:
        text = text.rstrip() + '\n' + section + '\n'
    return text, 'transformed'

def main():
    dry = '--dry-run' in sys.argv
    files = sorted(f for f in os.listdir(DIR) if f.endswith('.lean'))
    stats = {'transformed': 0, 'skip:no-header': 0, 'skip:already': 0,
             'skip:no-prefix': 0}
    for fn in files:
        p = os.path.join(DIR, fn)
        text = open(p, encoding='utf-8').read()
        new, status = transform(fn, text)
        stats[status] = stats.get(status, 0) + 1
        if dry and status == 'transformed':
            d = parse(fn, text)
            print(f'===== {fn} ({d["cls"]}) n={len(d["ops"])} prefix={d["prefix"]}')
            print(build_section(d))
            print()
        elif not dry and status == 'transformed':
            open(p, 'w', encoding='utf-8').write(new)
    print('STATS', stats)

if __name__ == '__main__':
    main()

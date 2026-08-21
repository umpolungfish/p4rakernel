"""What moves item 1's crystal address, measured over our own derived words.

Every word here was run through
  /home/mrnob0dy666/imsgct/mOMonadOS/run_hosted_cmds.sh 'imasm derive <word>'
and the tuple read off.  Nothing is asserted that was not derived.

Result: fourteen variants, TWO addresses, and the only discriminator is whether the
word carries the full Belnap triple ⊤ (EVALT), ⊥ (EVALF) and ⊞ (ENGAGR, the B state).

  all three present -> ⋈ = 𐑐 (3), ⊙ = 𐑻 (2.67)   crystal 16404190
  any one missing   -> ⋈ = 𐑞 (2), ⊙ = 𐑣 (3)      crystal 16389838

Order is irrelevant, multiplicity is irrelevant, and ≻ ≺ ◻ ⊢ ⊣ are irrelevant --
including dropping ⊙ itself.  So item 1's address is not an artefact of how the ask is
phrased: it is the object holding T, F and B at once, which is what reads as criticality
𐑻, the exceptional point, rather than ⊙ the fixed point.
"""

DERIVED = [
    # word,                          tuple,                        crystal
    ("⊢⊙∈≻⊤≺⊥∋⋈⊞◻⊣",   "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),  # item 1'
    ("⊢⊙∈⊞⊤⊥≺∋⋈◻⊣",     "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),  # mod-9 holder-first
    ("⊢⊙∈⊞⊤⊥⋈≻≺∋◻⊣",   "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),  # collatzcombo, repaired
    ("⊢⊙∈⊤⊥≺∋⋈⊞◻⊣",     "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),
    ("⊢⊙∈⊤≺⊥∋⋈≻⊞◻⊣",   "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),
    ("⊢⊙∈≻⊤⊥≺∋⋈⊞◻⊣",   "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),
    ("⊢⊙∈⊞⊤⊥⋈⋈≻≺∋◻⊣", "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),  # ⋈ doubled
    ("⊢⊙⊙∈⊞⊤⊥⋈≻≺∋◻⊣", "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),  # ⊙ doubled
    ("⊢∈⊞⊤⊥⋈≻≺∋◻⊣",     "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),  # ⊙ dropped
    ("⊢⊙∈⊞⊤⊥≺∋⋈◻◻⊣",   "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),  # ◻ doubled
    ("⊢⊙∈∈⊞⊤⊥≺∋∋⋈◻⊣", "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),  # ∈∋ doubled
    ("⊢⊙∈⊞⊤⊤⊥⊥≺∋⋈◻⊣", "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),  # ⊤⊥ doubled
    ("⊢⊙∈⊞⊤⊥⋈≻∋◻⊣",     "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),  # ≺ dropped
    ("⊢⊙∈⊞⊤⊥⋈≺∋◻⊣",     "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),  # ≻ dropped
    ("⊢⊙∈⊞⊤⊥⋈≻≺∋⊣",     "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),  # ◻ dropped
    ("⊙∈⊞⊤⊥⋈≻≺∋◻⊣",     "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),  # ⊢ dropped
    ("⊢⊙∈⊞⊤⊥⋈≻≺∋◻",     "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),  # ⊣ dropped
    # the two addresses part exactly here:
    ("⊢⊙∈⊞⊤⋈≻≺∋◻⊣",     "𐑦𐑶𐑾𐑹𐑞𐑘𐑔𐑠𐑣𐑫𐑳𐑭", 16389838),  # ⊥ dropped
    ("⊢⊙∈⊞⊥⋈≻≺∋◻⊣",     "𐑦𐑶𐑾𐑹𐑞𐑘𐑔𐑠𐑣𐑫𐑳𐑭", 16389838),  # ⊤ dropped
    ("⊢⊙∈⊤⊥⋈≻≺∋◻⊣",     "𐑦𐑶𐑾𐑹𐑞𐑘𐑔𐑠𐑣𐑫𐑳𐑭", 16389838),  # ⊞ dropped
    ("⊢⊙∈⊤⋈∋◻⊞≺⋈⊣",     "𐑦𐑶𐑾𐑹𐑞𐑘𐑔𐑠𐑣𐑫𐑳𐑭", 16389838),  # the kernel's wound word
]

TRIPLE = ("⊤", "⊥", "⊞")

if __name__ == "__main__":
    print(f"{'word':<28} {'⋈':>3} {'⊙':>3} {'crystal':>10}  full ⊤⊥⊞?")
    for w, t, c in DERIVED:
        full = all(g in w for g in TRIPLE)
        print(f"{w:<28} {t[4]:>3} {t[8]:>3} {c:>10}  {full}")
    bad = [(w, t, c) for w, t, c in DERIVED
           if (all(g in w for g in TRIPLE)) != (c == 16404190)]
    print(f"\ncounterexamples to 'full triple <-> 16404190': {len(bad)}")

"""What moves item 1's crystal address, measured over our own derived words.

Every word here was run through
  /home/mrnob0dy666/imsgct/mOMonadOS/run_hosted_cmds.sh 'imasm derive <word>'
and the tuple read off.  Nothing is asserted that was not derived.

TWO INDEPENDENT LEVERS, four addresses.

1. The Belnap triple.  Whether the word carries ⊤ (EVALT) and ⊥ (EVALF) and ⊞ (ENGAGR,
   the B state) together moves Fidelity ⋈ and Criticality ⊙:

     all three present   ⋈ = 𐑐 (3), ⊙ = 𐑻 (2.67)
     any one missing     ⋈ = 𐑞 (2), ⊙ = 𐑣 (3)

   Nothing else touches these two slots.  Reordering at a FIXED CUT does nothing,
   multiplicity does nothing -- ⋈, ⊙, ◻, ∈∋, ⊤⊥ all doubled, no change -- and dropping
   ≻, ≺, ◻, ⊢, ⊣, or ⊙ itself does nothing.

2. ROTAT.  The address is NOT rotation-invariant, and the first version of this file
   said it was.  That claim came from deriving every variant cut at ⊢, which measures
   the cut and not the word -- the ring rule, exactly.  Cycled, item 1'
   ⊢⊙∈≻⊤≺⊥∋⋈⊞◻⊣ splits 7/5 over its twelve rotations:

     k = 0,1,2 and 8..11   ≻ = 𐑾, ≺ = 𐑹, ◻ = 𐑭     crystal 16404190
     k = 3..7              ≻ = 𐑽, ≺ = 𐑯, ◻ = 𐑴     crystal 16144989

   and ⊢⊙∈⊞⊤⋈≻≺∋◻⊣ splits the same way, 16389838 against 16130637, the same three
   slots taking the same two values.  The phase flips exactly when the cut falls INSIDE
   the evaluation region ≻⊤≺⊥∋.

Invariant across the whole orbit and both levers: ⊢ 𐑦, ⊣ 𐑶, ⊤ 𐑘, ∈ 𐑔, ∋ 𐑠, ⊥ 𐑫, ⊞ 𐑳.

So item 1's exceptional-point criticality is not an artefact of phrasing -- the ∃k is
not what puts it there, since dropping ≻ and ≺ at a fixed cut leaves ⊙ alone -- but the
address as a whole is phase-bearing, and any reading of it has to say which cut it was
taken at.

The table below is the FIXED-CUT family, all cut at ⊢; ROTAT_ORBIT holds the cycled
readouts.
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

# The cycled readouts: word, tuple, crystal, for every rotation of two words.
ROTAT_ORBIT = [
    ("⊢⊙∈≻⊤≺⊥∋⋈⊞◻⊣", "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),
    ("⊙∈≻⊤≺⊥∋⋈⊞◻⊣⊢", "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),
    ("∈≻⊤≺⊥∋⋈⊞◻⊣⊢⊙", "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),
    ("≻⊤≺⊥∋⋈⊞◻⊣⊢⊙∈", "𐑦𐑶𐑽𐑯𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑴", 16144989),
    ("⊤≺⊥∋⋈⊞◻⊣⊢⊙∈≻", "𐑦𐑶𐑽𐑯𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑴", 16144989),
    ("≺⊥∋⋈⊞◻⊣⊢⊙∈≻⊤", "𐑦𐑶𐑽𐑯𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑴", 16144989),
    ("⊥∋⋈⊞◻⊣⊢⊙∈≻⊤≺", "𐑦𐑶𐑽𐑯𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑴", 16144989),
    ("∋⋈⊞◻⊣⊢⊙∈≻⊤≺⊥", "𐑦𐑶𐑽𐑯𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑴", 16144989),
    ("⋈⊞◻⊣⊢⊙∈≻⊤≺⊥∋", "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),
    ("⊞◻⊣⊢⊙∈≻⊤≺⊥∋⋈", "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),
    ("◻⊣⊢⊙∈≻⊤≺⊥∋⋈⊞", "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),
    ("⊣⊢⊙∈≻⊤≺⊥∋⋈⊞◻", "𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭", 16404190),
    ("⊢⊙∈⊞⊤⋈≻≺∋◻⊣", "𐑦𐑶𐑾𐑹𐑞𐑘𐑔𐑠𐑣𐑫𐑳𐑭", 16389838),
    ("⊙∈⊞⊤⋈≻≺∋◻⊣⊢", "𐑦𐑶𐑾𐑹𐑞𐑘𐑔𐑠𐑣𐑫𐑳𐑭", 16389838),
    ("∈⊞⊤⋈≻≺∋◻⊣⊢⊙", "𐑦𐑶𐑾𐑹𐑞𐑘𐑔𐑠𐑣𐑫𐑳𐑭", 16389838),
    ("⊞⊤⋈≻≺∋◻⊣⊢⊙∈", "𐑦𐑶𐑽𐑯𐑞𐑘𐑔𐑠𐑣𐑫𐑳𐑴", 16130637),
    ("⊤⋈≻≺∋◻⊣⊢⊙∈⊞", "𐑦𐑶𐑽𐑯𐑞𐑘𐑔𐑠𐑣𐑫𐑳𐑴", 16130637),
    ("⋈≻≺∋◻⊣⊢⊙∈⊞⊤", "𐑦𐑶𐑽𐑯𐑞𐑘𐑔𐑠𐑣𐑫𐑳𐑴", 16130637),
    ("≻≺∋◻⊣⊢⊙∈⊞⊤⋈", "𐑦𐑶𐑽𐑯𐑞𐑘𐑔𐑠𐑣𐑫𐑳𐑴", 16130637),
    ("≺∋◻⊣⊢⊙∈⊞⊤⋈≻", "𐑦𐑶𐑽𐑯𐑞𐑘𐑔𐑠𐑣𐑫𐑳𐑴", 16130637),
    ("∋◻⊣⊢⊙∈⊞⊤⋈≻≺", "𐑦𐑶𐑽𐑯𐑞𐑘𐑔𐑠𐑣𐑫𐑳𐑴", 16130637),
    ("◻⊣⊢⊙∈⊞⊤⋈≻≺∋", "𐑦𐑶𐑾𐑹𐑞𐑘𐑔𐑠𐑣𐑫𐑳𐑭", 16389838),
    ("⊣⊢⊙∈⊞⊤⋈≻≺∋◻", "𐑦𐑶𐑾𐑹𐑞𐑘𐑔𐑠𐑣𐑫𐑳𐑭", 16389838),
]

TRIPLE = ("⊤", "⊥", "⊞")

if __name__ == "__main__":
    print(f"{'word':<28} {'⋈':>3} {'⊙':>3} {'crystal':>10}  full ⊤⊥⊞?")
    for w, t, c in DERIVED:
        full = all(g in w for g in TRIPLE)
        print(f"{w:<28} {t[4]:>3} {t[8]:>3} {c:>10}  {full}")
    bad = [(w, t, c) for w, t, c in DERIVED
           if (all(g in w for g in TRIPLE)) != (c == 16404190)]
    print(f"\nfixed cut at ⊢: counterexamples to 'full triple <-> 16404190': {len(bad)}")

    print("\nROTAT orbit — the address is PHASE-BEARING:")
    print(f"  {'rotation':<28} {'≻':>3} {'≺':>3} {'◻':>3} {'crystal':>10}")
    for w, t, c in ROTAT_ORBIT:
        print(f"  {w:<28} {t[2]:>3} {t[3]:>3} {t[11]:>3} {c:>10}")
    addrs = sorted({c for _, _, c in ROTAT_ORBIT})
    print(f"\n  distinct addresses over the orbit: {len(addrs)}  {addrs}")
    inv = [i for i in range(12)
           if len({t[i] for _, t, _ in ROTAT_ORBIT if len(t) == 12}) == 1]
    print(f"  slots invariant across the whole orbit: {inv}")

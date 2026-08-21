"""What moves item 1's crystal address, measured over our own derived words.

Every word here was run through
  /home/mrnob0dy666/imsgct/mOMonadOS/run_hosted_cmds.sh 'imasm derive <word>'
and the tuple read off.  Nothing is asserted that was not derived.  Re-derived
2026-08-21 after Dimensionality ⊢ and Topology ⊣ were given the R2 fields they are
named for (mOMonadOS b683fe9), which moved ⊢ 𐑦 -> 𐑛 on every word carrying one
FSPLIT/FFUSE pair.

TWO INDEPENDENT LEVERS, four addresses.

1. The Belnap triple.  Whether the word carries ⊤ (EVALT) and ⊥ (EVALF) and ⊞ (ENGAGR,
   the B state) together moves Fidelity ⋈ and Criticality ⊙:

     all three present   ⋈ = 𐑐 (3), ⊙ = 𐑻 (2.67)
     any one missing     ⋈ = 𐑞 (2), ⊙ = 𐑣 (3)

   Nothing else touches these two slots.  Reordering at a FIXED CUT does nothing,
   and dropping ≻, ≺, ◻, ⊢, ⊣, or ⊙ itself does nothing.  Multiplicity does nothing
   at ⋈, ⊙, ◻ and ⊤⊥ -- but see lever 3, which ∈∋ doubled now moves.

2. ROTAT.  The address is NOT rotation-invariant, and the first version of this file
   said it was.  That claim came from deriving every variant cut at ⊢, which measures
   the cut and not the word -- the ring rule, exactly.  Cycled, item 1'
   ⊢⊙∈≻⊤≺⊥∋⋈⊞◻⊣ splits 7/5 over its twelve rotations:

     k = 0,1,2 and 8..11   ≻ = 𐑾, ≺ = 𐑹, ◻ = 𐑭     crystal 3442270
     k = 3..7              ≻ = 𐑽, ≺ = 𐑯, ◻ = 𐑴     crystal 3183069

   and ⊢⊙∈⊞⊤⋈≻≺∋◻⊣ splits the same way, 3427918 against 3168717, the same three
   slots taking the same two values.  The phase flips exactly when the cut falls INSIDE
   the evaluation region ≻⊤≺⊥∋.

3. The FORK COUNT.  Dimensionality ⊢ reads `atomic_reentry` -- exactly one FSPLIT and
   one FFUSE, a point-like fork -- so every word here takes ⊢ 𐑛 except ⊢⊙∈∈⊞⊤⊥≺∋∋⋈◻⊣,
   which carries two pairs and keeps ⊢ 𐑦.  It is the one place multiplicity moves the
   address, and it is why ∈∋ doubled is not in the "does nothing" list above.

Invariant across the whole orbit and both levers: ⊢ 𐑛, ⊣ 𐑶, ⊤ 𐑘, ∈ 𐑲, ∋ 𐑠, ⊥ 𐑫, ⊞ 𐑳.

So item 1's exceptional-point criticality is not an artefact of phrasing -- the ∃k is
not what puts it there, since dropping ≻ and ≺ at a fixed cut leaves ⊙ alone -- but the
address as a whole is phase-bearing, and any reading of it has to say which cut it was
taken at.

The table below is the FIXED-CUT family, all cut at ⊢; ROTAT_ORBIT holds the cycled
readouts.
"""

DERIVED = [
    # word,                          tuple,                        crystal
    ("⊢⊙∈≻⊤≺⊥∋⋈⊞◻⊣", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),  # item 1'
    ("⊢⊙∈⊞⊤⊥≺∋⋈◻⊣", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),  # mod-9 holder-first
    ("⊢⊙∈⊞⊤⊥⋈≻≺∋◻⊣", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),  # collatzcombo, repaired
    ("⊢⊙∈⊤⊥≺∋⋈⊞◻⊣", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),
    ("⊢⊙∈⊤≺⊥∋⋈≻⊞◻⊣", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),
    ("⊢⊙∈≻⊤⊥≺∋⋈⊞◻⊣", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),
    ("⊢⊙∈⊞⊤⊥⋈⋈≻≺∋◻⊣", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),  # ⋈ doubled
    ("⊢⊙⊙∈⊞⊤⊥⋈≻≺∋◻⊣", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),  # ⊙ doubled
    ("⊢∈⊞⊤⊥⋈≻≺∋◻⊣", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),  # ⊙ dropped
    ("⊢⊙∈⊞⊤⊥≺∋⋈◻◻⊣", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),  # ◻ doubled
    ("⊢⊙∈∈⊞⊤⊥≺∋∋⋈◻⊣", "𐑦𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 16402270),  # ∈∋ doubled
    ("⊢⊙∈⊞⊤⊤⊥⊥≺∋⋈◻⊣", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),  # ⊤⊥ doubled
    ("⊢⊙∈⊞⊤⊥⋈≻∋◻⊣", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),  # ≺ dropped
    ("⊢⊙∈⊞⊤⊥⋈≺∋◻⊣", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),  # ≻ dropped
    ("⊢⊙∈⊞⊤⊥⋈≻≺∋⊣", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),  # ◻ dropped
    ("⊙∈⊞⊤⊥⋈≻≺∋◻⊣", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),  # ⊢ dropped
    ("⊢⊙∈⊞⊤⊥⋈≻≺∋◻", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),  # ⊣ dropped
    # the two addresses part exactly here:
    ("⊢⊙∈⊞⊤⋈≻≺∋◻⊣", "𐑛𐑶𐑾𐑹𐑞𐑘𐑲𐑠𐑣𐑫𐑳𐑭", 3427918),  # ⊥ dropped
    ("⊢⊙∈⊞⊥⋈≻≺∋◻⊣", "𐑛𐑶𐑾𐑹𐑞𐑘𐑲𐑠𐑣𐑫𐑳𐑭", 3427918),  # ⊤ dropped
    ("⊢⊙∈⊤⊥⋈≻≺∋◻⊣", "𐑛𐑶𐑾𐑹𐑞𐑘𐑲𐑠𐑣𐑫𐑳𐑭", 3427918),  # ⊞ dropped
    ("⊢⊙∈⊤⋈∋◻⊞≺⋈⊣", "𐑛𐑶𐑾𐑹𐑞𐑘𐑲𐑠𐑣𐑫𐑳𐑭", 3427918),  # the kernel's wound word
]

# The cycled readouts: word, tuple, crystal, for every rotation of two words.
ROTAT_ORBIT = [
    ("⊢⊙∈≻⊤≺⊥∋⋈⊞◻⊣", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),
    ("⊙∈≻⊤≺⊥∋⋈⊞◻⊣⊢", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),
    ("∈≻⊤≺⊥∋⋈⊞◻⊣⊢⊙", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),
    ("≻⊤≺⊥∋⋈⊞◻⊣⊢⊙∈", "𐑛𐑶𐑽𐑯𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑴", 3183069),
    ("⊤≺⊥∋⋈⊞◻⊣⊢⊙∈≻", "𐑛𐑶𐑽𐑯𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑴", 3183069),
    ("≺⊥∋⋈⊞◻⊣⊢⊙∈≻⊤", "𐑛𐑶𐑽𐑯𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑴", 3183069),
    ("⊥∋⋈⊞◻⊣⊢⊙∈≻⊤≺", "𐑛𐑶𐑽𐑯𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑴", 3183069),
    ("∋⋈⊞◻⊣⊢⊙∈≻⊤≺⊥", "𐑛𐑶𐑽𐑯𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑴", 3183069),
    ("⋈⊞◻⊣⊢⊙∈≻⊤≺⊥∋", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),
    ("⊞◻⊣⊢⊙∈≻⊤≺⊥∋⋈", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),
    ("◻⊣⊢⊙∈≻⊤≺⊥∋⋈⊞", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),
    ("⊣⊢⊙∈≻⊤≺⊥∋⋈⊞◻", "𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭", 3442270),
    ("⊢⊙∈⊞⊤⋈≻≺∋◻⊣", "𐑛𐑶𐑾𐑹𐑞𐑘𐑲𐑠𐑣𐑫𐑳𐑭", 3427918),
    ("⊙∈⊞⊤⋈≻≺∋◻⊣⊢", "𐑛𐑶𐑾𐑹𐑞𐑘𐑲𐑠𐑣𐑫𐑳𐑭", 3427918),
    ("∈⊞⊤⋈≻≺∋◻⊣⊢⊙", "𐑛𐑶𐑾𐑹𐑞𐑘𐑲𐑠𐑣𐑫𐑳𐑭", 3427918),
    ("⊞⊤⋈≻≺∋◻⊣⊢⊙∈", "𐑛𐑶𐑽𐑯𐑞𐑘𐑲𐑠𐑣𐑫𐑳𐑴", 3168717),
    ("⊤⋈≻≺∋◻⊣⊢⊙∈⊞", "𐑛𐑶𐑽𐑯𐑞𐑘𐑲𐑠𐑣𐑫𐑳𐑴", 3168717),
    ("⋈≻≺∋◻⊣⊢⊙∈⊞⊤", "𐑛𐑶𐑽𐑯𐑞𐑘𐑲𐑠𐑣𐑫𐑳𐑴", 3168717),
    ("≻≺∋◻⊣⊢⊙∈⊞⊤⋈", "𐑛𐑶𐑽𐑯𐑞𐑘𐑲𐑠𐑣𐑫𐑳𐑴", 3168717),
    ("≺∋◻⊣⊢⊙∈⊞⊤⋈≻", "𐑛𐑶𐑽𐑯𐑞𐑘𐑲𐑠𐑣𐑫𐑳𐑴", 3168717),
    ("∋◻⊣⊢⊙∈⊞⊤⋈≻≺", "𐑛𐑶𐑽𐑯𐑞𐑘𐑲𐑠𐑣𐑫𐑳𐑴", 3168717),
    ("◻⊣⊢⊙∈⊞⊤⋈≻≺∋", "𐑛𐑶𐑾𐑹𐑞𐑘𐑲𐑠𐑣𐑫𐑳𐑭", 3427918),
    ("⊣⊢⊙∈⊞⊤⋈≻≺∋◻", "𐑛𐑶𐑾𐑹𐑞𐑘𐑲𐑠𐑣𐑫𐑳𐑭", 3427918),
]

# The four verbs over item 1's twelve cuts, run through run_hosted_cmds.sh.
# banked / weight / insert partition the orbit 4/2/6, which is NOT the crystal's 7/5:
# k = 8,9,10 sit at 3442270 and are vacuous.  Same IG type, different token content --
# the token algebra is finer than the crystal, measured here rather than cited.
# trans is fully rotation-invariant: ring 12, linear 11 at every cut, only the closing
# edge label moves.
VERBS = [
    # k, rotation,          banked,    final, dep/clr/rst, insert,       surviving
    (0,  "⊢⊙∈≻⊤≺⊥∋⋈⊞◻⊣", "OK",      "A",   "3/1/1", "holds",      "T,F,t,f"),
    (1,  "⊙∈≻⊤≺⊥∋⋈⊞◻⊣⊢", "OK",      "A",   "3/1/1", "holds",      "T,F,t,f"),
    (2,  "∈≻⊤≺⊥∋⋈⊞◻⊣⊢⊙", "OK",      "A",   "3/1/1", "holds",      "T,F,t,f"),
    (3,  "≻⊤≺⊥∋⋈⊞◻⊣⊢⊙∈", "LEAK 1",  "Ftf", "3/1/0", "2 repairs",  "F,t,f"),
    (4,  "⊤≺⊥∋⋈⊞◻⊣⊢⊙∈≻", "LEAK 1",  "Ftf", "3/1/0", "1 repair",   "F,t,f"),
    (5,  "≺⊥∋⋈⊞◻⊣⊢⊙∈≻⊤", "VACUOUS", "Ftf", "2/0/0", "vacuous",    "F,t,f"),
    (6,  "⊥∋⋈⊞◻⊣⊢⊙∈≻⊤≺", "VACUOUS", "Ftf", "2/0/0", "vacuous",    "F,t,f"),
    (7,  "∋⋈⊞◻⊣⊢⊙∈≻⊤≺⊥", "VACUOUS", "tf",  "1/0/0", "vacuous",    "t,f"),
    (8,  "⋈⊞◻⊣⊢⊙∈≻⊤≺⊥∋", "VACUOUS", "tf",  "1/0/0", "vacuous",    "t,f"),
    (9,  "⊞◻⊣⊢⊙∈≻⊤≺⊥∋⋈", "VACUOUS", "tf",  "1/0/0", "vacuous",    "t,f"),
    (10, "◻⊣⊢⊙∈≻⊤≺⊥∋⋈⊞", "VACUOUS", "T",   "0/0/0", "vacuous",    "none"),
    (11, "⊣⊢⊙∈≻⊤≺⊥∋⋈⊞◻", "OK",      "A",   "3/1/1", "holds",      "T,F,t,f"),
]

TRIPLE = ("⊤", "⊥", "⊞")

if __name__ == "__main__":
    print(f"{'word':<28} {'⋈':>3} {'⊙':>3} {'crystal':>10}  full ⊤⊥⊞?")
    for w, t, c in DERIVED:
        full = all(g in w for g in TRIPLE)
        print(f"{w:<28} {t[4]:>3} {t[8]:>3} {c:>10}  {full}")
    bad = [(w, t, c) for w, t, c in DERIVED
           if (all(g in w for g in TRIPLE)) != (t[4] == "𐑐" and t[8] == "𐑻")]
    print(f"\nfixed cut at ⊢: counterexamples to 'full triple <-> ⋈𐑐 ⊙𐑻': {len(bad)}")

    print("\nROTAT orbit — the address is PHASE-BEARING:")
    print(f"  {'rotation':<28} {'≻':>3} {'≺':>3} {'◻':>3} {'crystal':>10}")
    for w, t, c in ROTAT_ORBIT:
        print(f"  {w:<28} {t[2]:>3} {t[3]:>3} {t[11]:>3} {c:>10}")
    addrs = sorted({c for _, _, c in ROTAT_ORBIT})
    print(f"\n  distinct addresses over the orbit: {len(addrs)}  {addrs}")
    inv = [i for i in range(12)
           if len({t[i] for _, t, _ in ROTAT_ORBIT if len(t) == 12}) == 1]
    print(f"  slots invariant across the whole orbit: {inv}")

    print("\nthe four verbs over the same twelve cuts:")
    print(f"  {'k':>2} {'banked':<8} {'final':<5} {'d/c/r':<7} {'insert':<10} surviving")
    for k, w, b, f, dcr, ins, sur in VERBS:
        print(f"  {k:>2} {b:<8} {f:<5} {dcr:<7} {ins:<10} {sur}")
    banks = [k for k, *_ , in VERBS if _[0] == "OK"] if False else [v[0] for v in VERBS if v[2] == "OK"]
    print(f"\n  banks at cuts {banks};  crystal 3442270 at cuts "
          f"{[i for i, (w, t, c) in enumerate(ROTAT_ORBIT[:12]) if c == 3442270]}")
    print("  the two partitions differ -- token algebra finer than the crystal")

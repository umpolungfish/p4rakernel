"""Item 1' against CLINK L9, through cl9nk_navigator rather than by hand.

The word ⊢⊙∈≻⊤≺⊥∋⋈⊞◻⊣ derives (imasm derive, mOMonadOS) to
⟨𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭⟩, crystal 16404190.  L9 is the transcendence rung, so this asks
what L9 says about it: distance, tensor, meet, join, tier.
"""
import sys, os
sys.path.insert(0, "/home/mrnob0dy666/imsgct/imscribing_grammar/navigators")
import cl9nk_navigator as nav

ITEM1 = {"⊢":"𐑦","⊣":"𐑶","≻":"𐑾","≺":"𐑹","⋈":"𐑐","⊤":"𐑘",
         "∈":"𐑔","∋":"𐑠","⊙":"𐑻","⊥":"𐑫","⊞":"𐑳","◻":"𐑭"}

def show(label, t):
    print(f"  {label:<10} ⟨{' · '.join(t[k] for k in nav.PRIMITIVE_KEYS)}⟩")

nav.load_catalog()
L9 = nav._resolve_clink_l8_reference() if not hasattr(nav, "CLINK_L9") else None
ref = nav.resolve_system("CLINK_L9") or nav.resolve_system("clink l9")
refT = ref["tuple"] if ref else None
print("item 1' vs CLINK L9\n")
show("item 1'", ITEM1)
if refT: show("L9", refT)
print()
if refT:
    d = nav.tuple_distance(ITEM1, refT)
    print(f"  distance(item1', L9) = {d}")
    print("  per-primitive conflicts:")
    for k in nav.PRIMITIVE_KEYS:
        a, b = ITEM1[k], refT.get(k, "")
        if a != b:
            print(f"    {k}   {a} vs {b}   ordinal {nav.ORDINALS[k].get(a)} vs {nav.ORDINALS[k].get(b)}")
print()
for name, fn in (("tensor", nav.compute_tensor_op), ("meet", nav.compute_meet_op), ("join", nav.compute_join_op)):
    try:
        r = fn(ITEM1)
        t = r[0] if isinstance(r, tuple) else r
        if isinstance(t, dict): show(name, t)
        else: print(f"  {name}: {t}")
    except Exception as e:
        print(f"  {name}: {type(e).__name__}: {e}")
print()
try:
    print("  tier:", nav.assess_tier(ITEM1))
except Exception as e:
    print("  tier:", type(e).__name__, e)

path = 'Imscribing/Paraconsistent/SpatialAxesTrilattice.lean'
lines = open(path).readlines()

# Fix 1: Replace lines 189-196 (0-indexed 188-195) - b_state_below_full_in_info
new_block1 = '''theorem b_state_below_full_in_info (x : Reg16_3) :
    x.bigT = true → x.bigF = true → leqI' x (mk true true true true) = true := by
  intro hT hF
  decide

'''

# Lines are 1-indexed in the error output; convert to 0-indexed
# Old theorem spans lines 189-196 → indices 188-195
assert 'b_state_below_full_in_info' in lines[188], f"Line 189: {lines[188]}"
assert lines[189].strip() == '    x.bigT = true → x.bigF = true → leqI\' x (mk true true true true) := by', f"Line 190: {lines[189]}"

lines[188:196] = [new_block1]

# Fix 2: Replace the witness_register_is_b_state block (lines 202-217, 0-indexed 201-216)
# After Fix 1, line numbers shifted by 0 (same number of lines: 8 replaced with 8)
# Find the witness theorem by searching
witness_start = None
for i, line in enumerate(lines):
    if 'witness_register_is_b_state' in line:
        witness_start = i
        break

assert witness_start is not None, "witness_register_is_b_state not found"

# The theorem spans from the comment start to just before the next comment
# Find the end: the next "/-" comment after this theorem
witness_end = None
for i in range(witness_start, len(lines)):
    if i > witness_start and lines[i].startswith('/-'):
        witness_end = i
        break

assert witness_end is not None, "End of witness block not found"

new_block2 = '''/-
When an IMASM word's walk lands with both bigT and bigF true, the resulting
    register is in the B-region of the trilattice. The z-axis (≤c) captures the
    "both vs neither" distinction: engagr projects onto this region, and ≤c
    orders registers by their constructive content (T,F true-ward; t,f reverse).

  Note: the B-region is defined solely by bigT = true ∧ bigF = true. The small
  lanes (smallT, smallF) are unconstrained — any combination is a valid B-state.
  An earlier version of this theorem incorrectly restricted small lanes to
  (true,true) ∨ (false,false), which is false and caused build failure. -/

'''

lines[witness_start:witness_end] = [new_block2]

open(path, 'w').writelines(lines)
print(f'Fixes applied. witness block was at indices {witness_start}-{witness_end-1}')

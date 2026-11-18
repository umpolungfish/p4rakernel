path = "/home/mrnob0dy666/imsgct/p4rakernel/p4ramill/Imscribing/Paraconsistent/SpatialAxesTrilattice.lean"
with open(path, encoding='utf-8') as f:
    content = f.read()

# Fix reflexivity proofs: constructor doesn't flatten nested conjunctions
content = content.replace(
    "constructor <;> intro h <;> exact h",
    "repeat { constructor } <;> intro h <;> exact h"
)

# Fix swapped arguments in transitivity proofs
content = content.replace("exact h₁₁ (h₂₁ h)", "exact h₂₁ (h₁₁ h)")
content = content.replace("exact h₁₂ (h₂₂ h)", "exact h₂₂ (h₁₂ h)")

# Fix .trans on functions in leqI'_trans (functions don't have .trans)
content = content.replace("exact (h₁.1).trans (h₂.1) h", "exact h₂.1 (h₁.1 h)")
content = content.replace("exact (h₁.2.1).trans (h₂.2.1) h", "exact h₂.2.1 (h₁.2.1 h)")
content = content.replace("exact (h₁.2.2.1).trans (h₂.2.2.1) h", "exact h₂.2.2.1 (h₁.2.2.1 h)")
content = content.replace("exact (h₁.2.2.2).trans (h₂.2.2.2) h", "exact h₂.2.2.2 (h₁.2.2.2 h)")

# Fix antisymmetry proofs: tauto can't handle Bool field equality
content = content.replace("<;> tauto", "<;> decide")

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)

print("All fixes applied")

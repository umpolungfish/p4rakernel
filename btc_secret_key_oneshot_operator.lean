-- btc_secret_key_oneshot_operator
-- Crystal: 2564782 (tier O₀)
-- IMASM Word: ≻⋈◻⊥⊤≻⋈⋈≻≺⊞⊙
-- Tuple: ⟨⊙:𐑢, ≺:𐑯, ◻:𐑭, ⊢:𐑦, ⊣:𐑰, ≻:𐑾, ⋈:𐑞, ⊤:𐑘, ∈:𐑲, ∋:𐑵, ⊥:𐑫, ⊞:𐑕⟩
-- Status: OPEN round, d=12 SIC-POVM measurement space

namespace btc_secret_key_oneshot_operator

/-- One-shot operator for BTC secret key operations in the Imscribing Grammar -/
structure btc_secret_key_oneshot_operator where
  crystal : Nat := 2564782
  tier : String := "O₀"
  imasm_word : String := "≻⋈◻⊥⊤≻⋈⋈≻≺⊞⊙"
  tuple : List (Char × Char) := [
    ('⊙', '𐑢'), ('≺', '𐑯'), ('◻', '𐑭'), ('⊢', '𐑦'),
    ('⊣', '𐑰'), ('≻', '𐑾'), ('⋈', '𐑞'), ('⊤', '𐑘'),
    ('∈', '𐑲'), ('∋', '𐑵'), ('⊥', '𐑫'), ('⊞', '𐑕')
  ]
  status : String := "OPEN"
  d12_sic_povm : Bool := true

end btc_secret_key_oneshot_operator
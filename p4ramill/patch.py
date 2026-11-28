from pathlib import Path


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    assert count == 1, f"{label}: expected 1 match, found {count}"
    return text.replace(old, new, 1)


def patch_sic_channel(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    old = """  · rw [if_pos h]
    simp [h_restore f b]
    try rw [Function.update_eq_self]
    rw [h]
    simp"""
    new = """  · rw [if_pos h]
    simp [h_restore f b]
    try rw [Function.update_eq_self]
    rw [h]
    simp
    left
    congr 1
    ext x
    by_cases hx : x = k
    · subst hx; simp [h]
    · simp [Function.update_of_ne hx]"""
    text = replace_exact(text, old, new, "SICChannel:close_left")
    path.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    patch_sic_channel(Path("Imscribing/TrilatticeYM/SICChannel.lean"))
    print("Patched SICChannel.lean successfully.")
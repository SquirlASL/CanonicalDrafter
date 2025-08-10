import Mathlib

-- certain tactics are "banned" meaning that they won't be considered by the havedraft tracer
-- right now the banned ones are `intro, intros, rintro`

theorem test_intro : ∀ (a : Nat), a = a := by
  intro a
  sorry

theorem test_intros : ∀ (a b : Nat), a = a ∧ b = b := by
  intros a b
  sorry

theorem test_rintro : ∀ (ab : Nat × Nat), ab.1 = ab.1 ∧ ab.2 = ab.2 := by
  rintro ⟨a, b⟩
  sorry

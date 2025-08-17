import Mathlib

theorem womp (a : Fin 3): (⟨1, by decide⟩ : Fin 3) = 0 + a := by
  rw [add_comm]
  sorry

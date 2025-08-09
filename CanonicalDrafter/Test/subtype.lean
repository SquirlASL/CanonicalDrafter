import Mathlib

theorem womp : (⟨1, by decide⟩ : Fin 3) = 0 + 1 := by
  rw [add_comm]
  sorry

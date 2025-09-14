import Mathlib
import CanonicalDrafter

open Real
open Pointwise CauSeq

variable {ι : Sort*} {f : ι → ℝ} {s : Set ℝ} {a : ℝ}


theorem qqqq (hne : s.Nonempty) (hbdd : BddAbove s) : ∃ x, IsLUB s x := by
  rcases hne, hbdd with ⟨⟨L, hL⟩, ⟨U, hU⟩⟩
  have : ∀ d : ℕ, BddAbove { m : ℤ | ∃ y ∈ s, (m : ℝ) ≤ y * d } := by
    obtain ⟨k, hk⟩ := exists_int_gt U

    refine fun d => ⟨k * d, fun z h => ?_⟩
    rcases h with ⟨y, yS, hy⟩
    let h : (↑z : ℝ) ≤ (y * ↑d) * (↑d : ℝ) := sorry
    refine Int.cast_le.1 (hy.trans ?_)
    push_cast
    exact mul_le_mul_of_nonneg_right ((hU yS).trans hk.le) d.cast_nonneg
  sorry

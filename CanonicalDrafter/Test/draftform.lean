import Mathlib
import Canonical

open Real
open Pointwise CauSeq

variable {ι : Sort*} {f : ι → ℝ} {s : Set ℝ} {a : ℝ}


theorem qqq (s : Set ℝ) (L : ℝ) (hL : L ∈ s) (U : ℝ) (hU : U ∈ upperBounds s) : ∀ d : ℕ, BddAbove { m : ℤ | ∃ y ∈ s, (m : ℝ) ≤ y * d } := by
  have q : ∃ (n : ℤ), U < (↑n : ℝ) := exists_int_gt U
  destruct
  have q : ∀ (d : ℕ), ∀ z ∈ {m : ℤ | ∃ y ∈ s, (↑m : ℝ) ≤ y * (↑d : ℝ)}, z ≤ q_w * (↑d : ℤ) := by
    intros; expose_names
    have q : ∀ y ∈ s, (↑z : ℝ) ≤ y * (↑d : ℝ) → z ≤ q_w * (↑d : ℤ) := by
      clear h
      intros; expose_names
      have : y * (↑d : ℝ) ≤ (↑(q_w * (↑d : ℤ)) : ℝ) := by
        have q : y * (↑d : ℝ) ≤ (↑q_w : ℝ) * (↑d : ℝ) := by
          exact mul_le_mul_of_nonneg_right ((hU h).trans q_h.le) d.cast_nonneg
        push_cast; linarith
      exact Int.cast_le.1 (h_1.trans this)
    exact let ⟨y, yS, hy⟩ := h; q y yS hy
  exact fun d => ⟨q_w * d, q d⟩

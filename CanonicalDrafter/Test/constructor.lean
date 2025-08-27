example : (0 ≤ 2) ∧ (0 ≤ 1) := by
  constructor
  apply Nat.le.step
  apply Nat.le.step
  exact Nat.le.refl
  apply Nat.le.step
  exact Nat.le.refl

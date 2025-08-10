theorem test_le_mul_right (a b : Nat) (h : a * b ≠ 0) : a ≤ (a * b) := by
  induction b
  exact by
    simp only [Nat.le_eq, Nat.le_zero_eq, Nat.mul_zero, Nat.mul_eq] <;>
      exact False.rec (fun t ↦ a = Nat.zero) (h (Eq.refl Nat.zero))
  expose_names
  change a ≤ a * n + a
  exact
    Nat.rec (motive := fun t ↦ a.le (t.add a))
      (by simp only [Nat.zero_add, Nat.add_eq] <;> exact Nat.le.refl)
      (fun n n_ih ↦ by simp only [Nat.add_eq, Nat.succ_add] <;> exact Nat.le.step n_ih) (a.mul n)

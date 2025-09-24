theorem lll (h : 2 = 2) (q : 2 + 3 * 2 = 8) : 1 + 1 = 3 := by
  rw [Nat.mul_comm, Nat.add_comm] at q
  sorry

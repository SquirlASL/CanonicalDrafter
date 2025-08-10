theorem test_le_mul_right (a b : Nat) (h : a * b ≠ 0) : a ≤ (a * b : Int) := by
  induction b with
  | zero => sorry
  | succ n' => sorry

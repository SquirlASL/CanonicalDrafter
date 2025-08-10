-- test disambiguation logic
theorem helper (a b c : Nat) : a = 1 → b = 1 → c = 1 → c ≠ 2 → (a + b) + c = c + b + a := sorry

theorem lol (a b c : Nat) : (a + b) + c = c + b + a := by
  apply helper
  · sorry
  · sorry
  · sorry
  · sorry

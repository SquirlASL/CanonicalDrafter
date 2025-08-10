import Mathlib.Tactic

theorem qwe (b : Nat):  ∃ x : Nat, x + b = b + x:= by
  use 2
  exact Nat.add_comm 2 b

example : 2 + 2 = 4 := by
  -- fall through cases
  let ⟨i, hi⟩ : Fin 3 := 0
  obtain ⟨a, b⟩ : 2 = 2 ∧ 3 = 3 := by
    apply And.intro
    rfl
    rfl
  -- non fall through cases
  have bruh : ∃ x : Nat, x = x := ⟨5, rfl⟩
  let ⟨test1, test2⟩ := bruh
  -- anonoymous types
  have q := hi
  obtain qq := hi
  let qqq := hi
  rfl

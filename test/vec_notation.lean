import data.fin.vec_notation

/-! These tests are testing `pi_fin.reflect` and fail with
`local attribute [-instance] pi_fin.reflect` -/

#eval do
  let x : fin 0 → ℕ := ![],
  tactic.is_def_eq `(x) `(![] : fin 0 → ℕ)

#eval do
  let x := ![1, 2, 3],
  tactic.is_def_eq `(x) `(![1, 2, 3])

#eval do
  let x := ![ulift.up.{3} 1, ulift.up.{3} 2],
  tactic.is_def_eq (reflect x) `(![ulift.up.{3} 1, ulift.up.{3} 2])

#eval do
  let x := ![![1, 2], ![3, 4]],
  tactic.is_def_eq `(x) `(![![1, 2], ![3, 4]])

/-! These tests are testing `pi_fin.has_repr` -/

#eval show tactic unit, from guard (repr (![] : _ → ℕ) = "![]")
#eval show tactic unit, from guard (repr ![1, 2, 3] = "![1, 2, 3]")
#eval show tactic unit, from guard (repr ![![1, 2], ![3, 4]] = "![![1, 2], ![3, 4]]")

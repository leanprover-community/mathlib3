import tactic.zify

namespace tactic.interactive
setup_tactic_parser open tactic

meta def guard_hyp_red (n : parse ident) (p : parse $ tk ":" *> texpr) : tactic unit := do
h ← get_local n >>= infer_type >>= instantiate_mvars,
e ← to_expr p,
is_def_eq h e transparency.none

meta def guard_target_red (p : parse texpr) : tactic unit := do
tgt ← target,
e ← to_expr p,
is_def_eq tgt e transparency.none

end tactic.interactive

example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) (h2 : (c : ℤ) < a + 3 * b) : a + 3*b > c :=
begin
  zify at h ⊢,
  guard_hyp_red h : ¬↑x * ↑y * ↑z < (0 : ℤ),
  guard_target_red ↑c < (↑a : ℤ) + 3 * ↑b,
  exact h2
end

example (a b : ℕ) (h : (a : ℤ) ≤ b) : a ≤ b :=
begin
  zify,
  guard_target (a : ℤ) ≤ b,
  exact h
end

example (a b : ℕ) (h : a = b ∧ b < a) : false :=
begin
  zify at h,
  cases h with ha hb,
  apply ne_of_lt hb,
  rw ha
end

example (a b c : ℕ) (h : a - b < c) (hab : b ≤ a) : true :=
begin
  zify [hab] at h,
  guard_hyp_red h : (a : ℤ) - b < c,
  trivial
end

example (a b c : ℕ) (h : a + b ≠ c) : true :=
begin
  zify at h,
  guard_hyp_red h : (a : ℤ) + b ≠ c,
  trivial
end

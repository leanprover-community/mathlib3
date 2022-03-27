import tactic.lint

-- The following simp lemma has the variable `f` as head symbol of the left-hand side:
@[simp] axiom const_zero_eq_zero (f : ℕ → ℕ) (x) : f x = 0

example (f : ℕ → ℕ) : f 42 = 0 :=
begin
  -- Hence it doesn't work:
  success_if_fail {simp},

  -- BTW, rw doesn't work either:
  success_if_fail {rw const_zero_eq_zero},

  -- It only works if explicitly instantiate with `f`:
  simp only [const_zero_eq_zero f]
end


open tactic
run_cmd do
decl ← get_decl ``const_zero_eq_zero,
res ← linter.simp_var_head.test decl,
-- linter complains
guard $ res.is_some



-- However injectivity lemmas can still be marked simp,
-- even though injective is reducible and unfolds to a bad simp lemma:
@[simp] axiom injective_succ : function.injective nat.succ

run_cmd do
decl ← get_decl ``injective_succ,
res ← linter.simp_var_head.test decl,
-- linter does not complain
guard res.is_none

import tactic.lint

-- Consider a simp lemma that is a definitionally equality, but whose proof is not `rfl`:
@[simp] lemma add_zero' (x) : x + 0 = x :=
eq.refl _

example (x) : x + 0 = x :=
begin
  -- Such a lemma is not used by `dsimp`:
  success_if_fail {dsimp only [add_zero']},

  -- This only works if the proof is literally rfl:
  dsimp only [nat.add_zero],
  guard_target x = x,
  refl
end


open tactic
#eval do
decl ← get_decl ``add_zero',
res ← linter.rfl_lemma.test decl,
-- linter complains
guard $ res.is_some

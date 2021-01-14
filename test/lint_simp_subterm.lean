import tactic.lint

def f : ℕ → ℕ := id

lemma a : f 0 = 0 := rfl
@[simp] lemma b : f 1 = 1 := rfl
lemma c : f 1 = 1 + 0 := rfl
lemma d (x) : f x = x := rfl
lemma e : f 0 = f 0 := rfl
lemma g : f (1+0) = 1 := rfl

structure x : Prop := (x : true)
lemma h (h : x) : (⟨h.x⟩ : x) = h := rfl

open tactic

run_cmd do
decl ← get_decl ``a,
res ← linter.simp_subterm.test decl,
-- linter complains
guard res.is_some

run_cmd do
decl ← get_decl ``b,
res ← linter.simp_subterm.test decl,
-- linter does not complain
guard res.is_none

run_cmd do
decl ← get_decl ``c,
res ← linter.simp_subterm.test decl,
-- linter does not complain
guard res.is_none

run_cmd do
decl ← get_decl ``d,
res ← linter.simp_subterm.test decl,
-- linter complains
guard res.is_some

run_cmd do
decl ← get_decl ``e,
res ← linter.simp_subterm.test decl,
-- linter does not complain
guard res.is_none

run_cmd do
decl ← get_decl ``g,
res ← linter.simp_subterm.test decl,
-- linter does not complain
guard res.is_none

run_cmd do
decl ← get_decl ``h,
res ← linter.simp_subterm.test decl,
-- linter does not complain
guard res.is_none

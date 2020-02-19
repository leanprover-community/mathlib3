import tactic.lint

def f : ℕ → ℕ := default _
def g : ℕ → ℕ := default _
def c : ℕ := default _
def d : ℕ := default _

-- The following TRS is non-confluent, since `f d <-- f (g c) --> c` is not joinable
@[simp] lemma a : g c = d := rfl
@[simp] lemma b {x} : f (g x) = c := rfl

open tactic
#eval do
decl ← get_decl ``b,
res ← linter.simp_nonconfl.test decl,
-- linter complains
trace res,
guard $ res.is_some

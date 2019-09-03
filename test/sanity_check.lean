import tactic.sanity_check

def foo1 (n m : ℕ) : ℕ := n + 1
def foo2 (n m : ℕ) : m = m := by refl
lemma foo3 (n m : ℕ) : ℕ := n - m
lemma foo4 (n m : ℕ) : n ≤ n := by refl

run_cmd do
  let t := name × list ℕ,
  e ← fold_over_with_cond
    (λ d, d.in_current_file >>= λ b, if b then return (check_unused_arguments d) else return none),
  guard $ e.length = 3,
  let e2 : list t := e.map $ λ x, ⟨x.1.to_name, x.2⟩,
  guard $ (⟨`foo1, [2]⟩ : t) ∈ e2,
  guard $ (⟨`foo2, [1]⟩ : t) ∈ e2,
  guard $ (⟨`foo4, [2]⟩ : t) ∈ e2

run_cmd do
  e ← fold_over_with_cond
    (λ d, d.in_current_file >>= λ b, if b then incorrect_def_lemma d else return none),
  guard $ e.length = 2,
  let e2 : list (name × _) := e.map $ λ x, ⟨x.1.to_name, x.2⟩,
  guard $ ∃(x ∈ e2), (x : name × _).1 = `foo2,
  guard $ ∃(x ∈ e2), (x : name × _).1 = `foo3

-- #sanity_check_mathlib

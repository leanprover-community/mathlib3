import tactic.sanity_check

def foo1 (n m : ℕ) : ℕ := n + 1
def foo2 (n m : ℕ) : m = m := by refl
lemma foo3 (n m : ℕ) : ℕ := n - m
lemma foo4 (n m : ℕ) : n ≤ n := by refl

open tactic

run_cmd do
  let t := name × list ℕ,
  e ← get_env,
  l ← e.mfilter (λ d, return $
    e.in_current_file' d.to_name && ¬ d.to_name.is_internal && ¬ d.is_auto_generated e),
  l2 ← fold_over_with_cond l (return ∘ check_unused_arguments),
  guard $ l2.length = 3,
  let l2 : list t := l2.map $ λ x, ⟨x.1.to_name, x.2⟩,
  guard $ (⟨`foo1, [2]⟩ : t) ∈ l2,
  guard $ (⟨`foo2, [1]⟩ : t) ∈ l2,
  guard $ (⟨`foo4, [2]⟩ : t) ∈ l2,
  l2 ← fold_over_with_cond l incorrect_def_lemma,
  guard $ l2.length = 2,
  let l2 : list (name × _) := l2.map $ λ x, ⟨x.1.to_name, x.2⟩,
  guard $ ∃(x ∈ l2), (x : name × _).1 = `foo2,
  guard $ ∃(x ∈ l2), (x : name × _).1 = `foo3

-- #sanity_check_mathlib

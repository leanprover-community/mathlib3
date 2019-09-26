import tactic.sanity_check

def foo1 (n m : ℕ) : ℕ := n + 1
def foo2 (n m : ℕ) : m = m := by refl
lemma foo3 (n m : ℕ) : ℕ := n - m
lemma foo.foo (n m : ℕ) : n ≥ n := le_refl n
-- section
-- local attribute [instance, priority 1001] classical.prop_decidable
-- lemma foo4 : (if 3 = 3 then 1 else 2) = 1 := if_pos (by refl)
-- end

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
  guard $ (⟨`foo.foo, [2]⟩ : t) ∈ l2,
  l2 ← fold_over_with_cond l incorrect_def_lemma,
  guard $ l2.length = 2,
  let l2 : list (name × _) := l2.map $ λ x, ⟨x.1.to_name, x.2⟩,
  guard $ ∃(x ∈ l2), (x : name × _).1 = `foo2,
  guard $ ∃(x ∈ l2), (x : name × _).1 = `foo3,
  l3 ← fold_over_with_cond l dup_namespace,
  guard $ l3.length = 1,
  guard $ ∃(x ∈ l3), (x : declaration × _).1.to_name = `foo.foo,
  l4 ← fold_over_with_cond l illegal_constants_in_statement,
  guard $ l4.length = 1,
  guard $ ∃(x ∈ l4), (x : declaration × _).1.to_name = `foo.foo,
  -- guard $ ∃(x ∈ l4), (x : declaration × _).1.to_name = `foo4,
  s ← sanity_check ff,
  guard $ "/- (slow tests skipped) -/\n".is_suffix_of s.to_string,
  s2 ← sanity_check tt,
  guard $ s.to_string ≠ s2.to_string,
  skip

/- check customizability and sanity_skip -/
@[sanity_skip] def bar.foo : (if 3 = 3 then 1 else 2) = 1 := if_pos (by refl)

meta def dummy_check (d : declaration) : tactic (option string) :=
return $ if d.to_name.last = "foo" then some "gotcha!" else none

run_cmd do
  s ← sanity_check tt [(dummy_check, "found nothing", "found something")],
  guard $ "/- found something: -/\n#print foo.foo /- gotcha! -/\n\n".is_suffix_of s.to_string

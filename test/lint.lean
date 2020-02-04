import tactic.lint

def foo1 (n m : ℕ) : ℕ := n + 1
def foo2 (n m : ℕ) : m = m := by refl
lemma foo3 (n m : ℕ) : ℕ := n - m
lemma foo.foo (n m : ℕ) : n ≥ n := le_refl n
instance bar.bar : has_add ℕ := by apply_instance  -- we don't check the name of instances
lemma foo.bar (ε > 0) : ε = ε := rfl -- >/≥ is allowed in binders (and in fact, in all hypotheses)
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
  guard $ l2.length = 4,
  let l2 : list t := l2.map $ λ x, ⟨x.1.to_name, x.2⟩,
  guard $ (⟨`foo1, [2]⟩ : t) ∈ l2,
  guard $ (⟨`foo2, [1]⟩ : t) ∈ l2,
  guard $ (⟨`foo.foo, [2]⟩ : t) ∈ l2,
  guard $ (⟨`foo.bar, [2]⟩ : t) ∈ l2,
  l2 ← fold_over_with_cond l incorrect_def_lemma,
  guard $ l2.length = 2,
  let l2 : list (name × _) := l2.map $ λ x, ⟨x.1.to_name, x.2⟩,
  guard $ ∃(x ∈ l2), (x : name × _).1 = `foo2,
  guard $ ∃(x ∈ l2), (x : name × _).1 = `foo3,
  l3 ← fold_over_with_cond l dup_namespace,
  guard $ l3.length = 1,
  guard $ ∃(x ∈ l3), (x : declaration × _).1.to_name = `foo.foo,
  l4 ← fold_over_with_cond l ge_or_gt_in_statement,
  guard $ l4.length = 1,
  guard $ ∃(x ∈ l4), (x : declaration × _).1.to_name = `foo.foo,
  -- guard $ ∃(x ∈ l4), (x : declaration × _).1.to_name = `foo4,
  (_, s) ← lint ff,
  guard $ "/- (slow tests skipped) -/\n".is_suffix_of s.to_string,
  (_, s2) ← lint tt,
  guard $ s.to_string ≠ s2.to_string,
  skip

/- check customizability and nolint -/
@[nolint] def bar.foo : (if 3 = 3 then 1 else 2) = 1 := if_pos (by refl)

meta def dummy_check (d : declaration) : tactic (option string) :=
return $ if d.to_name.last = "foo" then some "gotcha!" else none

meta def linter.dummy_linter : linter :=
{ test := dummy_check,
  no_errors_found := "found nothing",
  errors_found := "found something" }

run_cmd do
  (_, s) ← lint tt tt [`linter.dummy_linter] tt,
  guard $ "/- found something: -/\n#print foo.foo /- gotcha! -/\n\n".is_suffix_of s.to_string

instance impossible_instance_test {α β : Type} [add_group α] : has_add α := infer_instance

run_cmd do
  d ← get_decl `impossible_instance_test,
  x ← impossible_instance d,
  guard $ x = some "Impossible to infer argument 2: {β : Type}"

def incorrect_type_class_argument_test {α : Type} (x : α) [x = x] [decidable_eq α] [group α] :
  unit := ()

run_cmd do
  d ← get_decl `incorrect_type_class_argument_test,
  x ← incorrect_type_class_argument d,
  guard $ x = some "These are not classes. argument 3: [_inst_1 : x = x]"

instance dangerous_instance_test {α β γ : Type} [ring α] [add_comm_group β] [has_coe α β]
  [has_inv γ] : has_add β := infer_instance

run_cmd do
  d ← get_decl `dangerous_instance_test,
  x ← dangerous_instance d,
  guard $ x = some "The following arguments become metavariables. argument 1: {α : Type}, argument 3: {γ : Type}"

import tactic.lint
import algebra.ring.basic

def foo1 (n m : ℕ) : ℕ := n + 1
def foo2 (n m : ℕ) : m = m := by refl
lemma foo3 (n m : ℕ) : ℕ := n - m
lemma foo.foo (n m : ℕ) : n ≥ n := le_refl n
instance bar.bar : has_add ℕ := by apply_instance  -- we don't check the name of instances
lemma foo.bar (ε > 0) : ε = ε := rfl -- >/≥ is allowed in binders (and in fact, in all hypotheses)
/-- Test exception in `def_lemma` linter. -/
@[pattern] def my_exists_intro := @Exists.intro
-- section
-- local attribute [instance, priority 1001] classical.prop_decidable
-- lemma foo4 : (if 3 = 3 then 1 else 2) = 1 := if_pos (by refl)
-- end

open tactic

meta def fold_over_with_cond {α} (l : list declaration) (tac : declaration → tactic (option α)) :
  tactic (list (declaration × α)) :=
l.mmap_filter $ λ d, option.map (λ x, (d, x)) <$> tac d

run_cmd do
  let t := name × list ℕ,
  e ← get_env,
  let l := e.filter (λ d, e.in_current_file d.to_name ∧ ¬ d.is_auto_or_internal e),
  l2 ← fold_over_with_cond l (return ∘ check_unused_arguments),
  guard $ l2.length = 4,
  let l2 : list t := l2.map $ λ x, ⟨x.1.to_name, x.2⟩,
  guard $ (⟨`foo1, [2]⟩ : t) ∈ l2,
  guard $ (⟨`foo2, [1]⟩ : t) ∈ l2,
  guard $ (⟨`foo.foo, [2]⟩ : t) ∈ l2,
  guard $ (⟨`foo.bar, [2]⟩ : t) ∈ l2,
  l2 ← fold_over_with_cond l linter.def_lemma.test,
  guard $ l2.length = 2,
  let l2 : list (name × _) := l2.map $ λ x, ⟨x.1.to_name, x.2⟩,
  guard $ ∃(x ∈ l2), (x : name × _).1 = `foo2,
  guard $ ∃(x ∈ l2), (x : name × _).1 = `foo3,
  l3 ← fold_over_with_cond l linter.dup_namespace.test,
  guard $ l3.length = 1,
  guard $ ∃(x ∈ l3), (x : declaration × _).1.to_name = `foo.foo,
  l4 ← fold_over_with_cond l linter.ge_or_gt.test,
  guard $ l4.length = 1,
  guard $ ∃(x ∈ l4), (x : declaration × _).1.to_name = `foo.foo,
  -- guard $ ∃(x ∈ l4), (x : declaration × _).1.to_name = `foo4,
  (_, s) ← lint ff,
  guard $ "/- (slow tests skipped) -/\n".is_suffix_of s.to_string,
  (_, s2) ← lint tt,
  guard $ s.to_string ≠ s2.to_string,
  skip

/- check customizability and nolint -/

meta def dummy_check (d : declaration) : tactic (option string) :=
return $ if d.to_name.last = "foo" then some "gotcha!" else none

meta def linter.dummy_linter : linter :=
{ test := dummy_check,
  auto_decls := ff,
  no_errors_found := "found nothing.",
  errors_found := "found something:" }

@[nolint dummy_linter]
def bar.foo : (if 3 = 3 then 1 else 2) = 1 := if_pos (by refl)

run_cmd do
  (_, s) ← lint tt lint_verbosity.medium [`linter.dummy_linter] tt,
  guard $ "/- found something: -/\n#check @foo.foo /- gotcha! -/\n".is_suffix_of s.to_string

def incorrect_type_class_argument_test {α : Type} (x : α) [x = x] [decidable_eq α] [group α] :
  unit := ()

run_cmd do
  d ← get_decl `incorrect_type_class_argument_test,
  x ← linter.incorrect_type_class_argument.test d,
  guard $ x = some "These are not classes. argument 3: [_inst_1 : x = x]"

section
def impossible_instance_test {α β : Type} [add_group α] : has_add α := infer_instance
local attribute [instance] impossible_instance_test
run_cmd do
  d ← get_decl `impossible_instance_test,
  x ← linter.impossible_instance.test d,
  guard $ x = some "Impossible to infer argument 2: {β : Type}"

def dangerous_instance_test {α β γ : Type} [ring α] [add_comm_group β] [has_coe α β]
  [has_inv γ] : has_add β := infer_instance
local attribute [instance] dangerous_instance_test
run_cmd do
  d ← get_decl `dangerous_instance_test,
  x ← linter.dangerous_instance.test d,
  guard $ x = some
    "The following arguments become metavariables. argument 1: {α : Type}, argument 3: {γ : Type}"
end

section
def foo_has_mul {α} [has_mul α] : has_mul α := infer_instance
local attribute [instance, priority 1] foo_has_mul
run_cmd do
  d ← get_decl `has_mul,
  some s ← fails_quickly 20 d,
  guard $ s = "type-class inference timed out"
local attribute [instance, priority 10000] foo_has_mul
run_cmd do
  d ← get_decl `has_mul,
  some s ← fails_quickly 3000 d,
  guard $ "maximum class-instance resolution depth has been reached".is_prefix_of s
end

instance beta_redex_test {α} [monoid α] : (λ (X : Type), has_mul X) α := ⟨(*)⟩
run_cmd do
  d ← get_decl `beta_redex_test,
  x ← linter.instance_priority.test d,
  guard $ x = some "set priority below 1000"

/- test of `apply_to_fresh_variables` -/
run_cmd do
  e ← mk_const `id,
  e2 ← apply_to_fresh_variables e,
  type_check e2,
  `(@id %%α %%a) ← instantiate_mvars e2,
  expr.sort (level.succ $ level.mvar u) ← infer_type α,
  skip

/- Test exception in `def_lemma` linter. -/
run_cmd do
  d ← get_decl `my_exists_intro,
  t ← linter.def_lemma.test d,
  guard $ t = none

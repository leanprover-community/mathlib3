import tactic.reduce_projections

open function tactic expr
structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)

infix ` ≃ `:25 := equiv

namespace foo

@[reduce_projections] protected def rfl {α} : α ≃ α :=
⟨id, λ x, x, λ x, rfl, λ x, rfl⟩

/- reduce_projections adds declarations -/
run_cmd do
  e ← get_env,
  e.get `foo.rfl_to_fun,
  e.get `foo.rfl_inv_fun,
  success_if_fail (e.get `foo.rfl_left_inv),
  success_if_fail (e.get `foo.rfl_right_inv)

example (n : ℕ) : foo.rfl.to_fun n = n := by rw [foo.rfl_to_fun, id]
example (n : ℕ) : foo.rfl.inv_fun n = n := by rw [foo.rfl_inv_fun]

/- the declarations are simp-lemmas -/
@[reduce_projections] def foo : ℕ × ℤ := (1, 2)

example : foo.1 = 1 := by simp
example : foo.2 = 2 := by simp
example {α} (x : α) : foo.rfl.to_fun x = x := by simp
example {α} (x : α) : foo.rfl.inv_fun x = x := by simp
example {α} (x : α) : foo.rfl.to_fun = @id α := by { success_if_fail {simp}, refl }

/- check some failures -/
def bar1 : ℕ := 1 -- type is not a structure
def bar2 : ℕ × ℤ := prod.map (λ x, x + 2) (λ y, y - 3) (3, 4) -- value is not a constructor
run_cmd do
  success_if_fail (reduce_projections_tac `bar1 tt),
  success_if_fail (reduce_projections_tac `bar2 tt)

end foo

/- test whether environment.get_projections works correctly on all structures -/
meta def test_projection (env : environment) (n : name) : tactic unit := do
  ns ← env.get_projections n,
  ns.mmap' $ λ n, if (env.is_projection n).is_some then skip else fail ns,
  skip

run_cmd do e ← get_env, e.mfold ()
  (λ d _, if e.is_structure d.to_name then test_projection e d.to_name else skip)

/- check projections for nested structures -/

namespace count_nested
@[reduce_projections] def nested1 : ℕ × ℤ × ℕ :=
⟨2, -1, 1⟩

@[reduce_projections] def nested2 : ℕ × ℕ × ℕ :=
⟨2, prod.map nat.succ nat.pred (1, 2)⟩

end count_nested

run_cmd do
  e ← get_env,
  e.get `count_nested.nested1_fst,
  e.get `count_nested.nested1_snd_fst,
  e.get `count_nested.nested1_snd_snd,
  e.get `count_nested.nested2_fst,
  e.get `count_nested.nested2_snd,
  b ← is_simp_lemma `count_nested.nested1_fst >>= λ b, guard b, -- simp attribute is global
  guard $ 7 = e.fold 0 -- there are no other lemmas generated
    (λ d n, n + if d.to_name.components.init.ilast = `count_nested then 1 else 0)

-- testing with arguments
@[reduce_projections] def bar {α : Type*} (n m : ℕ) : ℕ × ℤ :=
⟨n - m, n + m⟩

structure equiv_plus_data (α β) extends α ≃ β :=
(P : (α → β) → Prop)
(data : P to_fun)

structure automorphism_plus_data α extends α ⊕ α ≃ α ⊕ α :=
(P : (α ⊕ α → α ⊕ α) → Prop)
(data : P to_fun)
(extra : bool → ℕ × ℕ)

@[reduce_projections]
def refl_with_data {α} : equiv_plus_data α α :=
{ P := λ f, f = id,
  data := rfl,
  ..foo.rfl }

@[reduce_projections]
def refl_with_data' {α} : equiv_plus_data α α :=
{ P := λ f, f = id,
  data := rfl,
  to_equiv := foo.rfl }

/- test whether eta expansions are reduced correctly -/
@[reduce_projections]
def test {α} : automorphism_plus_data α :=
{ P := λ f, f = id,
  data := rfl,
  extra := λ b, ((3,5).1,(3,5).2),
  ..foo.rfl }

run_cmd do
  e ← get_env,
  e.get `refl_with_data_to_equiv,
  e.get `refl_with_data'_to_equiv,
  e.get `test_extra,
  success_if_fail (e.get `refl_with_data_to_equiv_to_fun),
  success_if_fail (e.get `refl_with_data'_to_equiv_to_fun),
  success_if_fail (e.get `test_extra_fst)

structure partially_applied_str :=
(data : ℕ → ℕ × ℕ)

/- if we have a partially applied constructor, we treat it as if it were eta-expanded -/
@[reduce_projections]
def partially_applied_term : partially_applied_str := ⟨prod.mk 3⟩

run_cmd do
  e ← get_env,
  e.get `partially_applied_term_data_fst,
  e.get `partially_applied_term_data_snd

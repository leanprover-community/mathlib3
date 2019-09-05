import tactic.reduce_projections data.equiv.basic

open tactic
namespace foo

/- the declarations exist -/
@[reduce_projections no_simp] protected def refl (α) : α ≃ α :=
⟨id, λ x, x, λ x, rfl, λ x, rfl⟩

run_cmd do
  e ← get_env,
  e.get `foo.refl_to_fun,
  e.get `foo.refl_inv_fun,
  success_if_fail (e.get `foo.refl_left_inv),
  success_if_fail (e.get `foo.refl_right_inv)

example (n : ℕ) : (foo.refl ℕ).to_fun n = n := by { rw [foo.refl_to_fun, id] }
example (n : ℕ) : (foo.refl ℕ).inv_fun n = n := by { rw [foo.refl_inv_fun] }

/- the declarations are simp-lemmas -/
@[reduce_projections] def foo : ℕ × ℤ := (1, 2)

example : foo.1 = 1 := by simp
example : foo.2 = 2 := by simp

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

namespace dummy_nat

/- test whether the declarations are created in a more complicated instance -/
@[reduce_projections]
instance my_nat_instance : decidable_linear_ordered_semiring nat :=
{ add_left_cancel            := @nat.add_left_cancel,
  add_right_cancel           := @nat.add_right_cancel,
  lt                         := nat.lt,
  le                         := nat.le,
  le_refl                    := nat.le_refl,
  le_trans                   := @nat.le_trans,
  le_antisymm                := @nat.le_antisymm,
  le_total                   := @nat.le_total,
  lt_iff_le_not_le           := @lt_iff_le_not_le _ _,
  add_le_add_left            := @nat.add_le_add_left,
  le_of_add_le_add_left      := @nat.le_of_add_le_add_left,
  zero_lt_one                := nat.zero_lt_succ 0,
  mul_le_mul_of_nonneg_left  := assume a b c h₁ h₂, nat.mul_le_mul_left c h₁,
  mul_le_mul_of_nonneg_right := assume a b c h₁ h₂, nat.mul_le_mul_right c h₁,
  mul_lt_mul_of_pos_left     := @nat.mul_lt_mul_of_pos_left,
  mul_lt_mul_of_pos_right    := @nat.mul_lt_mul_of_pos_right,
  decidable_lt               := nat.decidable_lt,
  decidable_le               := nat.decidable_le,
  decidable_eq               := nat.decidable_eq,
  ..nat.comm_semiring }

run_cmd do e ← get_env, guard $ 10 = e.fold 0
  (λ d n, n + if d.to_name.components.init.ilast = `dummy_nat then 1 else 0)

end dummy_nat

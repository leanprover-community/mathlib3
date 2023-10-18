/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.exterior_algebra.basic
import ring_theory.graded_algebra.basic

/-!
# Results about the grading structure of the exterior algebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Many of these results are copied with minimal modification from the tensor algebra.

The main result is `exterior_algebra.graded_algebra`, which says that the exterior algebra is a
ℕ-graded algebra.
-/

namespace exterior_algebra
variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
variables (R M)

open_locale direct_sum

/-- A version of `exterior_algebra.ι` that maps directly into the graded structure. This is
primarily an auxiliary construction used to provide `exterior_algebra.graded_algebra`. -/
def graded_algebra.ι : M →ₗ[R] ⨁ i : ℕ, ↥((ι R : M →ₗ[_] _).range ^ i) :=
direct_sum.lof R ℕ (λ i, ↥((ι R : M →ₗ[_] _).range ^ i)) 1
  ∘ₗ (ι R).cod_restrict _ (λ m, by simpa only [pow_one] using linear_map.mem_range_self _ m)

lemma graded_algebra.ι_apply (m : M) :
  graded_algebra.ι R M m =
    direct_sum.of (λ i, ↥((ι R : M →ₗ[_] _).range ^ i)) 1
      (⟨ι R m, by simpa only [pow_one] using linear_map.mem_range_self _ m⟩) := rfl

lemma graded_algebra.ι_sq_zero (m : M) : graded_algebra.ι R M m * graded_algebra.ι R M m = 0 :=
begin
  rw [graded_algebra.ι_apply, direct_sum.of_mul_of],
  refine dfinsupp.single_eq_zero.mpr (subtype.ext $ ι_sq_zero _),
end

/-- `exterior_algebra.graded_algebra.ι` lifted to exterior algebra. This is
primarily an auxiliary construction used to provide `exterior_algebra.graded_algebra`. -/
def graded_algebra.lift_ι : exterior_algebra R M →ₐ[R]
  ⨁ (i : ℕ), ↥((ι R).range ^ i : submodule R (exterior_algebra R M)) :=
lift R ⟨by apply graded_algebra.ι R M, graded_algebra.ι_sq_zero R M⟩

variables (R M)

lemma graded_algebra.lift_ι_eq (i : ℕ)
  (x : ((ι R : M →ₗ[R] exterior_algebra R M).range ^ i : submodule R (exterior_algebra R M))) :
  graded_algebra.lift_ι R M x =
    direct_sum.of (λ i, ↥((ι R).range ^ i : submodule R (exterior_algebra R M))) i x :=
begin
  cases x with x hx,
  dsimp only [subtype.coe_mk, direct_sum.lof_eq_of],
  refine submodule.pow_induction_on_left' _
    (λ r, _) (λ x y i hx hy ihx ihy, _) (λ m hm i x hx ih, _) hx,
  { rw [alg_hom.commutes, direct_sum.algebra_map_apply], refl },
  { rw [alg_hom.map_add, ihx, ihy, ←map_add], refl },
  { obtain ⟨_, rfl⟩ := hm,
    rw [alg_hom.map_mul, ih, graded_algebra.lift_ι, lift_ι_apply,
      graded_algebra.ι_apply R M, direct_sum.of_mul_of],
    exact direct_sum.of_eq_of_graded_monoid_eq (sigma.subtype_ext (add_comm _ _) rfl) },
end

/-- The exterior algebra is graded by the powers of the submodule `(exterior_algebra.ι R).range`. -/
instance graded_algebra :
  graded_algebra ((^) (ι R : M →ₗ[R] exterior_algebra R M).range : ℕ → submodule R _) :=
graded_algebra.of_alg_hom _
  -- while not necessary, the `by apply` makes this elaborate faster
  (by apply graded_algebra.lift_ι R M)
  -- the proof from here onward is identical to the `tensor_algebra` case
  (begin
    ext m,
    dsimp only [linear_map.comp_apply, alg_hom.to_linear_map_apply, alg_hom.comp_apply,
      alg_hom.id_apply, graded_algebra.lift_ι],
    rw [lift_ι_apply, graded_algebra.ι_apply R M, direct_sum.coe_alg_hom_of, subtype.coe_mk],
  end)
  (by apply graded_algebra.lift_ι_eq R M)

end exterior_algebra

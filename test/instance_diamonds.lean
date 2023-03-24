/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import algebra.module.pi
import data.polynomial.basic
import group_theory.group_action.prod
import group_theory.group_action.units
import data.complex.module
import ring_theory.algebraic
import data.zmod.basic
import ring_theory.tensor_product

/-! # Tests that instances do not form diamonds -/

/-! ## Scalar action instances -/
section has_smul
open_locale polynomial

example :
  (sub_neg_monoid.has_smul_int : has_smul ℤ ℂ) = (complex.has_smul : has_smul ℤ ℂ) :=
rfl

example : restrict_scalars.module ℝ ℂ ℂ = complex.module := rfl
example : restrict_scalars.algebra ℝ ℂ ℂ = complex.algebra := rfl

example (α β : Type*) [add_monoid α] [add_monoid β] :
  (prod.has_smul : has_smul ℕ (α × β)) = add_monoid.has_smul_nat := rfl

example (α β : Type*) [sub_neg_monoid α] [sub_neg_monoid β] :
  (prod.has_smul : has_smul ℤ (α × β)) = sub_neg_monoid.has_smul_int := rfl

example (α : Type*) (β : α → Type*) [Π a, add_monoid (β a)] :
  (pi.has_smul : has_smul ℕ (Π a, β a)) = add_monoid.has_smul_nat := rfl

example (α : Type*) (β : α → Type*) [Π a, sub_neg_monoid (β a)] :
  (pi.has_smul : has_smul ℤ (Π a, β a)) = sub_neg_monoid.has_smul_int := rfl

namespace tensor_product

open_locale tensor_product
open complex

/-! The `example` below times out. TODO Fix it!

/- `tensor_product.algebra.module` forms a diamond with `has_mul.to_has_smul` and
`algebra.tensor_product.tensor_product.semiring`. Given a commutative semiring `A` over a
commutative semiring `R`, we get two mathematically different scalar actions of `A ⊗[R] A` on
itself. -/
def f : ℂ ⊗[ℝ] ℂ →ₗ[ℝ] ℝ :=
tensor_product.lift
{ to_fun    := λ z, z.re • re_lm,
  map_add'  := λ z w, by simp [add_smul],
  map_smul' := λ r z, by simp [mul_smul], }

@[simp] lemma f_apply (z w : ℂ) : f (z ⊗ₜ[ℝ] w) = z.re * w.re := by simp [f]

/- `tensor_product.algebra.module` forms a diamond with `has_mul.to_has_smul` and
`algebra.tensor_product.tensor_product.semiring`. Given a commutative semiring `A` over a
commutative semiring `R`, we get two mathematically different scalar actions of `A ⊗[R] A` on
itself. -/
example :
  has_mul.to_has_smul (ℂ ⊗[ℝ] ℂ) ≠
  (@tensor_product.algebra.module ℝ ℂ ℂ (ℂ ⊗[ℝ] ℂ) _ _ _ _ _ _ _ _ _ _ _ _).to_has_smul :=
begin
  have contra : I ⊗ₜ[ℝ] I ≠ (-1) ⊗ₜ[ℝ] 1 := λ c, by simpa using congr_arg f c,
  contrapose! contra,
  rw has_smul.ext_iff at contra,
  replace contra := congr_fun (congr_fun contra (1 ⊗ₜ I)) (I ⊗ₜ 1),
  rw @tensor_product.algebra.smul_def ℝ ℂ ℂ (ℂ ⊗[ℝ] ℂ) _ _ _ _ _ _ _ _ _ _ _ _
    (1 : ℂ) I (I ⊗ₜ[ℝ] (1 : ℂ)) at contra,
  simpa only [algebra.id.smul_eq_mul, algebra.tensor_product.tmul_mul_tmul, one_mul, mul_one,
    one_smul, tensor_product.smul_tmul', I_mul_I] using contra,
end

-/

end tensor_product

section units

example (α : Type*) [monoid α] :
  (units.mul_action : mul_action αˣ (α × α)) = prod.mul_action := rfl

example (R α : Type*) (β : α → Type*) [monoid R] [Π i, mul_action R (β i)] :
  (units.mul_action : mul_action Rˣ (Π i, β i)) = pi.mul_action _ := rfl

example (R α : Type*) (β : α → Type*) [monoid R] [semiring α] [distrib_mul_action R α] :
  (units.distrib_mul_action : distrib_mul_action Rˣ α[X]) =
    polynomial.distrib_mul_action :=
rfl

/-!
TODO: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/units.2Emul_action'.20diamond/near/246402813
```lean
example {α : Type*} [comm_monoid α] :
  (units.mul_action' : mul_action αˣ αˣ) = monoid.to_mul_action _ :=
rfl -- fails
```
-/

end units

end has_smul

/-! ## `with_top` (Type with point at infinity) instances -/
section with_top

example (R : Type*) [h : strict_ordered_semiring R] :
  (@with_top.add_comm_monoid R
    (@non_unital_non_assoc_semiring.to_add_comm_monoid R
      (@non_assoc_semiring.to_non_unital_non_assoc_semiring R
        (@semiring.to_non_assoc_semiring R
          (@strict_ordered_semiring.to_semiring R h)))))
        =
  (@ordered_add_comm_monoid.to_add_comm_monoid (with_top R)
    (@with_top.ordered_add_comm_monoid R
      (@ordered_cancel_add_comm_monoid.to_ordered_add_comm_monoid R
        (@strict_ordered_semiring.to_ordered_cancel_add_comm_monoid R h)))) :=
rfl

end with_top

/-! ## `multiplicative` instances -/
section multiplicative

example :
  @monoid.to_mul_one_class (multiplicative ℕ) (comm_monoid.to_monoid _) =
    multiplicative.mul_one_class :=
rfl

-- `dunfold` can still break unification, but it's better to have `dunfold` break it than have the
-- above example fail.
example :
  @monoid.to_mul_one_class (multiplicative ℕ) (comm_monoid.to_monoid _) =
    multiplicative.mul_one_class :=
begin
  dunfold has_one.one multiplicative.mul_one_class,
  success_if_fail { refl, },
  ext,
  refl
end

end multiplicative

/-! ## `finsupp` instances-/

section finsupp
open finsupp

/-- `finsupp.comap_has_smul` can form a non-equal diamond with `finsupp.smul_zero_class` -/
example {k : Type*} [semiring k] [nontrivial k] :
  (finsupp.comap_has_smul : has_smul k (k →₀ k)) ≠ finsupp.smul_zero_class.to_has_smul :=
begin
  obtain ⟨u : k, hu⟩ := exists_ne (1 : k),
  intro h,
  simp only [has_smul.ext_iff, function.funext_iff, finsupp.ext_iff] at h,
  replace h := h u (finsupp.single 1 1) u,
  classical,
  rw [comap_smul_single, smul_apply, smul_eq_mul, mul_one, single_eq_same,
    smul_eq_mul, single_eq_of_ne hu.symm, mul_zero] at h,
  exact one_ne_zero h,
end

/-- `finsupp.comap_has_smul` can form a non-equal diamond with `finsupp.smul_zero_class` even when
the domain is a group. -/
example {k : Type*} [semiring k] [nontrivial kˣ] :
  (finsupp.comap_has_smul : has_smul kˣ (kˣ →₀ k)) ≠ finsupp.smul_zero_class.to_has_smul :=
begin
  obtain ⟨u : kˣ, hu⟩ := exists_ne (1 : kˣ),
  haveI : nontrivial k := ⟨⟨u, 1, units.ext.ne hu⟩⟩,
  intro h,
  simp only [has_smul.ext_iff, function.funext_iff, finsupp.ext_iff] at h,
  replace h := h u (finsupp.single 1 1) u,
  classical,
  rw [comap_smul_single, smul_apply, units.smul_def, smul_eq_mul, mul_one, single_eq_same,
    smul_eq_mul, single_eq_of_ne hu.symm, mul_zero] at h,
  exact one_ne_zero h,
end

end finsupp

/-! ## `polynomial` instances -/
section polynomial

variables (R A : Type*)
open_locale polynomial
open polynomial

/-- `polynomial.has_smul_pi` forms a diamond with `pi.has_smul`. -/
example [semiring R] [nontrivial R] :
  polynomial.has_smul_pi _ _ ≠ (pi.has_smul : has_smul R[X] (R → R[X])) :=
begin
  intro h,
  simp_rw [has_smul.ext_iff, function.funext_iff, polynomial.ext_iff] at h,
  simpa using h X 1 1 0,
end

/-- `polynomial.has_smul_pi'` forms a diamond with `pi.has_smul`. -/
example [comm_semiring R] [nontrivial R] :
  polynomial.has_smul_pi' _ _ _ ≠ (pi.has_smul : has_smul R[X] (R → R[X])) :=
begin
  intro h,
  simp_rw [has_smul.ext_iff, function.funext_iff, polynomial.ext_iff] at h,
  simpa using h X 1 1 0,
end

/-- `polynomial.has_smul_pi'` is consistent with `polynomial.has_smul_pi`. -/
example [comm_semiring R] [nontrivial R] :
  polynomial.has_smul_pi' _ _ _ = (polynomial.has_smul_pi _ _ : has_smul R[X] (R → R[X])) :=
rfl

/-- `polynomial.algebra_of_algebra` is consistent with `algebra_nat`. -/
example [semiring R] : (polynomial.algebra_of_algebra : algebra ℕ R[X]) = algebra_nat := rfl

/-- `polynomial.algebra_of_algebra` is consistent with `algebra_int`. -/
example [ring R] : (polynomial.algebra_of_algebra : algebra ℤ R[X]) = algebra_int _ := rfl

end polynomial

/-! ## `subtype` instances -/
section subtype

-- this diamond is the reason that `fintype.to_locally_finite_order` is not an instance
example {α} [preorder α] [locally_finite_order α] [fintype α] [@decidable_rel α (<)]
  [@decidable_rel α (≤)] (p : α → Prop) [decidable_pred p] :
  subtype.locally_finite_order p = fintype.to_locally_finite_order :=
begin
  success_if_fail { refl, },
  exact subsingleton.elim _ _
end

end subtype

/-! ## `zmod` instances -/
section zmod

variables {p : ℕ} [fact p.prime]

example : @euclidean_domain.to_comm_ring _ (@field.to_euclidean_domain _ (zmod.field p)) =
  zmod.comm_ring p :=
rfl

example (n : ℕ) : zmod.comm_ring (n + 1) = fin.comm_ring (n + 1) := rfl
example : zmod.comm_ring 0 = int.comm_ring := rfl

end zmod

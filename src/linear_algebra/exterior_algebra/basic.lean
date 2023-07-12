/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhangir Azerbayev, Adam Topaz, Eric Wieser
-/

import linear_algebra.clifford_algebra.basic
import linear_algebra.alternating

/-!
# Exterior Algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We construct the exterior algebra of a module `M` over a commutative semiring `R`.

## Notation

The exterior algebra of the `R`-module `M` is denoted as `exterior_algebra R M`.
It is endowed with the structure of an `R`-algebra.

Given a linear morphism `f : M → A` from a module `M` to another `R`-algebra `A`, such that
`cond : ∀ m : M, f m * f m = 0`, there is a (unique) lift of `f` to an `R`-algebra morphism,
which is denoted `exterior_algebra.lift R f cond`.

The canonical linear map `M → exterior_algebra R M` is denoted `exterior_algebra.ι R`.

## Theorems

The main theorems proved ensure that `exterior_algebra R M` satisfies the universal property
of the exterior algebra.
1. `ι_comp_lift` is  fact that the composition of `ι R` with `lift R f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift R f cond` with respect to 1.

## Definitions

* `ι_multi` is the `alternating_map` corresponding to the wedge product of `ι R m` terms.

## Implementation details

The exterior algebra of `M` is constructed as simply `clifford_algebra (0 : quadratic_form R M)`,
as this avoids us having to duplicate API.
-/

universes u1 u2 u3

variables (R : Type u1) [comm_ring R]
variables (M : Type u2) [add_comm_group M] [module R M]

/--
The exterior algebra of an `R`-module `M`.
-/
@[reducible]
def exterior_algebra := clifford_algebra (0 : quadratic_form R M)

namespace exterior_algebra

variables {M}

/--
The canonical linear map `M →ₗ[R] exterior_algebra R M`.
-/
@[reducible] def ι : M →ₗ[R] exterior_algebra R M := by exact clifford_algebra.ι _

variables {R}

/-- As well as being linear, `ι m` squares to zero -/
@[simp]
theorem ι_sq_zero (m : M) : (ι R m) * (ι R m) = 0 :=
(clifford_algebra.ι_sq_scalar _ m).trans $ map_zero _

variables {A : Type*} [semiring A] [algebra R A]

@[simp]
theorem comp_ι_sq_zero (g : exterior_algebra R M →ₐ[R] A)
  (m : M) : g (ι R m) * g (ι R m) = 0 :=
by rw [←alg_hom.map_mul, ι_sq_zero, alg_hom.map_zero]

variables (R)

/--
Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = 0`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `exterior_algebra R M` to `A`.
-/
@[simps symm_apply]
def lift : {f : M →ₗ[R] A // ∀ m, f m * f m = 0} ≃ (exterior_algebra R M →ₐ[R] A) :=
equiv.trans (equiv.subtype_equiv (equiv.refl _) $ by simp) $ clifford_algebra.lift _

@[simp]
theorem ι_comp_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) :
  (lift R ⟨f, cond⟩).to_linear_map.comp (ι R) = f :=
clifford_algebra.ι_comp_lift f _

@[simp]
theorem lift_ι_apply (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) (x) :
  lift R ⟨f, cond⟩ (ι R x) = f x :=
clifford_algebra.lift_ι_apply f _ x

@[simp]
theorem lift_unique (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0)
  (g : exterior_algebra R M →ₐ[R] A) : g.to_linear_map.comp (ι R) = f ↔ g = lift R ⟨f, cond⟩ :=
clifford_algebra.lift_unique f _ _

variables {R M}

@[simp]
theorem lift_comp_ι (g : exterior_algebra R M →ₐ[R] A) :
  lift R ⟨g.to_linear_map.comp (ι R), comp_ι_sq_zero _⟩ = g :=
clifford_algebra.lift_comp_ι g

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext {f g : exterior_algebra R M →ₐ[R] A}
  (h : f.to_linear_map.comp (ι R) = g.to_linear_map.comp (ι R)) : f = g :=
clifford_algebra.hom_ext h

/-- If `C` holds for the `algebra_map` of `r : R` into `exterior_algebra R M`, the `ι` of `x : M`,
and is preserved under addition and muliplication, then it holds for all of `exterior_algebra R M`.
-/
@[elab_as_eliminator]
lemma induction {C : exterior_algebra R M → Prop}
  (h_grade0 : ∀ r, C (algebra_map R (exterior_algebra R M) r))
  (h_grade1 : ∀ x, C (ι R x))
  (h_mul : ∀ a b, C a → C b → C (a * b))
  (h_add : ∀ a b, C a → C b → C (a + b))
  (a : exterior_algebra R M) :
  C a :=
clifford_algebra.induction h_grade0 h_grade1 h_mul h_add a

/-- The left-inverse of `algebra_map`. -/
def algebra_map_inv : exterior_algebra R M →ₐ[R] R :=
exterior_algebra.lift R ⟨(0 : M →ₗ[R] R), λ m, by simp⟩

variables (M)

lemma algebra_map_left_inverse :
  function.left_inverse algebra_map_inv (algebra_map R $ exterior_algebra R M) :=
λ x, by simp [algebra_map_inv]

@[simp] lemma algebra_map_inj (x y : R) :
  algebra_map R (exterior_algebra R M) x = algebra_map R (exterior_algebra R M) y ↔ x = y :=
(algebra_map_left_inverse M).injective.eq_iff

@[simp] lemma algebra_map_eq_zero_iff (x : R) :
  algebra_map R (exterior_algebra R M) x = 0 ↔ x = 0 :=
map_eq_zero_iff (algebra_map _ _) (algebra_map_left_inverse _).injective

@[simp] lemma algebra_map_eq_one_iff (x : R) : algebra_map R (exterior_algebra R M) x = 1 ↔ x = 1 :=
map_eq_one_iff (algebra_map _ _) (algebra_map_left_inverse _).injective

lemma is_unit_algebra_map (r : R) : is_unit (algebra_map R (exterior_algebra R M) r) ↔ is_unit r :=
is_unit_map_of_left_inverse _ (algebra_map_left_inverse M)

/-- Invertibility in the exterior algebra is the same as invertibility of the base ring. -/
@[simps]
def invertible_algebra_map_equiv (r : R) :
  invertible (algebra_map R (exterior_algebra R M) r) ≃ invertible r :=
invertible_equiv_of_left_inverse _ _ _ (algebra_map_left_inverse M)

variables {M}

/-- The canonical map from `exterior_algebra R M` into `triv_sq_zero_ext R M` that sends
`exterior_algebra.ι` to `triv_sq_zero_ext.inr`. -/
def to_triv_sq_zero_ext [module Rᵐᵒᵖ M] [is_central_scalar R M] :
  exterior_algebra R M →ₐ[R] triv_sq_zero_ext R M :=
lift R ⟨triv_sq_zero_ext.inr_hom R M, λ m, triv_sq_zero_ext.inr_mul_inr R m m⟩

@[simp] lemma to_triv_sq_zero_ext_ι [module Rᵐᵒᵖ M] [is_central_scalar R M] (x : M) :
  to_triv_sq_zero_ext (ι R x) = triv_sq_zero_ext.inr x :=
lift_ι_apply _ _ _ _

/-- The left-inverse of `ι`.

As an implementation detail, we implement this using `triv_sq_zero_ext` which has a suitable
algebra structure. -/
def ι_inv : exterior_algebra R M →ₗ[R] M :=
begin
  letI : module Rᵐᵒᵖ M := module.comp_hom _ ((ring_hom.id R).from_opposite mul_comm),
  haveI : is_central_scalar R M := ⟨λ r m, rfl⟩,
  exact (triv_sq_zero_ext.snd_hom R M).comp to_triv_sq_zero_ext.to_linear_map
end

lemma ι_left_inverse : function.left_inverse ι_inv (ι R : M → exterior_algebra R M) :=
λ x, by simp [ι_inv]

variables (R)

@[simp] lemma ι_inj (x y : M) : ι R x = ι R y ↔ x = y :=
ι_left_inverse.injective.eq_iff

variables {R}

@[simp] lemma ι_eq_zero_iff (x : M) : ι R x = 0 ↔ x = 0 :=
by rw [←ι_inj R x 0, linear_map.map_zero]

@[simp] lemma ι_eq_algebra_map_iff (x : M) (r : R) : ι R x = algebra_map R _ r ↔ x = 0 ∧ r = 0 :=
begin
  refine ⟨λ h, _, _⟩,
  { letI : module Rᵐᵒᵖ M := module.comp_hom _ ((ring_hom.id R).from_opposite mul_comm),
    haveI : is_central_scalar R M := ⟨λ r m, rfl⟩,
    have hf0 : to_triv_sq_zero_ext (ι R x) = (0, x), from to_triv_sq_zero_ext_ι _,
    rw [h, alg_hom.commutes] at hf0,
    have : r = 0 ∧ 0 = x := prod.ext_iff.1 hf0,
    exact this.symm.imp_left eq.symm, },
  { rintro ⟨rfl, rfl⟩,
    rw [linear_map.map_zero, ring_hom.map_zero] }
end

@[simp] lemma ι_ne_one [nontrivial R] (x : M) : ι R x ≠ 1 :=
begin
  rw [←(algebra_map R (exterior_algebra R M)).map_one, ne.def, ι_eq_algebra_map_iff],
  exact one_ne_zero ∘ and.right,
end

/-- The generators of the exterior algebra are disjoint from its scalars. -/
lemma ι_range_disjoint_one :
  disjoint (linear_map.range (ι R : M →ₗ[R] exterior_algebra R M))
    (1 : submodule R (exterior_algebra R M)) :=
begin
  rw submodule.disjoint_def,
  rintros _ ⟨x, hx⟩ ⟨r, (rfl : algebra_map _ _ _ = _)⟩,
  rw ι_eq_algebra_map_iff x at hx,
  rw [hx.2, ring_hom.map_zero]
end

@[simp]
lemma ι_add_mul_swap (x y : M) : ι R x * ι R y + ι R y * ι R x = 0 :=
calc _ = ι R (x + y) * ι R (x + y) : by simp [mul_add, add_mul]
   ... = _ : ι_sq_zero _

lemma ι_mul_prod_list {n : ℕ} (f : fin n → M) (i : fin n) :
  (ι R $ f i) * (list.of_fn $ λ i, ι R $ f i).prod = 0 :=
begin
  induction n with n hn,
  { exact i.elim0, },
  { rw [list.of_fn_succ, list.prod_cons, ←mul_assoc],
    by_cases h : i = 0,
    { rw [h, ι_sq_zero, zero_mul], },
    { replace hn := congr_arg ((*) $ ι R $ f 0) (hn (λ i, f $ fin.succ i) (i.pred h)),
      simp only at hn,
      rw [fin.succ_pred, ←mul_assoc, mul_zero] at hn,
      refine (eq_zero_iff_eq_zero_of_add_eq_zero _).mp hn,
      rw [← add_mul, ι_add_mul_swap, zero_mul], } }
end

variables (R)
/-- The product of `n` terms of the form `ι R m` is an alternating map.

This is a special case of `multilinear_map.mk_pi_algebra_fin`, and the exterior algebra version of
`tensor_algebra.tprod`. -/
def ι_multi (n : ℕ) : alternating_map R M (exterior_algebra R M) (fin n) :=
let F := (multilinear_map.mk_pi_algebra_fin R n (exterior_algebra R M)).comp_linear_map (λ i, ι R)
in
{ map_eq_zero_of_eq' := λ f x y hfxy hxy, begin
    rw [multilinear_map.comp_linear_map_apply, multilinear_map.mk_pi_algebra_fin_apply],
    clear F,
    wlog h : x < y,
    { exact this n f y x hfxy.symm hxy.symm (hxy.lt_or_lt.resolve_left h), },
    clear hxy,
    induction n with n hn,
    { exact x.elim0, },
    { rw [list.of_fn_succ, list.prod_cons],
      by_cases hx : x = 0,
      -- one of the repeated terms is on the left
      { rw hx at hfxy h,
        rw [hfxy, ←fin.succ_pred y (ne_of_lt h).symm],
        exact ι_mul_prod_list (f ∘ fin.succ) _, },
      -- ignore the left-most term and induct on the remaining ones, decrementing indices
      { convert mul_zero _,
        refine hn (λ i, f $ fin.succ i)
          (x.pred hx) (y.pred (ne_of_lt $ lt_of_le_of_lt x.zero_le h).symm) _
          (fin.pred_lt_pred_iff.mpr h),
        simp only [fin.succ_pred],
        exact hfxy, } }
  end,
  to_fun := F, ..F}
variables {R}

lemma ι_multi_apply {n : ℕ} (v : fin n → M) :
  ι_multi R n v = (list.of_fn $ λ i, ι R (v i)).prod := rfl

@[simp] lemma ι_multi_zero_apply (v : fin 0 → M) : ι_multi R 0 v = 1 := rfl

@[simp] lemma ι_multi_succ_apply {n : ℕ} (v : fin n.succ → M) :
  ι_multi R _ v = ι R (v 0) * ι_multi R _ (matrix.vec_tail v):=
(congr_arg list.prod (list.of_fn_succ _)).trans list.prod_cons

lemma ι_multi_succ_curry_left {n : ℕ} (m : M) :
  (ι_multi R n.succ).curry_left m =
    (linear_map.mul_left R (ι R m)).comp_alternating_map (ι_multi R n) :=
alternating_map.ext $ λ v, (ι_multi_succ_apply _).trans $ begin
  simp_rw matrix.tail_cons,
  refl,
end

end exterior_algebra

namespace tensor_algebra

variables {R M}

/-- The canonical image of the `tensor_algebra` in the `exterior_algebra`, which maps
`tensor_algebra.ι R x` to `exterior_algebra.ι R x`. -/
def to_exterior : tensor_algebra R M →ₐ[R] exterior_algebra R M :=
tensor_algebra.lift R (exterior_algebra.ι R : M →ₗ[R] exterior_algebra R M)

@[simp] lemma to_exterior_ι (m : M) : (tensor_algebra.ι R m).to_exterior = exterior_algebra.ι R m :=
by simp [to_exterior]

end tensor_algebra

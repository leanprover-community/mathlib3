/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import algebra.algebra.basic
import algebra.non_unital_alg_hom

/-!
# Unitization of a non-unital algebra

Given a non-unital `R`-algebra `A` (given via the type classes
`[non_unital_ring A] [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]`) we construct
the minimal unital `R`-algebra containing `A` as an ideal. This object `algebra.unitization R A` is
a type synonym for `R × A` on which we place a different multiplicative structure, namely,
`(r₁, a₁) * (r₂, a₂) = (r₁ * r₂, r₁ • a₂ + r₂ • a₁ + a₁ * a₂)` where the multiplicative identity
is `(1, 0)`.

Note, when `A` is a *unital* `R`-algebra, then `unitization R A` constructs a new multiplicative
identity different from the old one, and so in general `unitization R A` and `A` will not be
isomorphic even in the unital case. This approach actually has nice functorial properties.

There is a natural coercion from `A` to `algebra.unitization R A` given by `λ a, (0, a)`, the image
of which is a proper ideal (TODO), and when `R` is a field this ideal is maximal. Moreover,
this ideal is always an essential ideal (it has nontrivial intersection with every other nontrivial
ideal).

Every non-unital algebra homomorphism from `A` into a *unital* `R`-algebra `B` has a unique
extension to a (unital) algebra homomorphism from `algebra.unitization R A` to `B`.

## Main definitions

* `algebra.unitization R A`: the unitization of a non-unital `R`-algebra `A`.
* `unitization.algebra`: the unitization of `A` as a (unital) `R`-algebra.
* `unitization.coe_non_unital_alg_hom`: coercion as a non-unital algebra homomorphism.
* `non_unital_alg_hom.to_alg_hom φ`: the extension of a non-unital algebra homomorphism `φ : A → B`
  into a unital `R`-algebra `B` to an algebra homomorphism `algebra.unitization R A →ₐ[R] B`.

## Main results

* `non_unital_alg_hom.to_alg_hom_unique`: the extension is unique

## TODO

* prove the unitization operation is a functor between the appropriate categories
* prove the image of the coercion is an essential ideal, maximal if scalars are a field.
-/

def algebra.unitization (R A : Type*) [comm_ring R] [non_unital_ring A] := R × A

variables {R A : Type*} [comm_ring R] [non_unital_ring A]

open algebra

def to_unitization : R × A ≃ unitization R A := equiv.refl _

namespace unitization

instance : has_coe A (unitization R A) := { coe := λ a, to_unitization (0, a) }

@[simp]
lemma coe_apply (a : A) : (↑a : unitization R A) = to_unitization (0, a) := rfl

lemma coe_injective : function.injective (coe : A → unitization R A) := λ a₁ a₂, by simp

lemma decomp (x : unitization R A) : ∃ r a, x = to_unitization (r, a) :=
⟨(to_unitization.symm x).1, (to_unitization.symm x).2,
  by simp only [prod.mk.eta, equiv.apply_symm_apply]⟩

instance : add_comm_group (unitization R A) := prod.add_comm_group
instance [module R A] : module R (unitization R A) := prod.module

instance : has_one (unitization R A) := { one := to_unitization (1, 0) }
instance [module R A] : has_mul (unitization R A) :=
{ mul := λ ra₁ ra₂, (ra₁.1 * ra₂.1, ra₁.1 • ra₂.2 + ra₂.1 • ra₁.2 + ra₁.2 * ra₂.2) }

@[simp]
lemma one_def : (1 : unitization R A) = to_unitization (1, 0) := rfl

@[simp]
lemma mul_def [module R A] (r₁ r₂ : R) (a₁ a₂ : A) :
  to_unitization (r₁, a₁) * to_unitization (r₂, a₂) =
  to_unitization (r₁ * r₂, r₁ • a₂ + r₂ • a₁ + a₁ * a₂) :=
rfl

@[simp]
lemma smul_def [module R A] (r s : R) (a : A) :
  r • to_unitization (s, a) = to_unitization (r • s, r • a) := rfl

@[simp]
lemma add_def (r₁ r₂ : R) (a₁ a₂ : A) :
  to_unitization (r₁, a₁) + to_unitization (r₂, a₂) = to_unitization (r₁ + r₂, a₁ + a₂) := rfl

@[simp]
lemma to_unitization_symm_zero : to_unitization.symm (0 : unitization R A) = (0, 0) := rfl

instance [module R A] [is_scalar_tower R A A] [smul_comm_class R A A] :
  ring (unitization R A) :=
{ mul_assoc :=
  begin
    intros a b c,
    obtain ⟨⟨r, a, rfl⟩, ⟨s, b, rfl⟩, ⟨t, c, rfl⟩⟩ := ⟨decomp a, decomp b, decomp c⟩,
    rw [mul_def, mul_def, mul_def, mul_def],
    rw [mul_assoc],
    simp only [smul_add, prod.mk.inj_iff, eq_self_iff_true, true_and],
    rw [smul_smul r s c, smul_algebra_smul_comm t r b],
    simp only [right_distrib _ _ c, left_distrib a _ _],
    rw [smul_smul t s a, mul_comm t s, mul_assoc a b c, mul_smul_comm t a b, smul_mul_assoc r b c,
    mul_smul_comm s a c, smul_mul_assoc s a c],
    refine congr_arg to_unitization _,
    ac_refl,
  end,
  one_mul := by { intro a, rcases decomp a with ⟨r, a, rfl⟩, simp },
  mul_one := by { intro a, rcases decomp a with ⟨r, a, rfl⟩, simp },
  left_distrib :=
  begin
    intros a b c,
    obtain ⟨⟨r, a, rfl⟩, ⟨s, b, rfl⟩, ⟨t, c, rfl⟩⟩ := ⟨decomp a, decomp b, decomp c⟩,
    rw [add_def, mul_def, mul_def, mul_def, add_def],
    simp only [mul_def, left_distrib, smul_add, add_smul],
    abel,
  end,
  right_distrib :=
  begin
    intros a b c,
    obtain ⟨⟨r, a, rfl⟩, ⟨s, b, rfl⟩, ⟨t, c, rfl⟩⟩ := ⟨decomp a, decomp b, decomp c⟩,
    rw [add_def, mul_def, mul_def, mul_def, add_def],
    simp only [mul_def, right_distrib, smul_add, add_smul],
    abel,
  end,
  ..unitization.has_one,
  ..unitization.has_mul,
  ..unitization.add_comm_group }


variables [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]

instance : algebra R (unitization R A) :=
{ to_fun := λ r, to_unitization (r, 0),
  map_one' := rfl,
  map_mul' := λ x y, by simp,
  map_zero' := rfl,
  map_add' := λ x y, by simp,
  commutes' := λ r sa, by
    { rcases decomp sa with ⟨s, a, rfl⟩,
      simp only [mul_comm, mul_def, smul_zero, add_zero, mul_zero, zero_mul, zero_add] },
  smul_def' := λ r sa,
  begin
    rcases decomp sa with ⟨s, a, rfl⟩,
    simp only [mul_def, smul_zero, add_zero, zero_mul],
    refl,
  end,
  ..unitization.module }

@[simps]
def coe_non_unital_alg_hom : non_unital_alg_hom R A (unitization R A) :=
{ to_fun := coe,
  map_smul' := by simp,
  map_zero' := rfl,
  map_add' := by simp,
  map_mul' := by simp }

lemma decomp' (x : unitization R A) :
  ∃ r (a : A), x = algebra_map R (unitization R A) r + a :=
by { rcases decomp x with ⟨r, a, rfl⟩, exact ⟨r, a, by simp [algebra_map_eq_smul_one]⟩ }

end unitization

open unitization

variables
[module R A] [smul_comm_class R A A] [is_scalar_tower R A A]
{B : Type*} [ring B] [algebra R B]

@[simps]
def non_unital_alg_hom.to_alg_hom (φ : non_unital_alg_hom R A B) : (unitization R A) →ₐ[R] B :=
{ to_fun := λ ra, algebra_map R B (to_unitization.symm ra).1 + φ (to_unitization.symm ra).2,
  map_one' := by simp,
  map_mul' :=
  begin
    intros a b,
    obtain ⟨⟨r, a, rfl⟩, ⟨s, b, rfl⟩⟩ := ⟨decomp a, decomp b⟩,
    simp only [mul_def, equiv.symm_apply_apply, map_mul, φ.map_add, φ.map_smul, φ.map_mul,
      left_distrib, right_distrib],
    rw ←algebra.commutes s (φ a),
    simp only [algebra.algebra_map_eq_smul_one, smul_one_mul, φ.map_smul],
    ac_refl,
  end,
  map_zero' := by simp,
  map_add' :=
  begin
    intros a b,
    obtain ⟨⟨r, a, rfl⟩, ⟨s, b, rfl⟩⟩ := ⟨decomp a, decomp b⟩,
    simp only [add_def, equiv.symm_apply_apply, map_add, non_unital_alg_hom.map_add],
    rw add_add_add_comm,
  end,
  commutes' := λ r, by simp [algebra.algebra_map_eq_smul_one] }

local postfix `¹`:std.prec.max_plus := non_unital_alg_hom.to_alg_hom

lemma non_unital_alg_hom.to_alg_hom_apply_coe (φ : non_unital_alg_hom R A B) (a : A) :
  φ¹ a = φ a :=
by simp only [coe_apply, φ.to_alg_hom_apply, equiv.symm_apply_apply, map_zero, zero_add]

lemma non_unital_alg_hom.to_alg_hom_unique (φ : non_unital_alg_hom R A B)
  (ψ : unitization R A →ₐ[R] B) (h : ∀ a : A, ψ a = φ¹ a) : ψ = φ¹ :=
begin
  ext,
  rcases decomp' x with ⟨r, a, rfl⟩,
  simp only [map_add, h, alg_hom.commutes],
end

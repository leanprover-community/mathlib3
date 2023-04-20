/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import algebra.hom.equiv.type_tags
import algebra.module.equiv
import data.finsupp.defs
import group_theory.free_abelian_group
import group_theory.is_free_group
import linear_algebra.dimension

/-!
# Isomorphism between `free_abelian_group X` and `X →₀ ℤ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we construct the canonical isomorphism between `free_abelian_group X` and `X →₀ ℤ`.
We use this to transport the notion of `support` from `finsupp` to `free_abelian_group`.

## Main declarations

- `free_abelian_group.equiv_finsupp`: group isomorphism between `free_abelian_group X` and `X →₀ ℤ`
- `free_abelian_group.coeff`: the multiplicity of `x : X` in `a : free_abelian_group X`
- `free_abelian_group.support`: the finset of `x : X` that occur in `a : free_abelian_group X`

-/

noncomputable theory

open_locale big_operators

variables {X : Type*}

/-- The group homomorphism `free_abelian_group X →+ (X →₀ ℤ)`. -/
def free_abelian_group.to_finsupp : free_abelian_group X →+ (X →₀ ℤ) :=
free_abelian_group.lift $ λ x, finsupp.single x (1 : ℤ)

/-- The group homomorphism `(X →₀ ℤ) →+ free_abelian_group X`. -/
def finsupp.to_free_abelian_group : (X →₀ ℤ) →+ free_abelian_group X :=
finsupp.lift_add_hom $ λ x, (smul_add_hom ℤ (free_abelian_group X)).flip (free_abelian_group.of x)

open finsupp free_abelian_group

@[simp] lemma finsupp.to_free_abelian_group_comp_single_add_hom (x : X) :
  finsupp.to_free_abelian_group.comp (finsupp.single_add_hom x) =
    (smul_add_hom ℤ (free_abelian_group X)).flip (of x) :=
begin
  ext,
  simp only [add_monoid_hom.coe_comp, finsupp.single_add_hom_apply, function.comp_app,
    one_smul, to_free_abelian_group, finsupp.lift_add_hom_apply_single]
end

@[simp] lemma free_abelian_group.to_finsupp_comp_to_free_abelian_group :
  to_finsupp.comp to_free_abelian_group = add_monoid_hom.id (X →₀ ℤ) :=
begin
  ext x y, simp only [add_monoid_hom.id_comp],
  rw [add_monoid_hom.comp_assoc, finsupp.to_free_abelian_group_comp_single_add_hom],
  simp only [to_finsupp, add_monoid_hom.coe_comp, finsupp.single_add_hom_apply,
    function.comp_app, one_smul, lift.of, add_monoid_hom.flip_apply,
    smul_add_hom_apply, add_monoid_hom.id_apply],
end

@[simp] lemma finsupp.to_free_abelian_group_comp_to_finsupp :
  to_free_abelian_group.comp to_finsupp = add_monoid_hom.id (free_abelian_group X) :=
begin
  ext,
  rw [to_free_abelian_group, to_finsupp, add_monoid_hom.comp_apply, lift.of,
    lift_add_hom_apply_single, add_monoid_hom.flip_apply, smul_add_hom_apply, one_smul,
    add_monoid_hom.id_apply],
end

@[simp] lemma finsupp.to_free_abelian_group_to_finsupp {X} (x : free_abelian_group X) :
  x.to_finsupp.to_free_abelian_group = x :=
by rw [← add_monoid_hom.comp_apply, finsupp.to_free_abelian_group_comp_to_finsupp,
  add_monoid_hom.id_apply]

namespace free_abelian_group
open finsupp

variable {X}

@[simp] lemma to_finsupp_of (x : X) :
  to_finsupp (of x) = finsupp.single x 1 :=
by simp only [to_finsupp, lift.of]

@[simp] lemma to_finsupp_to_free_abelian_group (f : X →₀ ℤ) :
  f.to_free_abelian_group.to_finsupp = f :=
by rw [← add_monoid_hom.comp_apply, to_finsupp_comp_to_free_abelian_group, add_monoid_hom.id_apply]

variable (X)

/-- The additive equivalence between `free_abelian_group X` and `(X →₀ ℤ)`. -/
@[simps]
def equiv_finsupp : free_abelian_group X ≃+ (X →₀ ℤ) :=
{ to_fun := to_finsupp,
  inv_fun := to_free_abelian_group,
  left_inv := to_free_abelian_group_to_finsupp,
  right_inv := to_finsupp_to_free_abelian_group,
  map_add' := to_finsupp.map_add }

/-- `A` is a basis of the ℤ-module `free_abelian_group A`. -/
noncomputable def basis (α : Type*) :
  basis α ℤ (free_abelian_group α) :=
⟨(free_abelian_group.equiv_finsupp α).to_int_linear_equiv ⟩

/-- Isomorphic free ablian groups (as modules) have equivalent bases. -/
def equiv.of_free_abelian_group_linear_equiv {α β : Type*}
  (e : free_abelian_group α ≃ₗ[ℤ] free_abelian_group β) :
  α ≃ β :=
let t : _root_.basis α ℤ (free_abelian_group β) := (free_abelian_group.basis α).map e
  in t.index_equiv $ free_abelian_group.basis _

/-- Isomorphic free abelian groups (as additive groups) have equivalent bases. -/
def equiv.of_free_abelian_group_equiv {α β : Type*}
  (e : free_abelian_group α ≃+ free_abelian_group β) :
  α ≃ β :=
equiv.of_free_abelian_group_linear_equiv e.to_int_linear_equiv

/-- Isomorphic free groups have equivalent bases. -/
def equiv.of_free_group_equiv {α β : Type*}
  (e : free_group α ≃* free_group β) :
  α ≃ β :=
equiv.of_free_abelian_group_equiv e.abelianization_congr.to_additive

open is_free_group
/-- Isomorphic free groups have equivalent bases (`is_free_group` variant`). -/
def equiv.of_is_free_group_equiv {G H : Type*}
  [group G] [group H] [is_free_group G] [is_free_group H]
  (e : G ≃* H) :
  generators G ≃ generators H :=
equiv.of_free_group_equiv $
  mul_equiv.trans ((to_free_group G).symm) $
  mul_equiv.trans e $
  to_free_group H

variable {X}

/-- `coeff x` is the additive group homomorphism `free_abelian_group X →+ ℤ`
that sends `a` to the multiplicity of `x : X` in `a`. -/
def coeff (x : X) : free_abelian_group X →+ ℤ :=
(finsupp.apply_add_hom x).comp to_finsupp

/-- `support a` for `a : free_abelian_group X` is the finite set of `x : X`
that occur in the formal sum `a`. -/
def support (a : free_abelian_group X) : finset X :=
a.to_finsupp.support

lemma mem_support_iff (x : X) (a : free_abelian_group X) :
  x ∈ a.support ↔ coeff x a ≠ 0 :=
by { rw [support, finsupp.mem_support_iff], exact iff.rfl }

lemma not_mem_support_iff (x : X) (a : free_abelian_group X) :
  x ∉ a.support ↔ coeff x a = 0 :=
by { rw [support, finsupp.not_mem_support_iff], exact iff.rfl }

@[simp] lemma support_zero : support (0 : free_abelian_group X) = ∅ :=
by simp only [support, finsupp.support_zero, add_monoid_hom.map_zero]

@[simp] lemma support_of (x : X) : support (of x) = {x} :=
by simp only [support, to_finsupp_of, finsupp.support_single_ne_zero _ one_ne_zero]

@[simp] lemma support_neg (a : free_abelian_group X) : support (-a) = support a :=
by simp only [support, add_monoid_hom.map_neg, finsupp.support_neg]

@[simp] lemma support_zsmul (k : ℤ) (h : k ≠ 0) (a : free_abelian_group X) :
  support (k • a) = support a :=
begin
  ext x,
  simp only [mem_support_iff, add_monoid_hom.map_zsmul],
  simp only [h, zsmul_int_int, false_or, ne.def, mul_eq_zero]
end

@[simp] lemma support_nsmul (k : ℕ) (h : k ≠ 0) (a : free_abelian_group X) :
  support (k • a) = support a :=
by { apply support_zsmul k _ a, exact_mod_cast h }

open_locale classical

lemma support_add (a b : free_abelian_group X) : (support (a + b)) ⊆ a.support ∪ b.support :=
begin
  simp only [support, add_monoid_hom.map_add],
  apply finsupp.support_add
end

end free_abelian_group

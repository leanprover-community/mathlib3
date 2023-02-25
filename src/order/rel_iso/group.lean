/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.group.defs
import order.rel_iso.basic

/-!
# Relation isomorphisms form a group

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α: Type*}
  {r : α → α → Prop}

namespace rel_iso

instance : group (r ≃r r) :=
{ one := rel_iso.refl r,
  mul := λ f₁ f₂, f₂.trans f₁,
  inv := rel_iso.symm,
  mul_assoc := λ f₁ f₂ f₃, rfl,
  one_mul := λ f, ext $ λ _, rfl,
  mul_one := λ f, ext $ λ _, rfl,
  mul_left_inv := λ f, ext f.symm_apply_apply }

@[simp] lemma coe_one : ⇑(1 : r ≃r r) = id := rfl

@[simp] lemma coe_mul (e₁ e₂ : r ≃r r) : ⇑(e₁ * e₂) = e₁ ∘ e₂ := rfl

lemma mul_apply (e₁ e₂ : r ≃r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

@[simp] lemma inv_apply_self (e : r ≃r r) (x) : e⁻¹ (e x) = x := e.symm_apply_apply x

@[simp] lemma apply_inv_self (e : r ≃r r) (x) : e (e⁻¹ x) = x := e.apply_symm_apply x

end rel_iso

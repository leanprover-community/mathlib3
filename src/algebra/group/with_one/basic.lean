/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import algebra.group.with_one.defs
import algebra.hom.equiv.basic

/-!
# More operations on `with_one` and `with_zero`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines various bundled morphisms on `with_one` and `with_zero`
that were not available in `algebra/group/with_one/defs`.

## Main definitions

* `with_one.lift`, `with_zero.lift`
* `with_one.map`, `with_zero.map`
-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace with_one

section
-- workaround: we make `with_one`/`with_zero` irreducible for this definition, otherwise `simps`
-- will unfold it in the statement of the lemma it generates.
local attribute [irreducible] with_one with_zero
/-- `coe` as a bundled morphism -/
@[to_additive "`coe` as a bundled morphism", simps apply]
def coe_mul_hom [has_mul α] : α →ₙ* (with_one α) :=
{ to_fun := coe, map_mul' := λ x y, rfl }

end

section lift

local attribute [semireducible] with_one with_zero

variables [has_mul α] [mul_one_class β]

/-- Lift a semigroup homomorphism `f` to a bundled monoid homorphism. -/
@[to_additive "Lift an add_semigroup homomorphism `f` to a bundled add_monoid homorphism."]
def lift : (α →ₙ* β) ≃ (with_one α →* β) :=
{ to_fun := λ f,
  { to_fun := λ x, option.cases_on x 1 f,
    map_one' := rfl,
    map_mul' := λ x y,
      with_one.cases_on x (by { rw one_mul, exact (one_mul _).symm }) $ λ x,
      with_one.cases_on y (by { rw mul_one, exact (mul_one _).symm }) $ λ y,
      f.map_mul x y },
  inv_fun := λ F, F.to_mul_hom.comp coe_mul_hom,
  left_inv := λ f, mul_hom.ext $ λ x, rfl,
  right_inv := λ F, monoid_hom.ext $ λ x, with_one.cases_on x F.map_one.symm $ λ x, rfl }

variables (f : α →ₙ* β)

@[simp, to_additive]
lemma lift_coe (x : α) : lift f x = f x := rfl

@[simp, to_additive]
lemma lift_one : lift f 1 = 1 := rfl

@[to_additive]
theorem lift_unique (f : with_one α →* β) : f = lift (f.to_mul_hom.comp coe_mul_hom) :=
(lift.apply_symm_apply f).symm

end lift

section map

variables [has_mul α] [has_mul β] [has_mul γ]

/-- Given a multiplicative map from `α → β` returns a monoid homomorphism
  from `with_one α` to `with_one β` -/
@[to_additive "Given an additive map from `α → β` returns an add_monoid homomorphism
  from `with_zero α` to `with_zero β`"]
def map (f : α →ₙ* β) : with_one α →* with_one β :=
lift (coe_mul_hom.comp f)

@[simp, to_additive] lemma map_coe (f : α →ₙ* β) (a : α) : map f (a : with_one α) = f a :=
lift_coe _ _

@[simp, to_additive]
lemma map_id : map (mul_hom.id α) = monoid_hom.id (with_one α) :=
by { ext, induction x using with_one.cases_on; refl }

@[to_additive]
lemma map_map (f : α →ₙ* β) (g : β →ₙ* γ) (x) :
  map g (map f x) = map (g.comp f) x :=
by { induction x using with_one.cases_on; refl }

@[simp, to_additive]
lemma map_comp (f : α →ₙ* β) (g : β →ₙ* γ) :
  map (g.comp f) = (map g).comp (map f) :=
monoid_hom.ext $ λ x, (map_map f g x).symm

/-- A version of `equiv.option_congr` for `with_one`. -/
@[to_additive "A version of `equiv.option_congr` for `with_zero`.", simps apply]
def _root_.mul_equiv.with_one_congr (e : α ≃* β) : with_one α ≃* with_one β :=
{ to_fun := map e.to_mul_hom,
  inv_fun := map e.symm.to_mul_hom,
  left_inv := λ x, (map_map _ _ _).trans $ by induction x using with_one.cases_on; { simp },
  right_inv := λ x, (map_map _ _ _).trans $ by induction x using with_one.cases_on; { simp },
  .. map e.to_mul_hom }

@[simp]
lemma _root_.mul_equiv.with_one_congr_refl : (mul_equiv.refl α).with_one_congr = mul_equiv.refl _ :=
mul_equiv.to_monoid_hom_injective map_id

@[simp]
lemma _root_.mul_equiv.with_one_congr_symm (e : α ≃* β) :
  e.with_one_congr.symm = e.symm.with_one_congr := rfl

@[simp]
lemma _root_.mul_equiv.with_one_congr_trans (e₁ : α ≃* β) (e₂ : β ≃* γ) :
  e₁.with_one_congr.trans e₂.with_one_congr = (e₁.trans e₂).with_one_congr :=
mul_equiv.to_monoid_hom_injective (map_comp _ _).symm

end map

end with_one

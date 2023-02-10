/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import algebra.hom.equiv.basic
import algebra.group.type_tags

/-!
# Additive and multiplicative equivalences associated to `multiplicative` and `additive`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {G H : Type*}

/-- Reinterpret `G ≃+ H` as `multiplicative G ≃* multiplicative H`. -/
def add_equiv.to_multiplicative [add_zero_class G] [add_zero_class H] :
  (G ≃+ H) ≃ (multiplicative G ≃* multiplicative H) :=
{ to_fun := λ f, ⟨f.to_add_monoid_hom.to_multiplicative,
                  f.symm.to_add_monoid_hom.to_multiplicative, f.3, f.4, f.5⟩,
  inv_fun := λ f, ⟨f.to_monoid_hom, f.symm.to_monoid_hom, f.3, f.4, f.5⟩,
  left_inv := λ x, by { ext, refl, },
  right_inv := λ x, by { ext, refl, }, }

/-- Reinterpret `G ≃* H` as `additive G ≃+ additive H`. -/
def mul_equiv.to_additive [mul_one_class G] [mul_one_class H] :
  (G ≃* H) ≃ (additive G ≃+ additive H) :=
{ to_fun := λ f, ⟨f.to_monoid_hom.to_additive, f.symm.to_monoid_hom.to_additive, f.3, f.4, f.5⟩,
  inv_fun := λ f, ⟨f.to_add_monoid_hom, f.symm.to_add_monoid_hom, f.3, f.4, f.5⟩,
  left_inv := λ x, by { ext, refl, },
  right_inv := λ x, by { ext, refl, }, }

/-- Reinterpret `additive G ≃+ H` as `G ≃* multiplicative H`. -/
def add_equiv.to_multiplicative' [mul_one_class G] [add_zero_class H] :
  (additive G ≃+ H) ≃ (G ≃* multiplicative H) :=
{ to_fun := λ f, ⟨f.to_add_monoid_hom.to_multiplicative',
                  f.symm.to_add_monoid_hom.to_multiplicative'', f.3, f.4, f.5⟩,
  inv_fun := λ f, ⟨f.to_monoid_hom, f.symm.to_monoid_hom, f.3, f.4, f.5⟩,
  left_inv := λ x, by { ext, refl, },
  right_inv := λ x, by { ext, refl, }, }

/-- Reinterpret `G ≃* multiplicative H` as `additive G ≃+ H` as. -/
def mul_equiv.to_additive' [mul_one_class G] [add_zero_class H] :
  (G ≃* multiplicative H) ≃ (additive G ≃+ H) :=
add_equiv.to_multiplicative'.symm

/-- Reinterpret `G ≃+ additive H` as `multiplicative G ≃* H`. -/
def add_equiv.to_multiplicative'' [add_zero_class G] [mul_one_class H] :
  (G ≃+ additive H) ≃ (multiplicative G ≃* H) :=
{ to_fun := λ f, ⟨f.to_add_monoid_hom.to_multiplicative'',
                  f.symm.to_add_monoid_hom.to_multiplicative', f.3, f.4, f.5⟩,
  inv_fun := λ f, ⟨f.to_monoid_hom, f.symm.to_monoid_hom, f.3, f.4, f.5⟩,
  left_inv := λ x, by { ext, refl, },
  right_inv := λ x, by { ext, refl, }, }

/-- Reinterpret `multiplicative G ≃* H` as `G ≃+ additive H` as. -/
def mul_equiv.to_additive'' [add_zero_class G] [mul_one_class H] :
  (multiplicative G ≃* H) ≃ (G ≃+ additive H) :=
add_equiv.to_multiplicative''.symm

section
variables (G) (H)

/-- `additive (multiplicative G)` is just `G`. -/
def add_equiv.additive_multiplicative [add_zero_class G] : additive (multiplicative G) ≃+ G :=
mul_equiv.to_additive'' (mul_equiv.refl (multiplicative G))

/-- `multiplicative (additive H)` is just `H`. -/
def mul_equiv.multiplicative_additive [mul_one_class H] : multiplicative (additive H) ≃* H :=
add_equiv.to_multiplicative'' (add_equiv.refl (additive H))

end

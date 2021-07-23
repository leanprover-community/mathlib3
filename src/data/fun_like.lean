/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import tactic.lint
import tactic.norm_cast

/-!
# Typeclass for a type `F` with an injective map to `A → B`

This typeclass is primarily for use by homomorphisms like `monoid_hom` and `linear-map`.

A typical type of morphisms should be declared as:
```
structure my_hom (A B : Type*) [my_class A] [my_class B] :=
(to_fun : A → B)
(map_op' : ∀ {x y : A}, to_fun (my_class.op x y) = my_class.op (to_fun x) (to_fun y))

namespace my_hom

variables (A B : Type*) [my_class A] [my_class B]

instance : fun_like (my_hom A B) A B :=
{ coe := my_hom.to_fun, coe_injective' := λ f g h, by cases f; cases g; congr' }

@[simp] lemma to_fun_eq_coe {f : my_hom A B} : f.to_fun = (f : A → B) := rfl

@[ext] theorem ext {f g : my_hom A B} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

/-- Copy of a `my_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : my_hom A B) (f' : A → B) (h : f' = ⇑f) : my_hom A B :=
{ to_fun := f',
  map_op' := h.symm ▸ f.map_op' }

end my_hom
```

This file will then provide a `has_coe_to_fun` instance and various
extensionality and simp lemmas.

-/

/-- The class `fun_like F α β` expresses that terms of type `F` have an
injective coercion to functions from `α` to `β`.

This typeclass is used in the definition of the homomorphism typeclasses,
such as `zero_hom_class`, `mul_hom_class`, `monoid_hom_class`, ....
-/
class fun_like (F : Type*) (α β : out_param Type*) :=
(coe : F → (α → β))
(coe_injective' : function.injective coe)

variables {F α β : Type*}

namespace fun_like

variables [i : fun_like F α β]

include i

@[priority 100] -- see note [lower instance priority]
instance : has_coe_to_fun F (λ _, α → β) := { coe := fun_like.coe }

-- Unfortunately, the elaborator is not smart enough that we can write this as
-- `function.injective (coe_fn : F → α → β)`
theorem coe_injective ⦃f g : F⦄ (h : (f : α → β) = (g : α → β)) : f = g :=
fun_like.coe_injective' h

@[simp, norm_cast]
theorem coe_fn_eq {f g : F} : (f : α → β) = (g : α → β) ↔ f = g :=
⟨@@coe_injective i, λ h, by cases h; refl⟩

theorem ext' {f g : F} (h : (f : α → β) = (g : α → β)) : f = g :=
coe_injective h

theorem ext'_iff {f g : F} : f = g ↔ ((f : α → β) = (g : α → β)) :=
coe_fn_eq.symm

theorem ext (f g : F) (h : ∀ (x : α), f x = g x) : f = g :=
coe_injective (funext h)

theorem ext_iff {f g : F} : f = g ↔ (∀ x, f x = g x) :=
coe_fn_eq.symm.trans function.funext_iff

protected lemma congr {f g : F} {x y : α} (h₁ : f = g) (h₂ : x = y) : f x = g y :=
congr (congr_arg _ h₁) h₂

protected lemma congr_fun {f g : F} (h₁ : f = g) (x : α) : f x = g x :=
congr_fun (congr_arg _ h₁) x

protected lemma congr_arg (f : F) {x y : α} (h₂ : x = y) : f x = f y :=
congr_arg _ h₂

end fun_like

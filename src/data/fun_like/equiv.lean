/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import data.fun_like.embedding

/-!
# Typeclass for a type `F` with an injective map to `A ≃ B`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This typeclass is primarily for use by isomorphisms like `monoid_equiv` and `linear_equiv`.

## Basic usage of `equiv_like`

A typical type of morphisms should be declared as:
```
structure my_iso (A B : Type*) [my_class A] [my_class B]
  extends equiv A B :=
(map_op' : ∀ {x y : A}, to_fun (my_class.op x y) = my_class.op (to_fun x) (to_fun y))

namespace my_iso

variables (A B : Type*) [my_class A] [my_class B]

-- This instance is optional if you follow the "Isomorphism class" design below:
instance : equiv_like (my_iso A B) A (λ _, B) :=
{ coe := my_iso.to_equiv.to_fun,
  inv := my_iso.to_equiv.inv_fun,
  left_inv := my_iso.to_equiv.left_inv,
  right_inv := my_iso.to_equiv.right_inv,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

/-- Helper instance for when there's too many metavariables to apply `equiv_like.coe` directly. -/
instance : has_coe_to_fun (my_iso A B) := to_fun.to_coe_fn

@[simp] lemma to_fun_eq_coe {f : my_iso A B} : f.to_fun = (f : A → B) := rfl

@[ext] theorem ext {f g : my_iso A B} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

/-- Copy of a `my_iso` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : my_iso A B) (f' : A → B) (f_inv : B → A) (h : f' = ⇑f) : my_iso A B :=
{ to_fun := f',
  inv_fun := f_inv,
  left_inv := h.symm ▸ f.left_inv,
  right_inv := h.symm ▸ f.right_inv,
  map_op' := h.symm ▸ f.map_op' }

end my_iso
```

This file will then provide a `has_coe_to_fun` instance and various
extensionality and simp lemmas.

## Isomorphism classes extending `equiv_like`

The `equiv_like` design provides further benefits if you put in a bit more work.
The first step is to extend `equiv_like` to create a class of those types satisfying
the axioms of your new type of isomorphisms.
Continuing the example above:

```
section
set_option old_structure_cmd true

/-- `my_iso_class F A B` states that `F` is a type of `my_class.op`-preserving morphisms.
You should extend this class when you extend `my_iso`. -/
class my_iso_class (F : Type*) (A B : out_param $ Type*) [my_class A] [my_class B]
  extends equiv_like F A (λ _, B), my_hom_class F A B.

end

-- You can replace `my_iso.equiv_like` with the below instance:
instance : my_iso_class (my_iso A B) A B :=
{ coe := my_iso.to_fun,
  inv := my_iso.inv_fun,
  left_inv := my_iso.left_inv,
  right_inv := my_iso.right_inv,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_op := my_iso.map_op' }

-- [Insert `has_coe_to_fun`, `to_fun_eq_coe`, `ext` and `copy` here]
```

The second step is to add instances of your new `my_iso_class` for all types extending `my_iso`.
Typically, you can just declare a new class analogous to `my_iso_class`:

```
structure cooler_iso (A B : Type*) [cool_class A] [cool_class B]
  extends my_iso A B :=
(map_cool' : to_fun cool_class.cool = cool_class.cool)

section
set_option old_structure_cmd true

class cooler_iso_class (F : Type*) (A B : out_param $ Type*) [cool_class A] [cool_class B]
  extends my_iso_class F A B :=
(map_cool : ∀ (f : F), f cool_class.cool = cool_class.cool)

end

@[simp] lemma map_cool {F A B : Type*} [cool_class A] [cool_class B] [cooler_iso_class F A B]
  (f : F) : f cool_class.cool = cool_class.cool :=
my_iso_class.map_op

-- You can also replace `my_iso.equiv_like` with the below instance:
instance : cool_iso_class (cool_iso A B) A B :=
{ coe := cool_iso.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_op := cool_iso.map_op',
  map_cool := cool_iso.map_cool' }

-- [Insert `has_coe_to_fun`, `to_fun_eq_coe`, `ext` and `copy` here]
```

Then any declaration taking a specific type of morphisms as parameter can instead take the
class you just defined:
```
-- Compare with: lemma do_something (f : my_iso A B) : sorry := sorry
lemma do_something {F : Type*} [my_iso_class F A B] (f : F) : sorry := sorry
```

This means anything set up for `my_iso`s will automatically work for `cool_iso_class`es,
and defining `cool_iso_class` only takes a constant amount of effort,
instead of linearly increasing the work per `my_iso`-related declaration.

-/

/-- The class `equiv_like E α β` expresses that terms of type `E` have an
injective coercion to bijections between `α` and `β`.

This typeclass is used in the definition of the homomorphism typeclasses,
such as `zero_equiv_class`, `mul_equiv_class`, `monoid_equiv_class`, ....
-/
class equiv_like (E : Sort*) (α β : out_param Sort*) :=
(coe : E → α → β)
(inv : E → β → α)
(left_inv  : ∀ e, function.left_inverse (inv e) (coe e))
(right_inv : ∀ e, function.right_inverse (inv e) (coe e))
-- The `inv` hypothesis makes this easier to prove with `congr'`
(coe_injective' : ∀ e g, coe e = coe g → inv e = inv g → e = g)

namespace equiv_like

variables {E F α β γ : Sort*} [iE : equiv_like E α β] [iF : equiv_like F β γ]
include iE

lemma inv_injective : function.injective (equiv_like.inv : E → (β → α)) :=
λ e g h, coe_injective' e g ((right_inv e).eq_right_inverse (h.symm ▸ left_inv g)) h

@[priority 100]
instance to_embedding_like : embedding_like E α β :=
{ coe := (coe : E → α → β),
  coe_injective' := λ e g h, coe_injective' e g h
    ((left_inv e).eq_right_inverse (h.symm ▸ right_inv g)),
  injective' := λ e, (left_inv e).injective }

protected lemma injective (e : E) : function.injective e := embedding_like.injective e
protected lemma surjective (e : E) : function.surjective e := (right_inv e).surjective
protected lemma bijective (e : E) : function.bijective (e : α → β) :=
⟨equiv_like.injective e, equiv_like.surjective e⟩

theorem apply_eq_iff_eq (f : E) {x y : α} : f x = f y ↔ x = y := embedding_like.apply_eq_iff_eq f

@[simp] lemma injective_comp (e : E) (f : β → γ) :
  function.injective (f ∘ e) ↔ function.injective f :=
function.injective.of_comp_iff' f (equiv_like.bijective e)

@[simp] lemma surjective_comp (e : E) (f : β → γ) :
  function.surjective (f ∘ e) ↔ function.surjective f :=
(equiv_like.surjective e).of_comp_iff f

@[simp] lemma bijective_comp (e : E) (f : β → γ) :
  function.bijective (f ∘ e) ↔ function.bijective f :=
(equiv_like.bijective e).of_comp_iff f

/-- This lemma is only supposed to be used in the generic context, when working with instances
of classes extending `equiv_like`.
For concrete isomorphism types such as `equiv`, you should use `equiv.symm_apply_apply`
or its equivalent.

TODO: define a generic form of `equiv.symm`. -/
@[simp] lemma inv_apply_apply (e : E) (a : α) : equiv_like.inv e (e a) = a := left_inv _ _

/-- This lemma is only supposed to be used in the generic context, when working with instances
of classes extending `equiv_like`.
For concrete isomorphism types such as `equiv`, you should use `equiv.apply_symm_apply`
or its equivalent.

TODO: define a generic form of `equiv.symm`. -/
@[simp] lemma apply_inv_apply (e : E) (b : β) : e (equiv_like.inv e b) = b := right_inv _ _

omit iE
include iF

lemma comp_injective (f : α → β) (e : F) :
  function.injective (e ∘ f) ↔ function.injective f :=
embedding_like.comp_injective f e

@[simp] lemma comp_surjective (f : α → β) (e : F) :
  function.surjective (e ∘ f) ↔ function.surjective f :=
function.surjective.of_comp_iff' (equiv_like.bijective e) f

@[simp] lemma comp_bijective (f : α → β) (e : F) :
  function.bijective (e ∘ f) ↔ function.bijective f :=
(equiv_like.bijective e).of_comp_iff' f

/-- This is not an instance to avoid slowing down every single `subsingleton` typeclass search.-/
lemma subsingleton_dom [subsingleton β] : subsingleton F :=
⟨λ f g, fun_like.ext f g $ λ x, (right_inv f).injective $ subsingleton.elim _ _⟩

end equiv_like

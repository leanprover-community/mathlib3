/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import logic.function.basic
import tactic.lint
import tactic.norm_cast

/-!
# Typeclass for a type `F` with an injective map to `A → B`

This typeclass is primarily for use by homomorphisms like `monoid_hom` and `linear_map`.

## Basic usage of `fun_like`

A typical type of morphisms should be declared as:
```
structure my_hom (A B : Type*) [my_class A] [my_class B] :=
(to_fun : A → B)
(map_op' : ∀ {x y : A}, to_fun (my_class.op x y) = my_class.op (to_fun x) (to_fun y))

namespace my_hom

variables (A B : Type*) [my_class A] [my_class B]

-- This instance is optional if you follow the "morphism class" design below:
instance : fun_like (my_hom A B) A (λ _, B) :=
{ coe := my_hom.to_fun, coe_injective' := λ f g h, by cases f; cases g; congr' }

/-- Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
instance : has_coe_to_fun (my_hom A B) (λ _, A → B) := fun_like.has_coe_to_fun

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

## Morphism classes extending `fun_like`

The `fun_like` design provides further benefits if you put in a bit more work.
The first step is to extend `fun_like` to create a class of those types satisfying
the axioms of your new type of morphisms.
Continuing the example above:

```
/-- `my_hom_class F A B` states that `F` is a type of `my_class.op`-preserving morphisms.
You should extend this class when you extend `my_hom`. -/
class my_hom_class (F : Type*) (A B : out_param $ Type*) [my_class A] [my_class B]
  extends fun_like F A (λ _, B) :=
(map_op : ∀ (f : F) (x y : A), f (my_class.op x y) = my_class.op (f x) (f y))

@[simp] lemma map_op {F A B : Type*} [my_class A] [my_class B] [my_hom_class F A B]
  (f : F) (x y : A) : f (my_class.op x y) = my_class.op (f x) (f y) :=
my_hom_class.map_op

-- You can replace `my_hom.fun_like` with the below instance:
instance : my_hom_class (my_hom A B) A B :=
{ coe := my_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_op := my_hom.map_op' }

-- [Insert `has_coe_to_fun`, `to_fun_eq_coe`, `ext` and `copy` here]
```

The second step is to add instances of your new `my_hom_class` for all types extending `my_hom`.
Typically, you can just declare a new class analogous to `my_hom_class`:

```
structure cooler_hom (A B : Type*) [cool_class A] [cool_class B]
  extends my_hom A B :=
(map_cool' : to_fun cool_class.cool = cool_class.cool)

class cooler_hom_class (F : Type*) (A B : out_param $ Type*) [cool_class A] [cool_class B]
  extends my_hom_class F A B :=
(map_cool : ∀ (f : F), f cool_class.cool = cool_class.cool)

@[simp] lemma map_cool {F A B : Type*} [cool_class A] [cool_class B] [cooler_hom_class F A B]
  (f : F) : f cool_class.cool = cool_class.cool :=
my_hom_class.map_op

-- You can also replace `my_hom.fun_like` with the below instance:
instance : cool_hom_class (cool_hom A B) A B :=
{ coe := cool_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_op := cool_hom.map_op',
  map_cool := cool_hom.map_cool' }

-- [Insert `has_coe_to_fun`, `to_fun_eq_coe`, `ext` and `copy` here]
```

Then any declaration taking a specific type of morphisms as parameter can instead take the
class you just defined:
```
-- Compare with: lemma do_something (f : my_hom A B) : sorry := sorry
lemma do_something {F : Type*} [my_hom_class F A B] (f : F) : sorry := sorry
```

This means anything set up for `my_hom`s will automatically work for `cool_hom_class`es,
and defining `cool_hom_class` only takes a constant amount of effort,
instead of linearly increasing the work per `my_hom`-related declaration.

-/

-- This instance should have low priority, to ensure we follow the chain
-- `fun_like → has_coe_to_fun`
attribute [instance, priority 10] coe_fn_trans

/-- The class `fun_like F α β` expresses that terms of type `F` have an
injective coercion to functions from `α` to `β`.

This typeclass is used in the definition of the homomorphism typeclasses,
such as `zero_hom_class`, `mul_hom_class`, `monoid_hom_class`, ....
-/
class fun_like (F : Sort*) (α : out_param Sort*) (β : out_param $ α → Sort*) :=
(coe : F → Π a : α, β a)
(coe_injective' : function.injective coe)

section dependent

/-! ### `fun_like F α β` where `β` depends on `a : α` -/

variables (F α : Sort*) (β : α → Sort*)

namespace fun_like

variables {F α β} [i : fun_like F α β]

include i

@[priority 100, -- Give this a priority between `coe_fn_trans` and the default priority
  nolint dangerous_instance] -- `α` and `β` are out_params, so this instance should not be dangerous
instance : has_coe_to_fun F (λ _, Π a : α, β a) := { coe := fun_like.coe }

@[simp] lemma coe_eq_coe_fn : (fun_like.coe : F → Π a : α, β a) = coe_fn := rfl

theorem coe_injective : function.injective (coe_fn : F → Π a : α, β a) :=
fun_like.coe_injective'

@[simp, norm_cast]
theorem coe_fn_eq {f g : F} : (f : Π a : α, β a) = (g : Π a : α, β a) ↔ f = g :=
⟨λ h, @coe_injective _ _ _ i _ _ h, λ h, by cases h; refl⟩

theorem ext' {f g : F} (h : (f : Π a : α, β a) = (g : Π a : α, β a)) : f = g :=
coe_injective h

theorem ext'_iff {f g : F} : f = g ↔ ((f : Π a : α, β a) = (g : Π a : α, β a)) :=
coe_fn_eq.symm

theorem ext (f g : F) (h : ∀ (x : α), f x = g x) : f = g :=
coe_injective (funext h)

theorem ext_iff {f g : F} : f = g ↔ (∀ x, f x = g x) :=
coe_fn_eq.symm.trans function.funext_iff

protected lemma congr_fun {f g : F} (h₁ : f = g) (x : α) : f x = g x :=
congr_fun (congr_arg _ h₁) x

end fun_like

end dependent

section non_dependent

/-! ### `fun_like F α (λ _, β)` where `β` does not depend on `a : α` -/

variables {F α β : Sort*} [i : fun_like F α (λ _, β)]

include i

namespace fun_like

protected lemma congr {f g : F} {x y : α} (h₁ : f = g) (h₂ : x = y) : f x = g y :=
congr (congr_arg _ h₁) h₂

protected lemma congr_arg (f : F) {x y : α} (h₂ : x = y) : f x = f y :=
congr_arg _ h₂

end fun_like

end non_dependent

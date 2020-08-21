/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import deprecated.group

/-!
# Unbundled semiring and ring homomorphisms (deprecated)

This file defines typeclasses for unbundled semiring and ring homomorphisms. Though these classes are
deprecated, they are still widely used in mathlib, and probably will not go away before Lean 4
because Lean 3 often fails to coerce a bundled homomorphism to a function.

## main definitions

is_semiring_hom (deprecated), is_ring_hom (deprecated)

## Tags

is_semiring_hom, is_ring_hom

-/

universes u v w

variable {α : Type u}

/-- Predicate for semiring homomorphisms (deprecated -- use the bundled `ring_hom` version). -/
class is_semiring_hom {α : Type u} {β : Type v} [semiring α] [semiring β] (f : α → β) : Prop :=
(map_zero [] : f 0 = 0)
(map_one [] : f 1 = 1)
(map_add [] : ∀ {x y}, f (x + y) = f x + f y)
(map_mul [] : ∀ {x y}, f (x * y) = f x * f y)

namespace is_semiring_hom

variables {β : Type v} [semiring α] [semiring β]
variables (f : α → β) [is_semiring_hom f] {x y : α}

/-- The identity map is a semiring homomorphism. -/
instance id : is_semiring_hom (@id α) := by refine {..}; intros; refl

/-- The composition of two semiring homomorphisms is a semiring homomorphism. -/
-- see Note [no instance on morphisms]
lemma comp {γ} [semiring γ] (g : β → γ) [is_semiring_hom g] :
  is_semiring_hom (g ∘ f) :=
{ map_zero := by simp [map_zero f]; exact map_zero g,
  map_one := by simp [map_one f]; exact map_one g,
  map_add := λ x y, by simp [map_add f]; rw map_add g; refl,
  map_mul := λ x y, by simp [map_mul f]; rw map_mul g; refl }

/-- A semiring homomorphism is an additive monoid homomorphism. -/
@[priority 100] -- see Note [lower instance priority]
instance : is_add_monoid_hom f :=
{ ..‹is_semiring_hom f› }

/-- A semiring homomorphism is a monoid homomorphism. -/
@[priority 100] -- see Note [lower instance priority]
instance : is_monoid_hom f :=
{ ..‹is_semiring_hom f› }

end is_semiring_hom

/-- Predicate for ring homomorphisms (deprecated -- use the bundled `ring_hom` version). -/
class is_ring_hom {α : Type u} {β : Type v} [ring α] [ring β] (f : α → β) : Prop :=
(map_one [] : f 1 = 1)
(map_mul [] : ∀ {x y}, f (x * y) = f x * f y)
(map_add [] : ∀ {x y}, f (x + y) = f x + f y)

namespace is_ring_hom

variables {β : Type v} [ring α] [ring β]

/-- A map of rings that is a semiring homomorphism is also a ring homomorphism. -/
lemma of_semiring (f : α → β) [H : is_semiring_hom f] : is_ring_hom f := {..H}

variables (f : α → β) [is_ring_hom f] {x y : α}

/-- Ring homomorphisms map zero to zero. -/
lemma map_zero : f 0 = 0 :=
calc f 0 = f (0 + 0) - f 0 : by rw [map_add f]; simp
     ... = 0 : by simp

/-- Ring homomorphisms preserve additive inverses. -/
lemma map_neg : f (-x) = -f x :=
calc f (-x) = f (-x + x) - f x : by rw [map_add f]; simp
        ... = -f x : by simp [map_zero f]

/-- Ring homomorphisms preserve subtraction. -/
lemma map_sub : f (x - y) = f x - f y :=
by simp [sub_eq_add_neg, map_add f, map_neg f]

/-- The identity map is a ring homomorphism. -/
instance id : is_ring_hom (@id α) := by refine {..}; intros; refl

/-- The composition of two ring homomorphisms is a ring homomorphism. -/
-- see Note [no instance on morphisms]
lemma comp {γ} [ring γ] (g : β → γ) [is_ring_hom g] :
  is_ring_hom (g ∘ f) :=
{ map_add := λ x y, by simp [map_add f]; rw map_add g; refl,
  map_mul := λ x y, by simp [map_mul f]; rw map_mul g; refl,
  map_one := by simp [map_one f]; exact map_one g }

/-- A ring homomorphism is also a semiring homomorphism. -/
@[priority 100] -- see Note [lower instance priority]
instance : is_semiring_hom f :=
{ map_zero := map_zero f, ..‹is_ring_hom f› }

@[priority 100] -- see Note [lower instance priority]
instance : is_add_group_hom f := { }

end is_ring_hom

variables {β : Type v} {γ : Type w} [rα : semiring α] [rβ : semiring β]

namespace ring_hom

section
include rα rβ

/-- Interpret `f : α → β` with `is_semiring_hom f` as a ring homomorphism. -/
def of (f : α → β) [is_semiring_hom f] : α →+* β :=
{ to_fun := f,
  .. monoid_hom.of f,
  .. add_monoid_hom.of f }

@[simp] lemma coe_of (f : α → β) [is_semiring_hom f] : ⇑(of f) = f := rfl

instance (f : α →+* β) : is_semiring_hom f :=
{ map_zero := f.map_zero,
  map_one := f.map_one,
  map_add := f.map_add,
  map_mul := f.map_mul }

end

instance {α γ} [ring α] [ring γ] (g : α →+* γ) : is_ring_hom g :=
is_ring_hom.of_semiring g

end ring_hom

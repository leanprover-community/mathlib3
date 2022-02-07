/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import topology.continuous_function.algebra

/-!

# Continuous Monoid Homs

This file defines the space of continuous homomorphisms between two topological groups.

## Main definitions

* `continuous_monoid_hom A B`: The continuous homomorphisms `A →* B`.

-/

variables (A B C D E : Type*)
  [monoid A] [monoid B] [monoid C] [monoid D] [comm_group E]
  [topological_space A] [topological_space B] [topological_space C] [topological_space D]
  [topological_space E] [topological_group E]

set_option old_structure_cmd true

/-- Continuous homomorphisms between two topological groups. -/
structure continuous_monoid_hom extends A →* B, continuous_map A B

/-- Continuous homomorphisms between two topological groups. -/
structure continuous_add_monoid_hom (A B : Type*) [add_monoid A] [add_monoid B]
  [topological_space A] [topological_space B] extends A →+ B, continuous_map A B

attribute [to_additive] continuous_monoid_hom
attribute [to_additive] continuous_monoid_hom.to_monoid_hom

initialize_simps_projections continuous_monoid_hom (to_fun → apply)

/-- Reinterpret a `continuous_monoid_hom` as a `monoid_hom`. -/
add_decl_doc continuous_monoid_hom.to_monoid_hom

/-- Reinterpret a `continuous_monoid_hom` as a `continuous_map`. -/
add_decl_doc continuous_monoid_hom.to_continuous_map

/-- Reinterpret a `continuous_add_monoid_hom` as an `add_monoid_hom`. -/
add_decl_doc continuous_add_monoid_hom.to_add_monoid_hom

/-- Reinterpret a `continuous_add_monoid_hom` as a `continuous_map`. -/
add_decl_doc continuous_add_monoid_hom.to_continuous_map

namespace continuous_monoid_hom

variables {A B C D E}

@[to_additive] instance : has_coe_to_fun (continuous_monoid_hom A B) (λ _, A → B) :=
⟨continuous_monoid_hom.to_fun⟩

@[to_additive] lemma ext {f g : continuous_monoid_hom A B} (h : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr; exact funext h

/-- Construct a `continuous_monoid_hom` from a `continuous` `monoid_hom`. -/
@[to_additive "Construct a `continuous_add_monoid_hom` from a `continuous` `add_monoid_hom`.",
  simps]
def mk' (f : A →* B) (hf : continuous f) : continuous_monoid_hom A B := { .. f }

/-- Composition of two continuous homomorphisms. -/
@[to_additive "Composition of two continuous homomorphisms.", simps]
def comp (g : continuous_monoid_hom B C) (f : continuous_monoid_hom A B) :
  continuous_monoid_hom A C :=
mk' (g.to_monoid_hom.comp f.to_monoid_hom) (g.continuous_to_fun.comp f.continuous_to_fun)

/-- Product of two continuous homomorphisms on the same space. -/
@[to_additive "Product of two continuous homomorphisms on the same space.", simps]
def prod (f : continuous_monoid_hom A B) (g : continuous_monoid_hom A C) :
  continuous_monoid_hom A (B × C) :=
mk' (f.to_monoid_hom.prod g.to_monoid_hom) (f.continuous_to_fun.prod_mk g.continuous_to_fun)

/-- Product of two continuous homomorphisms on different spaces. -/
@[to_additive "Product of two continuous homomorphisms on different spaces.", simps]
def prod_map (f : continuous_monoid_hom A C) (g : continuous_monoid_hom B D) :
  continuous_monoid_hom (A × B) (C × D) :=
mk' (f.to_monoid_hom.prod_map g.to_monoid_hom) (f.continuous_to_fun.prod_map g.continuous_to_fun)

variables (A B C D E)

/-- The trivial continuous homomorphism. -/
@[to_additive "The trivial continuous homomorphism.", simps]
def one : continuous_monoid_hom A B := mk' 1 continuous_const

@[to_additive] instance : inhabited (continuous_monoid_hom A B) := ⟨one A B⟩

/-- The identity continuous homomorphism. -/
@[to_additive "The identity continuous homomorphism.", simps]
def id : continuous_monoid_hom A A := mk' (monoid_hom.id A) continuous_id

/-- The continuous homomorphism given by projection onto the first factor. -/
@[to_additive "The continuous homomorphism given by projection onto the first factor.", simps]
def fst : continuous_monoid_hom (A × B) A := mk' (monoid_hom.fst A B) continuous_fst

/-- The continuous homomorphism given by projection onto the second factor. -/
@[to_additive "The continuous homomorphism given by projection onto the second factor.", simps]
def snd : continuous_monoid_hom (A × B) B := mk' (monoid_hom.snd A B) continuous_snd

/-- The continuous homomorphism given by inclusion of the first factor. -/
@[to_additive "The continuous homomorphism given by inclusion of the first factor.", simps]
def inl : continuous_monoid_hom A (A × B) := prod (id A) (one A B)

/-- The continuous homomorphism given by inclusion of the second factor. -/
@[to_additive "The continuous homomorphism given by inclusion of the second factor.", simps]
def inr : continuous_monoid_hom B (A × B) := prod (one B A) (id B)

/-- The continuous homomorphism given by the diagonal embedding. -/
@[to_additive "The continuous homomorphism given by the diagonal embedding.", simps]
def diag : continuous_monoid_hom A (A × A) := prod (id A) (id A)

/-- The continuous homomorphism given by swapping components. -/
@[to_additive "The continuous homomorphism given by swapping components.", simps]
def swap : continuous_monoid_hom (A × B) (B × A) := prod (snd A B) (fst A B)

/-- The continuous homomorphism given by multiplication. -/
@[to_additive "The continuous homomorphism given by addition.", simps]
def mul : continuous_monoid_hom (E × E) E :=
mk' mul_monoid_hom continuous_mul

/-- The continuous homomorphism given by inversion. -/
@[to_additive "The continuous homomorphism given by negation.", simps]
def inv : continuous_monoid_hom E E :=
mk' comm_group.inv_monoid_hom continuous_inv

variables {A B C D E}

/-- Coproduct of two continuous homomorphisms to the same space. -/
@[to_additive "Coproduct of two continuous homomorphisms to the same space.", simps]
def coprod (f : continuous_monoid_hom A E) (g : continuous_monoid_hom B E) :
  continuous_monoid_hom (A × B) E :=
(mul E).comp (f.prod_map g)

@[to_additive] instance : comm_group (continuous_monoid_hom A E) :=
{ mul := λ f g, (mul E).comp (f.prod g),
  mul_comm := λ f g, ext (λ x, mul_comm (f x) (g x)),
  mul_assoc := λ f g h, ext (λ x, mul_assoc (f x) (g x) (h x)),
  one := one A E,
  one_mul := λ f, ext (λ x, one_mul (f x)),
  mul_one := λ f, ext (λ x, mul_one (f x)),
  inv := λ f, (inv E).comp f,
  mul_left_inv := λ f, ext (λ x, mul_left_inv (f x)) }

instance : topological_space (continuous_monoid_hom A B) :=
topological_space.induced to_continuous_map continuous_map.compact_open

variables (A B C D E)

lemma is_inducing : inducing (to_continuous_map : continuous_monoid_hom A B → C(A, B)) := ⟨rfl⟩

lemma is_embedding : embedding (to_continuous_map : continuous_monoid_hom A B → C(A, B)) :=
⟨is_inducing A B, λ _ _, ext ∘ continuous_map.ext_iff.mp⟩

variables {A B C D E}

instance [locally_compact_space A] [t2_space B] : t2_space (continuous_monoid_hom A B) :=
(is_embedding A B).t2_space

instance : topological_group (continuous_monoid_hom A E) :=
let hi := is_inducing A E, hc := hi.continuous in
{ continuous_mul := hi.continuous_iff.mpr (continuous_mul.comp (continuous.prod_map hc hc)),
  continuous_inv := hi.continuous_iff.mpr (continuous_inv.comp hc) }

end continuous_monoid_hom

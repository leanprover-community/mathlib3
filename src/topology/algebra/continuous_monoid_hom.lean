/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import analysis.complex.circle
import topology.continuous_function.algebra

/-!

# Continuous Monoid Homs

This file defines the space of continuous homomorphisms between two topological groups.

## Main definitions

* `continuous_monoid_hom A B`: The continuous homomorphisms `A →* B`.
* `continuous_add_monoid_hom α β`: The continuous additive homomorphisms `α →+ β`.
-/

open_locale pointwise

open function

variables {F α β : Type*} (A B C D E : Type*)
  [monoid A] [monoid B] [monoid C] [monoid D] [comm_group E]
  [topological_space A] [topological_space B] [topological_space C] [topological_space D]
  [topological_space E] [topological_group E]

/-- The type of continuous additive monoid homomorphisms from `α` to `β`.

When possible, instead of parametrizing results over `(f : continuous_add_monoid_hom α β)`,
you should parametrize over `(F : Type*) [continuous_add_monoid_hom_class F α β] (f : F)`.

When you extend this structure, make sure to extend `continuous_add_monoid_hom_class`. -/
structure continuous_add_monoid_hom (A B : Type*) [add_monoid A] [add_monoid B]
  [topological_space A] [topological_space B] extends A →+ B :=
(continuous_to_fun : continuous to_fun)

/-- The type of continuous monoid homomorphisms from `α` to `β`.

When possible, instead of parametrizing results over `(f : continuous_monoid_hom α β)`,
you should parametrize over `(F : Type*) [continuous_monoid_hom_class F α β] (f : F)`.

When you extend this structure, make sure to extend `continuous_add_monoid_hom_class`. -/
@[to_additive]
structure continuous_monoid_hom extends A →* B :=
(continuous_to_fun : continuous to_fun)

/-- `continuous_add_monoid_hom_class F α β` states that `F` is a type of continuous additive monoid
homomorphisms.

You should also extend this typeclass when you extend `continuous_add_monoid_hom`. -/
class continuous_add_monoid_hom_class (F α β : Type*) [add_monoid α] [add_monoid β]
  [topological_space α] [topological_space β] extends add_monoid_hom_class F α β :=
(map_continuous (f : F) : continuous f)

/-- `continuous_monoid_hom_class F α β` states that `F` is a type of continuous additive monoid
homomorphisms.

You should also extend this typeclass when you extend `continuous_monoid_hom`. -/
@[to_additive]
class continuous_monoid_hom_class (F α β : Type*) [monoid α] [monoid β]
  [topological_space α] [topological_space β] extends monoid_hom_class F α β :=
(map_continuous (f : F) : continuous f)

/-- Reinterpret a `continuous_monoid_hom` as a `monoid_hom`. -/
add_decl_doc continuous_monoid_hom.to_monoid_hom

/-- Reinterpret a `continuous_add_monoid_hom` as an `add_monoid_hom`. -/
add_decl_doc continuous_add_monoid_hom.to_add_monoid_hom

@[priority 100, to_additive] -- See note [lower instance priority]
instance continuous_monoid_hom_class.to_continuous_map_class [monoid α] [monoid β]
  [topological_space α] [topological_space β] [continuous_monoid_hom_class F α β] :
  continuous_map_class F α β :=
{ .. ‹continuous_monoid_hom_class F α β› }

namespace continuous_monoid_hom
variables {A B C D E} [monoid α] [monoid β] [topological_space α] [topological_space β]

@[to_additive]
instance : continuous_monoid_hom_class (continuous_monoid_hom α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_mul := λ f, f.map_mul',
  map_one := λ f, f.map_one',
  map_continuous := λ f, f.continuous_to_fun }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
@[to_additive] instance : has_coe_to_fun (continuous_monoid_hom A B) (λ _, A → B) :=
fun_like.has_coe_to_fun

@[to_additive] lemma ext {f g : continuous_monoid_hom A B} (h : ∀ x, f x = g x) : f = g :=
fun_like.ext _ _ h

/-- Reinterpret a `continuous_monoid_hom` as a `continuous_map`. -/
@[to_additive "Reinterpret a `continuous_add_monoid_hom` as a `continuous_map`."]
def to_continuous_map (f : continuous_monoid_hom α β) : C(α, β) := { .. f}

@[to_additive] lemma to_continuous_map_injective : injective (to_continuous_map : _ → C(α, β)) :=
λ f g h, ext $ by convert fun_like.ext_iff.1 h

/-- Construct a `continuous_monoid_hom` from a `continuous` `monoid_hom`. -/
@[to_additive "Construct a `continuous_add_monoid_hom` from a `continuous` `add_monoid_hom`.",
  simps]
def mk' (f : A →* B) (hf : continuous f) : continuous_monoid_hom A B :=
{ continuous_to_fun := hf, .. f }

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
⟨is_inducing A B, to_continuous_map_injective⟩

lemma is_closed_embedding [has_continuous_mul B] [t2_space B] :
  closed_embedding (to_continuous_map : continuous_monoid_hom A B → C(A, B)) :=
⟨is_embedding A B, ⟨begin
  suffices : (set.range (to_continuous_map : continuous_monoid_hom A B → C(A, B))) =
    ({f | f '' {1} ⊆ {1}ᶜ} ∪ ⋃ (x y) (U V W) (hU : is_open U) (hV : is_open V) (hW : is_open W)
    (h : disjoint (U * V) W), {f | f '' {x} ⊆ U} ∩ {f | f '' {y} ⊆ V} ∩ {f | f '' {x * y} ⊆ W})ᶜ,
  { rw [this, compl_compl],
    refine (continuous_map.is_open_gen is_compact_singleton is_open_compl_singleton).union _,
    repeat { apply is_open_Union, intro, },
    repeat { apply is_open.inter },
    all_goals { apply continuous_map.is_open_gen is_compact_singleton, assumption } },
  simp_rw [set.compl_union, set.compl_Union, set.image_singleton, set.singleton_subset_iff,
    set.ext_iff, set.mem_inter_iff, set.mem_Inter, set.mem_compl_iff],
  refine λ f, ⟨_, _⟩,
  { rintros ⟨f, rfl⟩,
    exact ⟨λ h, h (map_one f), λ x y U V W hU hV hW h ⟨⟨hfU, hfV⟩, hfW⟩,
      h ⟨set.mul_mem_mul hfU hfV, (congr_arg (∈ W) (map_mul f x y)).mp hfW⟩⟩ },
  { rintros ⟨hf1, hf2⟩,
    suffices : ∀ x y, f (x * y) = f x * f y,
    { refine ⟨({ map_one' := of_not_not hf1, map_mul' := this, .. f } : continuous_monoid_hom A B),
       continuous_map.ext (λ _, rfl)⟩, },
    intros x y,
    contrapose! hf2,
    obtain ⟨UV, W, hUV, hW, hfUV, hfW, h⟩ := t2_separation hf2.symm,
    have hB := @continuous_mul B _ _ _,
    obtain ⟨U, V, hU, hV, hfU, hfV, h'⟩ := is_open_prod_iff.mp (hUV.preimage hB) (f x) (f y) hfUV,
    refine ⟨x, y, U, V, W, hU, hV, hW, ((disjoint_iff.mpr h).mono_left _), ⟨hfU, hfV⟩, hfW⟩,
    rintros _ ⟨x, y, hx : (x, y).1 ∈ U, hy : (x, y).2 ∈ V, rfl⟩,
    exact h' ⟨hx, hy⟩ },
end⟩⟩

variables {A B C D E}

instance [t2_space B] : t2_space (continuous_monoid_hom A B) :=
(is_embedding A B).t2_space

instance : topological_group (continuous_monoid_hom A E) :=
let hi := is_inducing A E, hc := hi.continuous in
{ continuous_mul := hi.continuous_iff.mpr (continuous_mul.comp (continuous.prod_map hc hc)),
  continuous_inv := hi.continuous_iff.mpr (continuous_inv.comp hc) }

end continuous_monoid_hom

/-- The Pontryagin dual of `G` is the group of continuous homomorphism `G → circle`. -/
@[derive [topological_space, t2_space, comm_group, topological_group, inhabited]]
def pontryagin_dual (G : Type*) [monoid G] [topological_space G] := continuous_monoid_hom G circle

/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.equalizers
import category_theory.limits.preserves

/-!
# Connected category

Define a connected category as a _nonempty_ category for which every functor
to a discrete category is isomorphic to the constant functor.

NB. Some authors include the empty category as connected, we do not.
We instead are interested in categories with exactly one 'connected
component'.

We give some equivalent definitions:
- A nonempty category for which every functor to a discrete category is
  constant on objects.
  See `any_functor_const_on_obj` and `connected.of_any_functor_const_on_obj`.
- A nonempty category for which every function `F` for which the presence of a
  morphism `f : j₁ ⟶ j₂` implies `F j₁ = F j₂` must be constant everywhere.
  See `constant_of_preserves_morphisms` and `connected.of_constant_of_preserves_morphisms`.
- A nonempty category for which any subset of its elements containing the
  default and closed under morphisms is everything.
  See `induct_on_objects` and `connected.of_induct`.
- A nonempty category for which every object is related under the reflexive
  transitive closure of the relation "there is a morphism in some direction
  from `j₁` to `j₂`".
  See `connected_zigzag` and `zigzag_connected`.
- A nonempty category for which for any two objects there is a sequence of
  morphisms (some reversed) from one to the other.
  See `exists_zigzag'` and `connected_of_zigzag`.

We also prove the result that the functor given by `(X × -)` preserves any
connected limit. That is, any limit of shape `J` where `J` is a connected
category is preserved by the functor `(X × -)`.
-/

universes v₁ v₂ u₁ u₂

open category_theory category_theory.category category_theory.limits
namespace category_theory

section connected
-- See note [default priority]
set_option default_priority 100
/--
We define a connected category as a _nonempty_ category for which every
functor to a discrete category is constant.

NB. Some authors include the empty category as connected, we do not.
We instead are interested in categories with exactly one 'connected
component'.

This allows us to show that the functor X ⨯ - preserves connected limits.
-/
class connected (J : Type v₂) [𝒥 : category.{v₁} J] extends inhabited J :=
(iso_constant : Π {α : Type v₂} (F : J ⥤ discrete α), F ≅ (functor.const J).obj (F.obj default))
end connected

section J
variables {J : Type v₂} [𝒥 : category.{v₁} J]
include 𝒥

/--
If J is connected, any functor to a discrete category is constant on objects.
The converse is given in `connected.of_any_functor_const_on_obj`.
-/
lemma any_functor_const_on_obj [connected J] {α : Type v₂} (F : J ⥤ discrete α) (j : J) :
  F.obj j = F.obj (default J) :=
((connected.iso_constant F).hom.app j).down.1

/--
If any functor to a discrete category is constant on objects, J is connected.
The converse of `any_functor_const_on_obj`.
-/
def connected.of_any_functor_const_on_obj [inhabited J]
  (h : ∀ {α : Type v₂} (F : J ⥤ discrete α), ∀ (j : J), F.obj j = F.obj (default J)) :
  connected J :=
{ iso_constant := λ α F, nat_iso.of_components (λ B, eq_to_iso (h F B)) (λ _ _ _, subsingleton.elim _ _) }

/--
If `J` is connected, then given any function `F` such that the presence of a
morphism `j₁ ⟶ j₂` implies `F j₁ = F j₂`, we have that `F` is constant.
This can be thought of as a local-to-global property.

The converse is shown in `connected.of_constant_of_preserves_morphisms`
-/
lemma constant_of_preserves_morphisms [connected J] {α : Type v₂} (F : J → α) (h : ∀ (j₁ j₂ : J) (f : j₁ ⟶ j₂), F j₁ = F j₂) (j : J) :
  F j = F (default J) :=
any_functor_const_on_obj { obj := F, map := λ _ _ f, eq_to_hom (h _ _ f) } j

/--
`J` is connected if: given any function `F : J → α` which is constant for any
`j₁, j₂` for which there is a morphism `j₁ ⟶ j₂`, then `F` is constant.
This can be thought of as a local-to-global property.

The converse of `constant_of_preserves_morphisms`.
-/
def connected.of_constant_of_preserves_morphisms [inhabited J]
  (h : ∀ {α : Type v₂} (F : J → α), (∀ {j₁ j₂ : J} (f : j₁ ⟶ j₂), F j₁ = F j₂) → (∀ j : J, F j = F (default J))) :
  connected J :=
connected.of_any_functor_const_on_obj (λ _ F, h F.obj (λ _ _ f, (F.map f).down.1))

/--
An inductive-like property for the objects of a connected category.
If `default J` is in the set `p`, and `p` is closed under morphisms of `J`,
then `p` contains all of `J`.

The converse is given in `connected.of_induct`.
-/
lemma induct_on_objects [connected J] (p : set J) (h0 : default J ∈ p)
  (h1 : ∀ {j₁ j₂ : J} (f : j₁ ⟶ j₂), j₁ ∈ p ↔ j₂ ∈ p) (j : J) :
  j ∈ p :=
begin
  injection (constant_of_preserves_morphisms (λ k, ulift.up (k ∈ p)) (λ j₁ j₂ f, _) j) with i,
  rwa i,
  dsimp,
  exact congr_arg ulift.up (propext (h1 f)),
end

/--
If any maximal connected component of J containing the default is all of J, then J is connected.

The converse of `induct_on_objects`.
-/
def connected.of_induct [inhabited J]
  (h : ∀ (p : set J), default J ∈ p → (∀ {j₁ j₂ : J} (f : j₁ ⟶ j₂), j₁ ∈ p ↔ j₂ ∈ p) → ∀ (j : J), j ∈ p) :
  connected J :=
connected.of_constant_of_preserves_morphisms (λ α F a, h {j | F j = F (default J)} rfl (λ _ _ f, by simp [a f] ))

/-- j₁ and j₂ are related by `zag` if there is a morphism between them. -/
@[reducible]
def zag (j₁ j₂ : J) : Prop := nonempty (j₁ ⟶ j₂) ∨ nonempty (j₂ ⟶ j₁)
/--
`j₁` and `j₂` are related by `zigzag` if there is a chain of
morphisms from `j₁` to `j₂`, with backward morphisms allowed.
-/
@[reducible]
def zigzag : J → J → Prop := relation.refl_trans_gen zag

/-- Any equivalence relation containing (⟶) holds for all pairs of a connected category. -/
lemma equiv_relation [connected J] (r : J → J → Prop) (hr : _root_.equivalence r)
  (h : ∀ {j₁ j₂ : J} (f : j₁ ⟶ j₂), r j₁ j₂) :
  ∀ (j₁ j₂ : J), r j₁ j₂ :=
begin
  have z: ∀ (j : J), r (default J) j :=
    induct_on_objects (λ k, r (default J) k)
        (hr.1 (default J)) (λ _ _ f, ⟨λ t, hr.2.2 t (h f), λ t, hr.2.2 t (hr.2.1 (h f))⟩),
  intros, apply hr.2.2 (hr.2.1 (z _)) (z _)
end

/-- In a connected category, any two objects are related by `zigzag`. -/
lemma connected_zigzag [connected J] (j₁ j₂ : J) : zigzag j₁ j₂ :=
equiv_relation _
  (mk_equivalence _
    relation.reflexive_refl_trans_gen
    (relation.refl_trans_gen.symmetric (λ _ _ _, by rwa [zag, or_comm]))
    relation.transitive_refl_trans_gen)
  (λ _ _ f, relation.refl_trans_gen.single (or.inl (nonempty.intro f))) _ _

/--
If any two objects in an inhabited category are related by `zigzag`, the category is connected.
-/
def zigzag_connected [inhabited J] (h : ∀ (j₁ j₂ : J), zigzag j₁ j₂) : connected J :=
begin
  apply connected.of_induct,
  intros,
  have: ∀ (j₁ j₂ : J), zigzag j₁ j₂ → (j₁ ∈ p ↔ j₂ ∈ p),
  { introv k,
    induction k,
    { refl },
    { rw k_ih,
      rcases k_a_1 with ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩,
      apply a_1 k_a_1,
      apply (a_1 k_a_1).symm } },
  rwa this j (default J) (h _ _)
end

lemma exists_zigzag' [connected J] (j₁ j₂ : J) :
  ∃ l, list.chain zag j₁ l ∧ list.last (j₁ :: l) (list.cons_ne_nil _ _) = j₂ :=
list.exists_chain_of_relation_refl_trans_gen (connected_zigzag _ _)

/--
If any two objects in an inhabited category are linked by a sequence of (potentially reversed)
morphisms, then J is connected.

The converse of `exists_zigzag'`.
-/
def connected_of_zigzag [inhabited J]
  (h : ∀ (j₁ j₂ : J), ∃ l, list.chain zag j₁ l ∧ list.last (j₁ :: l) (list.cons_ne_nil _ _) = j₂) :
  connected J :=
begin
  apply connected.of_induct,
  intros p d k j,
  obtain ⟨l, zags, lst⟩ := h j (default J),
  apply list.chain.induction p l zags lst _ d,
  rintros _ _ (⟨⟨_⟩⟩ | ⟨⟨_⟩⟩),
  { exact (k a).2 },
  { exact (k a).1 }
end

end J

section examples
instance cospan_inhabited : inhabited walking_cospan := ⟨walking_cospan.one⟩

instance cospan_connected : connected (walking_cospan) :=
begin
  apply connected.of_induct,
  introv _ t,
  cases j,
  { rwa t walking_cospan.hom.inl },
  { rwa t walking_cospan.hom.inr },
  { assumption }
end

instance span_inhabited : inhabited walking_span := ⟨walking_span.zero⟩

instance span_connected : connected (walking_span) :=
begin
  apply connected.of_induct,
  introv _ t,
  cases j,
  { assumption },
  { rwa ← t walking_span.hom.fst },
  { rwa ← t walking_span.hom.snd },
end

instance parallel_pair_inhabited : inhabited walking_parallel_pair := ⟨walking_parallel_pair.one⟩

instance parallel_pair_connected : connected (walking_parallel_pair) :=
begin
  apply connected.of_induct,
  introv _ t, cases j,
  { rwa t walking_parallel_pair_hom.left },
  { assumption }
end

end examples

section C
variables {J : Type v₂} [𝒥 : category.{v₁} J]
include 𝒥

variables {C : Type u₂} [𝒞 : category.{v₂} C]
include 𝒞

/--
For objects `X Y : C`, any natural transformation `α : const X ⟶ const Y` from a connected
category must be constant.
This is the key property of connected categories which we use to establish properties about limits.
-/
lemma nat_trans_from_connected [conn : connected J] {X Y : C}
  (α : (functor.const J).obj X ⟶ (functor.const J).obj Y) :
  ∀ (j : J), α.app j = (α.app (default J) : X ⟶ Y) :=
@constant_of_preserves_morphisms _ _ _
  (X ⟶ Y)
  (λ j, α.app j)
  (λ _ _ f, (by { have := α.naturality f, erw [id_comp, comp_id] at this, exact this.symm }))

end C

local attribute [tidy] tactic.case_bash

variables {C : Type u₂} [𝒞 : category.{v₂} C]
include 𝒞

section products

variables [has_binary_products.{v₂} C]

variables {J : Type v₂} [small_category J]

/-- (Impl). The obvious natural transformation from (X × K -) to K. -/
@[simps]
def γ₂ {K : J ⥤ C} (X : C) : K ⋙ prod_functor.obj X ⟶ K :=
{ app := λ Y, limits.prod.snd }

/-- (Impl). The obvious natural transformation from (X × K -) to X -/
@[simps]
def γ₁ {K : J ⥤ C} (X : C) : K ⋙ prod_functor.obj X ⟶ (functor.const J).obj X :=
{ app := λ Y, limits.prod.fst }

/-- (Impl). Given a cone for (X × K -), produce a cone for K using the natural transformation `γ₂` -/
@[simps]
def forget_cone {X : C} {K : J ⥤ C} (s : cone (K ⋙ prod_functor.obj X)) : cone K :=
{ X := s.X,
  π := s.π ≫ γ₂ X }

/--
The functor `(X × -)` preserves any connected limit.
Note that this functor does not preserve the two most obvious disconnected limits - that is,
`(X × -)` does not preserve products or terminal object, eg `(X ⨯ A) ⨯ (X ⨯ B)` is not isomorphic to
`X ⨯ (A ⨯ B)` and `X ⨯ 1` is not isomorphic to `1`.
-/
def prod_preserves_connected_limits [connected J] (X : C) :
  preserves_limits_of_shape J (prod_functor.obj X) :=
{ preserves_limit := λ K,
  { preserves := λ c l,
    { lift := λ s, prod.lift (s.π.app (default _) ≫ limits.prod.fst) (l.lift (forget_cone s)),
      fac' := λ s j,
      begin
        apply prod.hom_ext,
        { erw [assoc, limit.map_π, comp_id, limit.lift_π],
          exact (nat_trans_from_connected (s.π ≫ γ₁ X) j).symm },
        { simp [← l.fac (forget_cone s) j] }
      end,
      uniq' := λ s m L,
      begin
        apply prod.hom_ext,
        { erw [limit.lift_π, ← L (default J), assoc, limit.map_π, comp_id],
          refl },
        { rw limit.lift_π,
          apply l.uniq (forget_cone s),
          intro j,
          simp [← L j] }
      end } } }

end products

end category_theory

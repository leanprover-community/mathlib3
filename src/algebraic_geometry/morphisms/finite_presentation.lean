/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.morphisms.ring_hom_properties
import algebraic_geometry.morphisms.quasi_separated

/-!
# Morphisms of finite presentation

A morphism of schemes `f : X ⟶ Y` is locally of finite presentation if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite presentation.

A morphism of schemes is of finite presentation if it is both locally of finite presentation,
quasi-compact, and quasi-separated.

We show that these properties is local, and is stable under compositions and base-changes.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
A morphism is `affine` if the preimages of affine open sets are affine.
-/
@[mk_iff]
class locally_of_finite_presentation (f : X ⟶ Y) : Prop :=
(of_finite_presentation_of_affine_subset :
  ∀ (U : Y.affine_opens) (V : X.affine_opens) (e : V.1 ≤ (opens.map f.1.base).obj U.1),
  (f.1.c.app (op U) ≫ X.presheaf.map (hom_of_le e).op).finite_presentation)

lemma _root_.ring_hom.finite_presentation_is_local :
  ring_hom.property_is_local @ring_hom.finite_presentation := sorry

lemma _root_.ring_hom.finite_presentation_stable_under_base_change :
  ring_hom.stable_under_base_change @ring_hom.finite_presentation := sorry

lemma _root_.ring_hom.finite_presentation_respects_iso :
  ring_hom.respects_iso @ring_hom.finite_presentation :=
ring_hom.finite_presentation_is_local.respects_iso

lemma locally_of_finite_presentation_eq :
  @locally_of_finite_presentation = target_affine_locally (source_affine_locally @ring_hom.finite_presentation) :=
begin
  ext X Y f,
  rw [locally_of_finite_presentation_iff, target_affine_locally_source_affine_locally_iff_affine_opens_le],
  exact ring_hom.finite_presentation_respects_iso
end

@[priority 900]
instance locally_of_finite_presentation_of_is_open_immersion {X Y : Scheme} (f : X ⟶ Y)
  [is_open_immersion f] : locally_of_finite_presentation f :=
locally_of_finite_presentation_eq.symm ▸
  affine_locally_of_is_open_immersion ring_hom.finite_presentation_is_local f

lemma locally_of_finite_presentation_stable_under_composition :
  stable_under_composition @locally_of_finite_presentation :=
locally_of_finite_presentation_eq.symm ▸
  affine_locally_stable_under_composition ring_hom.finite_presentation_is_local

instance locally_of_finite_presentation_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [hf : locally_of_finite_presentation f] [hg : locally_of_finite_presentation g] :
  locally_of_finite_presentation (f ≫ g) :=
locally_of_finite_presentation_stable_under_composition f g hf hg

lemma locally_of_finite_presentation.affine_open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)]
  (𝒰' : ∀ i, Scheme.open_cover.{u} ((𝒰.pullback_cover f).obj i)) [∀ i j, is_affine ((𝒰' i).obj j)] :
  locally_of_finite_presentation f ↔
    (∀ i j, (Scheme.Γ.map ((𝒰' i).map j ≫ pullback.snd).op).finite_presentation) :=
locally_of_finite_presentation_eq.symm ▸
  ring_hom.finite_presentation_is_local.affine_open_cover_iff f 𝒰 𝒰'

lemma locally_of_finite_presentation.source_open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} X) :
  locally_of_finite_presentation f ↔ (∀ i, locally_of_finite_presentation (𝒰.map i ≫ f)) :=
locally_of_finite_presentation_eq.symm ▸
  ring_hom.finite_presentation_is_local.source_open_cover_iff f 𝒰

lemma locally_of_finite_presentation.open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} Y) :
  locally_of_finite_presentation f ↔
    (∀ i, locally_of_finite_presentation (pullback.snd : pullback f (𝒰.map i) ⟶ _)) :=
locally_of_finite_presentation_eq.symm ▸
  ring_hom.finite_presentation_is_local.is_local_source_affine_locally.open_cover_iff f 𝒰

lemma locally_of_finite_presentation_respects_iso :
  respects_iso @locally_of_finite_presentation :=
locally_of_finite_presentation_eq.symm ▸ target_affine_locally_respects_iso
  (source_affine_locally_respects_iso ring_hom.finite_presentation_respects_iso)

lemma locally_of_finite_presentation_stable_under_base_change :
  stable_under_base_change @locally_of_finite_presentation :=
locally_of_finite_presentation_eq.symm ▸
  affine_locally_stable_under_base_change ring_hom.finite_presentation_is_local
    ring_hom.finite_presentation_stable_under_base_change

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [locally_of_finite_presentation g] :
  locally_of_finite_presentation (pullback.fst : pullback f g ⟶ X) :=
locally_of_finite_presentation_stable_under_base_change f g infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [locally_of_finite_presentation f] :
  locally_of_finite_presentation (pullback.snd : pullback f g ⟶ Y) :=
locally_of_finite_presentation_stable_under_base_change.symmetry
  locally_of_finite_presentation_respects_iso f g infer_instance

class of_finite_presentation extends
  locally_of_finite_presentation f, quasi_compact f, quasi_separated f

@[priority 900]
instance of_finite_presentation_of_iso {X Y Z : Scheme} (f : X ⟶ Y) [is_iso f] :
  of_finite_presentation f := {}

instance of_finite_presentation_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [hf : of_finite_presentation f] [hg : of_finite_presentation g] :
  of_finite_presentation (f ≫ g) := {}

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [of_finite_presentation g] :
  of_finite_presentation (pullback.fst : pullback f g ⟶ X) := {}

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [of_finite_presentation f] :
  of_finite_presentation (pullback.snd : pullback f g ⟶ Y) := {}

#check of_finite_presentation

end algebraic_geometry

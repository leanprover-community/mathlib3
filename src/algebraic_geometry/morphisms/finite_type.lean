/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.morphisms.ring_hom_properties
import algebraic_geometry.morphisms.quasi_compact

/-!
# Morphisms of finite type

A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.

A morphism of schemes is of finite type if it is both locally of finite type and quasi-compact.

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
class locally_of_finite_type (f : X ⟶ Y) : Prop :=
(of_finite_type_of_affine_subset :
  ∀ (U : Y.affine_opens) (V : X.affine_opens) (e : V.1 ≤ (opens.map f.1.base).obj U.1),
  (f.1.c.app (op U) ≫ X.presheaf.map (hom_of_le e).op).finite_type)

lemma _root_.ring_hom.finite_type_is_local : ring_hom.property_is_local @ring_hom.finite_type :=
sorry

lemma _root_.ring_hom.finite_type_stable_under_base_change :
  ring_hom.stable_under_base_change @ring_hom.finite_type := sorry

lemma _root_.ring_hom.finite_type_respects_iso : ring_hom.respects_iso @ring_hom.finite_type :=
ring_hom.finite_type_is_local.respects_iso

lemma locally_of_finite_type_eq :
  @locally_of_finite_type = affine_locally @ring_hom.finite_type :=
begin
  ext X Y f,
  rw [locally_of_finite_type_iff, affine_locally_iff_affine_opens_le],
  exact ring_hom.finite_type_respects_iso
end

@[priority 900]
instance locally_of_finite_type_of_is_open_immersion {X Y : Scheme} (f : X ⟶ Y)
  [is_open_immersion f] : locally_of_finite_type f :=
locally_of_finite_type_eq.symm ▸ affine_locally_of_is_open_immersion ring_hom.finite_type_is_local f

lemma locally_of_finite_type_stable_under_composition :
  stable_under_composition @locally_of_finite_type :=
locally_of_finite_type_eq.symm ▸ affine_locally_stable_under_composition ring_hom.finite_type_is_local

instance locally_of_finite_type_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [hf : locally_of_finite_type f] [hg : locally_of_finite_type g] :
  locally_of_finite_type (f ≫ g) :=
locally_of_finite_type_stable_under_composition f g hf hg

lemma locally_of_finite_type.affine_open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)]
  (𝒰' : ∀ i, Scheme.open_cover.{u} ((𝒰.pullback_cover f).obj i)) [∀ i j, is_affine ((𝒰' i).obj j)] :
  locally_of_finite_type f ↔ (∀ i j, (Scheme.Γ.map ((𝒰' i).map j ≫ pullback.snd).op).finite_type) :=
locally_of_finite_type_eq.symm ▸ ring_hom.finite_type_is_local.affine_open_cover_iff f 𝒰 𝒰'

lemma locally_of_finite_type.source_open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} X) :
  locally_of_finite_type f ↔ (∀ i, locally_of_finite_type (𝒰.map i ≫ f)) :=
locally_of_finite_type_eq.symm ▸ ring_hom.finite_type_is_local.source_open_cover_iff f 𝒰

lemma locally_of_finite_type.open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} Y) :
  locally_of_finite_type f ↔
    (∀ i, locally_of_finite_type (pullback.snd : pullback f (𝒰.map i) ⟶ _)) :=
locally_of_finite_type_eq.symm ▸
  ring_hom.finite_type_is_local.is_local_source_affine_locally.open_cover_iff f 𝒰

lemma locally_of_finite_type_respects_iso :
  respects_iso @locally_of_finite_type :=
locally_of_finite_type_eq.symm ▸ target_affine_locally_respects_iso
  (source_affine_locally_respects_iso ring_hom.finite_type_respects_iso)

lemma locally_of_finite_type_stable_under_base_change :
  stable_under_base_change @locally_of_finite_type :=
locally_of_finite_type_eq.symm ▸ affine_locally_stable_under_base_change ring_hom.finite_type_is_local
  ring_hom.finite_type_stable_under_base_change

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [locally_of_finite_type g] :
  locally_of_finite_type (pullback.fst : pullback f g ⟶ X) :=
locally_of_finite_type_stable_under_base_change f g infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [locally_of_finite_type f] :
  locally_of_finite_type (pullback.snd : pullback f g ⟶ Y) :=
locally_of_finite_type_stable_under_base_change.symmetry
  locally_of_finite_type_respects_iso f g infer_instance

class finite_type extends locally_of_finite_type f, quasi_compact f

@[priority 900]
instance of_finite_type_of_iso {X Y Z : Scheme} (f : X ⟶ Y) [is_iso f] : finite_type f := {}

instance of_finite_type_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [hf : finite_type f] [hg : finite_type g] : finite_type (f ≫ g) := {}

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [finite_type g] :
  finite_type (pullback.fst : pullback f g ⟶ X) := {}

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [finite_type f] :
  finite_type (pullback.snd : pullback f g ⟶ Y) := {}

end algebraic_geometry

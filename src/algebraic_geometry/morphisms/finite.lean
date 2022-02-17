/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.morphisms.ring_hom_properties

/-!
# Finite morphisms

A morphism of schemes is finite if it is affine and the component of the sheaf map on affine opens
is finite.

We show that this property is local, and is stable under compositions and base-changes.

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
class finite (f : X ⟶ Y) extends affine f : Prop :=
(is_finite_of_affine : ∀ U : opens Y.carrier, is_affine_open U → (f.1.c.app (op U)).finite)

lemma _root_.ring_hom.finite_respects_iso : ring_hom.respects_iso @ring_hom.finite := sorry

lemma finite_eq_affine_locally_finite :
  @finite = target_affine_locally (affine_and @ring_hom.finite) :=
by { ext, rw [finite_iff, affine_and_target_affine_locally_iff ring_hom.finite_respects_iso] }

lemma finite_respects_iso : respects_iso @finite :=
finite_eq_affine_locally_finite.symm ▸ affine_and_res ring_hom.finite_respects_iso

@[priority 900]
instance affine_of_is_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] : affine f :=
⟨λ U hU, hU.map_is_iso f⟩

instance affine_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [affine f] [affine g] : affine (f ≫ g) :=
begin
  constructor,
  intros U hU,
  rw [Scheme.comp_val_base, opens.map_comp_obj],
  apply affine.is_affine_preimage,
  apply affine.is_affine_preimage,
  exact hU
end

lemma affine_iff_affine_property :
  affine f ↔ target_affine_locally affine.affine_property f :=
(affine_iff f).trans ⟨λ H U, H U U.prop, λ H U hU, H ⟨U, hU⟩⟩

lemma affine_eq_affine_property :
  @affine = target_affine_locally affine.affine_property :=
by { ext, exact affine_iff_affine_property _ }

lemma affine_affine_property_is_local :
  affine_target_morphism_property.is_local affine.affine_property :=
begin
  split,
  { split,
    all_goals
    { rintros X Y Z _ _ _ (H : is_affine _),
      resetI },
    exacts [is_affine_of_iso e.hom, H] },
  { introv H,
    change is_affine_open _,
    rw Scheme.preimage_basic_open f r,
    exact (@@top_is_affine_open X H).basic_open_is_affine _ },
  { rintros X Y H f S hS hS',
    resetI,
    rw ← (top_is_affine_open Y).basic_open_union_eq_self_iff at hS,
    delta affine.affine_property,
    sorry }
end

lemma affine_affine_property_stable_under_base_change :
  affine_target_morphism_property.stable_under_base_change affine.affine_property :=
begin
  introv X H,
  delta affine.affine_property at H ⊢,
  resetI,
  apply_instance
end

lemma affine.affine_open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [affine f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)],
      ∀ (i : 𝒰.J), is_affine (pullback f (𝒰.map i)),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)] (i : 𝒰.J),
      is_affine (pullback f (𝒰.map i)),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_affine U] [is_open_immersion g],
      is_affine (pullback f g)] :=
affine_eq_affine_property.symm ▸
  affine_affine_property_is_local.affine_open_cover_tfae f

lemma affine.open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [affine f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
      affine (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
      affine (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (U : opens Y.carrier), affine (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
      affine (pullback.snd : pullback f g ⟶ _)] :=
affine_eq_affine_property.symm ▸
  affine_affine_property_is_local.open_cover_tfae f

lemma affine_over_affine_iff {X Y : Scheme} (f : X ⟶ Y) [is_affine Y] :
  affine f ↔ is_affine X :=
affine_eq_affine_property.symm ▸
  affine_affine_property_is_local.affine_target_iff f

lemma compact_space_iff_affine (X : Scheme) :
  is_affine X ↔ affine (terminal.from X) :=
(affine_over_affine_iff _).symm

lemma affine.affine_open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
  affine f ↔ ∀ i, is_affine (pullback f (𝒰.map i)) :=
affine_eq_affine_property.symm ▸
  affine_affine_property_is_local.affine_open_cover_iff f 𝒰

lemma affine.open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
  affine f ↔ ∀ i, affine (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
affine_eq_affine_property.symm ▸
  affine_affine_property_is_local.open_cover_iff f 𝒰

lemma affine_stable_under_base_change :
  stable_under_base_change @affine :=
affine_eq_affine_property.symm ▸
  affine_affine_property_is_local.stable_under_base_change
    affine_affine_property_stable_under_base_change

lemma affine_respects_iso : respects_iso @affine :=
affine_eq_affine_property.symm ▸
  target_affine_locally_respects_iso affine_affine_property_is_local.1

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [affine g] :
  affine (pullback.fst : pullback f g ⟶ X) :=
affine_stable_under_base_change f g infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [affine f] :
  affine (pullback.snd : pullback f g ⟶ Y) :=
affine_stable_under_base_change.symmetry affine_respects_iso f g infer_instance

instance {X : Scheme} (r : X.presheaf.obj (op ⊤)) :
  affine (X.of_restrict (X.basic_open r).open_embedding) :=
begin
  constructor,
  intros U hU,
  fapply (is_open_immersion.is_affine_open_iff (X.of_restrict _) _).mpr,
  swap,
  { apply_instance },
  convert hU.basic_open_is_affine (X.presheaf.map (hom_of_le le_top).op r),
  ext1,
  rw X.basic_open_res,
  dsimp [opens.map, opens.inclusion],
  rw [set.image_preimage_eq_inter_range, subtype.range_coe],
  refl
end

@[simps]
def affine_preimage {X Y : Scheme} (f : X ⟶ Y) [affine f] (U : Y.affine_opens) :
  X.affine_opens :=
⟨(opens.map f.1.base).obj (U : opens Y.carrier), affine.is_affine_preimage _ U.prop⟩

end algebraic_geometry

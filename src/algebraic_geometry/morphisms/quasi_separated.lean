/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.morphisms.quasi_compact

/-!
# Quasi-separated morphisms

A morphism of schemes `f : X ⟶ Y` is quasi-separated if the diagonal morphism `X ⟶ X ×[Y] X` is
quasi-compact.

A scheme is quasi-separated if the intersections of any two affine open sets is quasi-compact.

We show that a morphism is quasi-separated if the preimage of every affine open is quasi-separated.

We also show that this property is local, and is stable under compositions and base-changes.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
A morphism is `quasi-compact` if the underlying map of topological spaces is, i.e. if the preimages
of quasi-compact open sets are quasi-compact.
-/
@[mk_iff]
class quasi_separated (f : X ⟶ Y) : Prop :=
(diagonal_quasi_compact : quasi_compact (pullback.diagonal f))

@[mk_iff]
class is_quasi_separated (X : Scheme) : Prop :=
(inter_is_compact : ∀ (U V : X.affine_opens), is_compact (U ∩ V : set X.carrier) )

lemma quasi_compact_affine_property_iff_is_quasi_separated {X Y : Scheme} [is_affine Y]
  (f : X ⟶ Y) :
  diagonal_is.affine_property quasi_compact.affine_property f ↔ is_quasi_separated X :=
begin
  delta diagonal_is.affine_property,
  rw is_quasi_separated_iff,
  split,
  { intros H U V,
    haveI : is_affine _ := U.2,
    haveI : is_affine _ := V.2,
    let g : pullback (X.of_restrict U.1.open_embedding) (X.of_restrict V.1.open_embedding) ⟶ X :=
      pullback.fst ≫ X.of_restrict _,
    have : is_open_immersion g := infer_instance,
    have e := homeomorph.of_embedding _ this.base_open.to_embedding,
    rw is_open_immersion.range_pullback_one at e,
    erw [subtype.range_coe, subtype.range_coe] at e,
    rw is_compact_iff_compact_space,
    exact @@homeomorph.compact_space _ _ (H _ _) e },
  { introv H h₁ h₂,
    resetI,
    let g : pullback f₁ f₂ ⟶ X := pullback.fst ≫ f₁,
    have : is_open_immersion g := infer_instance,
    have e := homeomorph.of_embedding _ this.base_open.to_embedding,
    rw is_open_immersion.range_pullback_one at e,
    simp_rw is_compact_iff_compact_space at H,
    exact @@homeomorph.compact_space _ _
      (H ⟨⟨_, h₁.base_open.open_range⟩, range_is_affine_open_of_open_immersion _⟩
        ⟨⟨_, h₂.base_open.open_range⟩, range_is_affine_open_of_open_immersion _⟩) e.symm },
end

lemma quasi_separated_eq_diagonal_is_quasi_compact :
  @quasi_separated = diagonal_is @quasi_compact :=
by { ext, exact quasi_separated_iff _ }

lemma quasi_compact_affine_property_eq_is_quasi_separated :
  diagonal_is.affine_property quasi_compact.affine_property =
    (λ X Y f _, is_quasi_separated X) :=
by { ext, rw quasi_compact_affine_property_iff_is_quasi_separated }

lemma quasi_separated_eq_affine_property :
  @quasi_separated =
    target_affine_locally (diagonal_is.affine_property quasi_compact.affine_property) :=
begin
  rw [quasi_separated_eq_diagonal_is_quasi_compact, quasi_compact_eq_affine_property],
  exact (diagonal_is_eq_diagonal_is_affine_property _ quasi_compact_affine_property_is_local)
end

lemma quasi_separated_affine_property_is_local :
  (diagonal_is.affine_property quasi_compact.affine_property).is_local :=
diagonal_is_affine_property.is_local _ quasi_compact_affine_property_is_local

@[priority 900]
instance quasi_separated_of_mono {X Y : Scheme} (f : X ⟶ Y) [mono f] : quasi_separated f :=
⟨infer_instance⟩

lemma quasi_separated_stable_under_composition :
  stable_under_composition @quasi_separated :=
quasi_separated_eq_diagonal_is_quasi_compact.symm ▸
  diagonal_is_stable_under_composition @quasi_compact
    quasi_compact_stable_under_base_change
    quasi_compact_respects_iso
    quasi_compact_stable_under_composition

lemma quasi_separated_stable_under_base_change :
  stable_under_base_change @quasi_separated :=
quasi_separated_eq_diagonal_is_quasi_compact.symm ▸
  diagonal_is_stable_under_base_change @quasi_compact
    quasi_compact_stable_under_base_change
    quasi_compact_respects_iso

instance quasi_separated_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [quasi_separated f] [quasi_separated g] : quasi_separated (f ≫ g) :=
quasi_separated_stable_under_composition f g infer_instance infer_instance

lemma quasi_separated_respects_iso : respects_iso @quasi_separated :=
quasi_separated_eq_diagonal_is_quasi_compact.symm ▸
  diagonal_is_respects_iso @quasi_compact quasi_compact_respects_iso

lemma quasi_separated.affine_open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [quasi_separated f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)],
      ∀ (i : 𝒰.J), is_quasi_separated (pullback f (𝒰.map i)),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)] (i : 𝒰.J),
      is_quasi_separated (pullback f (𝒰.map i)),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_affine U] [is_open_immersion g],
      is_quasi_separated (pullback f g)] :=
begin
  have := quasi_separated_affine_property_is_local,
  rw quasi_separated_eq_affine_property,
  rw quasi_compact_affine_property_eq_is_quasi_separated at this ⊢,
  exact this.affine_open_cover_tfae f
end

lemma quasi_separated.open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [quasi_separated f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
      quasi_separated (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
      quasi_separated (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (U : opens Y.carrier), quasi_separated (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
      quasi_separated (pullback.snd : pullback f g ⟶ _)] :=
quasi_separated_eq_affine_property.symm ▸
  quasi_separated_affine_property_is_local.open_cover_tfae f

lemma quasi_separated_over_affine_iff {X Y : Scheme} (f : X ⟶ Y) [is_affine Y] :
  quasi_separated f ↔ is_quasi_separated X :=
by rw [quasi_separated_eq_affine_property,
  quasi_separated_affine_property_is_local.affine_target_iff f,
  quasi_compact_affine_property_eq_is_quasi_separated]

lemma compact_space_iff_quasi_separated (X : Scheme) :
  is_quasi_separated X ↔ quasi_separated (terminal.from X) :=
(quasi_separated_over_affine_iff _).symm

lemma quasi_separated.affine_open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
  quasi_separated f ↔ ∀ i, is_quasi_separated (pullback f (𝒰.map i)) :=
begin
  rw [quasi_separated_eq_affine_property,
    quasi_separated_affine_property_is_local.affine_open_cover_iff f 𝒰],
  simp_rw quasi_compact_affine_property_eq_is_quasi_separated,
end

lemma quasi_separated.open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
  quasi_separated f ↔ ∀ i, quasi_separated (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
quasi_separated_eq_affine_property.symm ▸
  quasi_separated_affine_property_is_local.open_cover_iff f 𝒰

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [quasi_separated g] :
  quasi_separated (pullback.fst : pullback f g ⟶ X) :=
quasi_separated_stable_under_base_change f g infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [quasi_separated f] :
  quasi_separated (pullback.snd : pullback f g ⟶ Y) :=
quasi_separated_stable_under_base_change.symmetry quasi_separated_respects_iso f g infer_instance

instance {X Y Z: Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [quasi_separated f] [quasi_separated g] :
  quasi_separated (f ≫ g) :=
quasi_separated_stable_under_composition f g infer_instance infer_instance


end algebraic_geometry

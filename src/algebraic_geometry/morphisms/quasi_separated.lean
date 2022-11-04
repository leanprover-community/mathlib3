/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.morphisms.quasi_compact
import topology.quasi_separated

/-!
# Quasi-separated morphisms

A morphism of schemes `f : X ⟶ Y` is quasi-separated if the diagonal morphism `X ⟶ X ×[Y] X` is
quasi-compact.

A scheme is quasi-separated if the intersections of any two affine open sets is quasi-compact.
(`algebraic_geometry.quasi_separated_space_iff_affine`)

We show that a morphism is quasi-separated if the preimage of every affine open is quasi-separated.

We also show that this property is local at the target,
and is stable under compositions and base-changes.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism is `quasi_separated` if diagonal map is quasi-compact. -/
@[mk_iff]
class quasi_separated (f : X ⟶ Y) : Prop :=
(diagonal_quasi_compact : quasi_compact (pullback.diagonal f))

/-- The `affine_target_morphism_property` corresponding to `quasi_separated`, asserting that the
domain is a quasi-separated scheme. -/
def quasi_separated.affine_property : affine_target_morphism_property :=
(λ X Y f _, quasi_separated_space X.carrier)

lemma quasi_separated_space_iff_affine (X : Scheme) :
  quasi_separated_space X.carrier ↔ ∀ (U V : X.affine_opens), is_compact (U ∩ V : set X.carrier) :=
begin
  rw quasi_separated_space_iff,
  split,
  { intros H U V, exact H U V U.1.2 U.2.is_compact V.1.2 V.2.is_compact },
  { intros H,
    suffices : ∀ (U : opens X.carrier) (hU : is_compact U.1) (V : opens X.carrier)
      (hV : is_compact V.1), is_compact (U ⊓ V).1,
    { intros U V hU hU' hV hV', exact this ⟨U, hU⟩ hU' ⟨V, hV⟩ hV' },
    intros U hU V hV,
    apply compact_open_induction_on V hV,
    { simp },
    { intros S hS V hV,
      change is_compact (U.1 ∩ (S.1 ∪ V.1)),
      rw set.inter_union_distrib_left,
      apply hV.union,
      clear hV,
      apply compact_open_induction_on U hU,
      { simp },
      { intros S hS W hW,
      change is_compact ((S.1 ∪ W.1) ∩ V.1),
        rw set.union_inter_distrib_right,
        apply hW.union,
        apply H } } }
end

lemma quasi_compact_affine_property_iff_quasi_separated_space {X Y : Scheme} [is_affine Y]
  (f : X ⟶ Y) :
  quasi_compact.affine_property.diagonal f ↔ quasi_separated_space X.carrier :=
begin
  delta affine_target_morphism_property.diagonal,
  rw quasi_separated_space_iff_affine,
  split,
  { intros H U V,
    haveI : is_affine _ := U.2,
    haveI : is_affine _ := V.2,
    let g : pullback (X.of_restrict U.1.open_embedding) (X.of_restrict V.1.open_embedding) ⟶ X :=
      pullback.fst ≫ X.of_restrict _,
    have : is_open_immersion g := infer_instance,
    have e := homeomorph.of_embedding _ this.base_open.to_embedding,
    rw is_open_immersion.range_pullback_to_base_of_left at e,
    erw [subtype.range_coe, subtype.range_coe] at e,
    rw is_compact_iff_compact_space,
    exact @@homeomorph.compact_space _ _ (H _ _) e },
  { introv H h₁ h₂,
    resetI,
    let g : pullback f₁ f₂ ⟶ X := pullback.fst ≫ f₁,
    have : is_open_immersion g := infer_instance,
    have e := homeomorph.of_embedding _ this.base_open.to_embedding,
    rw is_open_immersion.range_pullback_to_base_of_left at e,
    simp_rw is_compact_iff_compact_space at H,
    exact @@homeomorph.compact_space _ _
      (H ⟨⟨_, h₁.base_open.open_range⟩, range_is_affine_open_of_open_immersion _⟩
        ⟨⟨_, h₂.base_open.open_range⟩, range_is_affine_open_of_open_immersion _⟩) e.symm },
end

lemma quasi_separated_eq_diagonal_is_quasi_compact :
  @quasi_separated = morphism_property.diagonal @quasi_compact :=
by { ext, exact quasi_separated_iff _ }

lemma quasi_compact_affine_property_diagonal_eq :
  quasi_compact.affine_property.diagonal = quasi_separated.affine_property :=
by { ext, rw quasi_compact_affine_property_iff_quasi_separated_space, refl }

lemma quasi_separated_eq_affine_property_diagonal :
  @quasi_separated =
    target_affine_locally quasi_compact.affine_property.diagonal :=
begin
  rw [quasi_separated_eq_diagonal_is_quasi_compact, quasi_compact_eq_affine_property],
  exact diagonal_target_affine_locally_eq_target_affine_locally
    _ quasi_compact.affine_property_is_local
end

lemma quasi_separated_eq_affine_property :
  @quasi_separated =
    target_affine_locally quasi_separated.affine_property :=
by rw [quasi_separated_eq_affine_property_diagonal, quasi_compact_affine_property_diagonal_eq]

lemma quasi_separated.affine_property_is_local :
  quasi_separated.affine_property.is_local :=
quasi_compact_affine_property_diagonal_eq ▸
quasi_compact.affine_property_is_local.diagonal

@[priority 900]
instance quasi_separated_of_mono {X Y : Scheme} (f : X ⟶ Y) [mono f] : quasi_separated f :=
⟨infer_instance⟩

lemma quasi_separated_stable_under_composition :
  morphism_property.stable_under_composition @quasi_separated :=
quasi_separated_eq_diagonal_is_quasi_compact.symm ▸
  quasi_compact_stable_under_composition.diagonal
    quasi_compact_respects_iso
    quasi_compact_stable_under_base_change

lemma quasi_separated_stable_under_base_change :
  morphism_property.stable_under_base_change @quasi_separated :=
quasi_separated_eq_diagonal_is_quasi_compact.symm ▸
  quasi_compact_stable_under_base_change.diagonal
    quasi_compact_respects_iso

instance quasi_separated_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [quasi_separated f] [quasi_separated g] : quasi_separated (f ≫ g) :=
quasi_separated_stable_under_composition f g infer_instance infer_instance

lemma quasi_separated_respects_iso : morphism_property.respects_iso @quasi_separated :=
quasi_separated_eq_diagonal_is_quasi_compact.symm ▸
  quasi_compact_respects_iso.diagonal

lemma quasi_separated.affine_open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [quasi_separated f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)],
      ∀ (i : 𝒰.J), quasi_separated_space (pullback f (𝒰.map i)).carrier,
    ∀ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)] (i : 𝒰.J),
      quasi_separated_space (pullback f (𝒰.map i)).carrier,
    ∀ {U : Scheme} (g : U ⟶ Y) [is_affine U] [is_open_immersion g],
      quasi_separated_space (pullback f g).carrier,
    ∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)]
      (𝒰' : Π (i : 𝒰.J), Scheme.open_cover.{u} (pullback f (𝒰.map i)))
      [∀ i j, is_affine ((𝒰' i).obj j)], by exactI ∀ (i : 𝒰.J) (j k : (𝒰' i).J),
        compact_space (pullback ((𝒰' i).map j) ((𝒰' i).map k)).carrier] :=
begin
  have := quasi_compact.affine_property_is_local.diagonal_affine_open_cover_tfae f,
  simp_rw [← quasi_compact_eq_affine_property,
    ← quasi_separated_eq_diagonal_is_quasi_compact,
    quasi_compact_affine_property_diagonal_eq] at this,
  exact this
end

lemma quasi_separated.is_local_at_target :
  property_is_local_at_target @quasi_separated :=
quasi_separated_eq_affine_property_diagonal.symm ▸
  quasi_compact.affine_property_is_local.diagonal.target_affine_locally_is_local

lemma quasi_separated.open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [quasi_separated f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
      quasi_separated (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
      quasi_separated (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (U : opens Y.carrier), quasi_separated (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
      quasi_separated (pullback.snd : pullback f g ⟶ _),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤),
      ∀ i, quasi_separated (f ∣_ (U i))] :=
quasi_separated.is_local_at_target.open_cover_tfae f

lemma quasi_separated_over_affine_iff {X Y : Scheme} (f : X ⟶ Y) [is_affine Y] :
  quasi_separated f ↔ quasi_separated_space X.carrier :=
by rw [quasi_separated_eq_affine_property,
  quasi_separated.affine_property_is_local.affine_target_iff f,
  quasi_separated.affine_property]

lemma quasi_separated_space_iff_quasi_separated (X : Scheme) :
  quasi_separated_space X.carrier ↔ quasi_separated (terminal.from X) :=
(quasi_separated_over_affine_iff _).symm

lemma quasi_separated.affine_open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
  quasi_separated f ↔ ∀ i, quasi_separated_space (pullback f (𝒰.map i)).carrier :=
begin
  rw [quasi_separated_eq_affine_property,
    quasi_separated.affine_property_is_local.affine_open_cover_iff f 𝒰],
  refl,
end

lemma quasi_separated.open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  (f : X ⟶ Y) :
  quasi_separated f ↔ ∀ i, quasi_separated (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
quasi_separated.is_local_at_target.open_cover_iff f 𝒰

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [quasi_separated g] :
  quasi_separated (pullback.fst : pullback f g ⟶ X) :=
quasi_separated_stable_under_base_change.fst f g infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [quasi_separated f] :
  quasi_separated (pullback.snd : pullback f g ⟶ Y) :=
quasi_separated_stable_under_base_change.snd f g infer_instance

instance {X Y Z: Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [quasi_separated f] [quasi_separated g] :
  quasi_separated (f ≫ g) :=
quasi_separated_stable_under_composition f g infer_instance infer_instance

lemma quasi_separated_space_of_quasi_separated {X Y : Scheme} (f : X ⟶ Y)
  [hY : quasi_separated_space Y.carrier] [quasi_separated f] : quasi_separated_space X.carrier :=
begin
  rw quasi_separated_space_iff_quasi_separated at hY ⊢,
  have : f ≫ terminal.from Y = terminal.from X := terminal_is_terminal.hom_ext _ _,
  rw ← this,
  resetI, apply_instance
end

instance quasi_separated_space_of_is_affine (X : Scheme) [is_affine X] :
  quasi_separated_space X.carrier :=
begin
  constructor,
  intros U V hU hU' hV hV',
  obtain ⟨s, hs, e⟩ := (is_compact_open_iff_eq_basic_open_union _).mp ⟨hU', hU⟩,
  obtain ⟨s', hs', e'⟩ := (is_compact_open_iff_eq_basic_open_union _).mp ⟨hV', hV⟩,
  rw [e, e', set.Union₂_inter],
  simp_rw [set.inter_Union₂],
  apply hs.is_compact_bUnion,
  { intros i hi,
    apply hs'.is_compact_bUnion,
    intros i' hi',
    change is_compact (X.basic_open i ⊓ X.basic_open i').1,
    rw ← Scheme.basic_open_mul,
    exact ((top_is_affine_open _).basic_open_is_affine _).is_compact }
end

lemma is_affine_open.is_quasi_separated {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
  is_quasi_separated (U : set X.carrier)  :=
begin
  rw is_quasi_separated_iff_quasi_separated_space,
  exacts [@@algebraic_geometry.quasi_separated_space_of_is_affine _ hU, U.prop],
end

lemma quasi_separated_of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [H : quasi_separated (f ≫ g)] : quasi_separated f :=
begin
  rw (quasi_separated.affine_open_cover_tfae f).out 0 1,
  rw (quasi_separated.affine_open_cover_tfae (f ≫ g)).out 0 2 at H,
  use (Z.affine_cover.pullback_cover g).bind (λ x, Scheme.affine_cover _),
  split, { intro i, dsimp, apply_instance },
  rintro ⟨i, j⟩, dsimp at *,
  specialize H _ i,
  refine @@quasi_separated_space_of_quasi_separated _ H _,
  { exact pullback.map _ _ _ _ (𝟙 _) _ _ (by simp) (category.comp_id _) ≫
      (pullback_right_pullback_fst_iso g (Z.affine_cover.map i) f).hom },
  { apply algebraic_geometry.quasi_separated_of_mono }
end

end algebraic_geometry

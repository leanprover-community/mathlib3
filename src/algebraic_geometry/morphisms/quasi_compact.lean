/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.morphisms.basic
import topology.spectral.hom
import algebraic_geometry.limits

/-!
# Quasi-compact morphisms

A morphism of schemes is quasi-compact if the preimages of quasi-compact open sets are
quasi-compact.

It suffices to check that preimages of affine open sets are compact
(`quasi_compact_iff_forall_affine`).

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
class quasi_compact (f : X ⟶ Y) : Prop :=
(is_compact_preimage : ∀ U : set Y.carrier, is_open U → is_compact U → is_compact (f.1.base ⁻¹' U))

lemma quasi_compact_iff_spectral : quasi_compact f ↔ is_spectral_map f.1.base :=
⟨λ ⟨h⟩, ⟨by continuity, h⟩, λ h, ⟨h.2⟩⟩

/-- The `affine_target_morphism_property` corresponding to `quasi_compact`, asserting that the
domain is a quasi-compact scheme. -/
def quasi_compact.affine_property : affine_target_morphism_property :=
λ X Y f hf, compact_space X.carrier

@[priority 900]
instance quasi_compact_of_is_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] : quasi_compact f :=
begin
  constructor,
  intros U hU hU',
  convert hU'.image (inv f.1.base).continuous_to_fun using 1,
  rw set.image_eq_preimage_of_inverse,
  delta function.left_inverse,
  exacts [is_iso.inv_hom_id_apply f.1.base, is_iso.hom_inv_id_apply f.1.base]
end

instance quasi_compact_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [quasi_compact f] [quasi_compact g] : quasi_compact (f ≫ g) :=
begin
  constructor,
  intros U hU hU',
  rw [Scheme.comp_val_base, coe_comp, set.preimage_comp],
  apply quasi_compact.is_compact_preimage,
  { exact continuous.is_open_preimage (by continuity) _ hU },
  apply quasi_compact.is_compact_preimage; assumption
end

lemma is_compact_open_iff_eq_finset_affine_union {X : Scheme} (U : set X.carrier) :
  is_compact U ∧ is_open U ↔
    ∃ (s : set X.affine_opens), s.finite ∧ U = ⋃ (i : X.affine_opens) (h : i ∈ s), i :=
begin
  apply opens.is_compact_open_iff_eq_finite_Union_of_is_basis
    (coe : X.affine_opens → opens X.carrier),
  { rw subtype.range_coe, exact is_basis_affine_open X },
  { intro i, exact i.2.is_compact }
end

lemma is_compact_open_iff_eq_basic_open_union {X : Scheme} [is_affine X] (U : set X.carrier) :
  is_compact U ∧ is_open U ↔
    ∃ (s : set (X.presheaf.obj (op ⊤))), s.finite ∧
      U = ⋃ (i : X.presheaf.obj (op ⊤)) (h : i ∈ s), X.basic_open i :=
begin
  apply opens.is_compact_open_iff_eq_finite_Union_of_is_basis,
  { exact is_basis_basic_open X },
  { intro i, exact ((top_is_affine_open _).basic_open_is_affine _).is_compact }
end

lemma quasi_compact_iff_forall_affine : quasi_compact f ↔
  ∀ U : opens Y.carrier, is_affine_open U → is_compact (f.1.base ⁻¹' (U : set Y.carrier)) :=
begin
  rw quasi_compact_iff,
  refine ⟨λ H U hU, H U U.prop hU.is_compact, _⟩,
  intros H U hU hU',
  obtain ⟨S, hS, rfl⟩ := (is_compact_open_iff_eq_finset_affine_union U).mp ⟨hU', hU⟩,
  simp only [set.preimage_Union, subtype.val_eq_coe],
  exact hS.is_compact_bUnion (λ i _, H i i.prop)
end

@[simp] lemma quasi_compact.affine_property_to_property {X Y : Scheme} (f : X ⟶ Y) :
  (quasi_compact.affine_property : _).to_property f ↔
    is_affine Y ∧ compact_space X.carrier :=
by { delta affine_target_morphism_property.to_property quasi_compact.affine_property, simp }

lemma quasi_compact_iff_affine_property :
  quasi_compact f ↔ target_affine_locally quasi_compact.affine_property f :=
begin
  rw quasi_compact_iff_forall_affine,
  transitivity (∀ U : Y.affine_opens, is_compact (f.1.base ⁻¹' (U : set Y.carrier))),
  { exact ⟨λ h U, h U U.prop, λ h U hU, h ⟨U, hU⟩⟩ },
  apply forall_congr,
  exact λ _, is_compact_iff_compact_space,
end

lemma quasi_compact_eq_affine_property :
  @quasi_compact = target_affine_locally quasi_compact.affine_property :=
by { ext, exact quasi_compact_iff_affine_property _ }

lemma is_compact_basic_open (X : Scheme) {U : opens X.carrier} (hU : is_compact (U : set X.carrier))
   (f : X.presheaf.obj (op U)) : is_compact (X.basic_open f : set X.carrier) :=
begin
  classical,
  refine ((is_compact_open_iff_eq_finset_affine_union _).mpr _).1,
  obtain ⟨s, hs, e⟩ := (is_compact_open_iff_eq_finset_affine_union _).mp ⟨hU, U.prop⟩,
  let g : s → X.affine_opens,
  { intro V,
    use V.1 ⊓ X.basic_open f,
    have : V.1.1 ⟶ U,
    { apply hom_of_le, change _ ⊆ (U : set X.carrier), rw e,
      convert @set.subset_Union₂ _ _ _ (λ (U : X.affine_opens) (h : U ∈ s), ↑U) V V.prop using 1,
      refl },
    erw ← X.to_LocallyRingedSpace.to_RingedSpace.basic_open_res this.op,
    exact is_affine_open.basic_open_is_affine V.1.prop _ },
  haveI : finite s := hs.to_subtype,
  refine ⟨set.range g, set.finite_range g, _⟩,
  refine (set.inter_eq_right_iff_subset.mpr (RingedSpace.basic_open_le _ _)).symm.trans _,
  rw [e, set.Union₂_inter],
  apply le_antisymm; apply set.Union₂_subset,
  { intros i hi,
    refine set.subset.trans _ (set.subset_Union₂ _ (set.mem_range_self ⟨i, hi⟩)),
    exact set.subset.rfl },
  { rintro ⟨i, hi⟩ ⟨⟨j, hj⟩, hj'⟩,
    rw ← hj',
    refine set.subset.trans _ (set.subset_Union₂ j hj),
    exact set.subset.rfl }
end

lemma quasi_compact.affine_property_is_local :
  (quasi_compact.affine_property : _).is_local :=
begin
  split,
  { apply affine_target_morphism_property.respects_iso_mk; rintros X Y Z _ _ _ H,
    exacts [@@homeomorph.compact_space _ _ H (Top.homeo_of_iso (as_iso e.inv.1.base)), H] },
  { introv H,
    delta quasi_compact.affine_property at H ⊢,
    change compact_space ((opens.map f.val.base).obj (Y.basic_open r)),
    rw Scheme.preimage_basic_open f r,
    erw ← is_compact_iff_compact_space,
    rw ← is_compact_univ_iff at H,
    exact is_compact_basic_open X H _ },
  { rintros X Y H f S hS hS',
    resetI,
    rw ← is_affine_open.basic_open_union_eq_self_iff at hS,
    delta quasi_compact.affine_property,
    rw ← is_compact_univ_iff,
    change is_compact ((opens.map f.val.base).obj ⊤).1,
    rw ← hS,
    dsimp [opens.map],
    simp only [opens.coe_supr, set.preimage_Union, subtype.val_eq_coe],
    exacts [is_compact_Union (λ i, is_compact_iff_compact_space.mpr (hS' i)),
      top_is_affine_open _] }
end

lemma quasi_compact.affine_open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [quasi_compact f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)],
      ∀ (i : 𝒰.J), compact_space (pullback f (𝒰.map i)).carrier,
    ∀ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)] (i : 𝒰.J),
      compact_space (pullback f (𝒰.map i)).carrier,
    ∀ {U : Scheme} (g : U ⟶ Y) [is_affine U] [is_open_immersion g],
      compact_space (pullback f g).carrier,
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤) (hU' : ∀ i, is_affine_open (U i)),
      ∀ i, compact_space (f.1.base ⁻¹' (U i).1)] :=
quasi_compact_eq_affine_property.symm ▸
  quasi_compact.affine_property_is_local.affine_open_cover_tfae f

lemma quasi_compact.is_local_at_target :
  property_is_local_at_target @quasi_compact :=
quasi_compact_eq_affine_property.symm ▸
  quasi_compact.affine_property_is_local.target_affine_locally_is_local

lemma quasi_compact.open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [quasi_compact f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
      quasi_compact (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
      quasi_compact (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (U : opens Y.carrier), quasi_compact (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
      quasi_compact (pullback.snd : pullback f g ⟶ _),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤), ∀ i, quasi_compact (f ∣_ (U i))] :=
quasi_compact_eq_affine_property.symm ▸
  quasi_compact.affine_property_is_local.target_affine_locally_is_local.open_cover_tfae f

lemma quasi_compact_over_affine_iff {X Y : Scheme} (f : X ⟶ Y) [is_affine Y] :
  quasi_compact f ↔ compact_space X.carrier :=
quasi_compact_eq_affine_property.symm ▸
  quasi_compact.affine_property_is_local.affine_target_iff f

lemma compact_space_iff_quasi_compact (X : Scheme) :
  compact_space X.carrier ↔ quasi_compact (terminal.from X) :=
(quasi_compact_over_affine_iff _).symm

lemma quasi_compact.affine_open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
  quasi_compact f ↔ ∀ i, compact_space (pullback f (𝒰.map i)).carrier :=
quasi_compact_eq_affine_property.symm ▸
  quasi_compact.affine_property_is_local.affine_open_cover_iff f 𝒰

lemma quasi_compact.open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y) (f : X ⟶ Y) :
  quasi_compact f ↔ ∀ i, quasi_compact (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
quasi_compact_eq_affine_property.symm ▸
  quasi_compact.affine_property_is_local.target_affine_locally_is_local.open_cover_iff f 𝒰

lemma quasi_compact_respects_iso : morphism_property.respects_iso @quasi_compact :=
quasi_compact_eq_affine_property.symm ▸
  target_affine_locally_respects_iso quasi_compact.affine_property_is_local.1

lemma quasi_compact_stable_under_composition :
  morphism_property.stable_under_composition @quasi_compact :=
λ _ _ _ _ _ _ _, by exactI infer_instance

local attribute [-simp] PresheafedSpace.as_coe SheafedSpace.as_coe

lemma quasi_compact.affine_property_stable_under_base_change :
  quasi_compact.affine_property.stable_under_base_change :=
begin
  intros X Y S _ _ f g h,
  rw quasi_compact.affine_property at h ⊢,
  resetI,
  let 𝒰 := Scheme.pullback.open_cover_of_right Y.affine_cover.finite_subcover f g,
  haveI : finite 𝒰.J,
  { dsimp [𝒰], apply_instance },
  haveI : ∀ i, compact_space (𝒰.obj i).carrier,
  { intro i, dsimp, apply_instance },
  exact 𝒰.compact_space,
end

lemma quasi_compact_stable_under_base_change :
  morphism_property.stable_under_base_change @quasi_compact :=
quasi_compact_eq_affine_property.symm ▸
  quasi_compact.affine_property_is_local.stable_under_base_change
    quasi_compact.affine_property_stable_under_base_change

variables {Z : Scheme.{u}}

instance (f : X ⟶ Z) (g : Y ⟶ Z) [quasi_compact g] :
  quasi_compact (pullback.fst : pullback f g ⟶ X) :=
quasi_compact_stable_under_base_change.fst f g infer_instance

instance (f : X ⟶ Z) (g : Y ⟶ Z) [quasi_compact f] :
  quasi_compact (pullback.snd : pullback f g ⟶ Y) :=
quasi_compact_stable_under_base_change.snd f g infer_instance

@[elab_as_eliminator]
lemma compact_open_induction_on {P : opens X.carrier → Prop} (S : opens X.carrier)
  (hS : is_compact S.1)
  (h₁ : P ⊥)
  (h₂ : ∀ (S : opens X.carrier) (hS : is_compact S.1) (U : X.affine_opens), P S → P (S ⊔ U)) :
    P S :=
begin
  classical,
  obtain ⟨s, hs, hs'⟩ := (is_compact_open_iff_eq_finset_affine_union S.1).mp ⟨hS, S.2⟩,
  replace hs' : S = supr (λ i : s, (i : opens X.carrier)) := by { ext1, simpa using hs' },
  subst hs',
  apply hs.induction_on,
  { convert h₁, rw supr_eq_bot, rintro ⟨_, h⟩, exact h.elim },
  { intros x s h₃ hs h₄,
    have : is_compact (⨆ i : s, (i : opens X.carrier)).1,
    { refine ((is_compact_open_iff_eq_finset_affine_union _).mpr _).1, exact ⟨s, hs, by simp⟩ },
    convert h₂ _ this x h₄,
    simp only [coe_coe],
    rw [supr_subtype, sup_comm],
    conv_rhs { rw supr_subtype },
    exact supr_insert }
end

end algebraic_geometry

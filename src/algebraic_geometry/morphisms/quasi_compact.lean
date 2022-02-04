/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.morphisms.basic

/-!
# Quasi-compact morphisms

A morphism of schemes is quasi-compact if the preimages of quasi-compact open sets are
quasi-compact.

It suffices to check that preimages of affine open sets are compact
(`quasi_compact_iff_forall_affine`).

We show that this property is local, and is stable under compositions and base-changes.

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

def quasi_compact.affine_property : affine_target_morphism_property :=
λ X Y f hf, compact_space X.carrier

@[simp] lemma quasi_compact_affine_property_to_property {X Y : Scheme} (f : X ⟶ Y) :
  affine_target_morphism_property.to_property quasi_compact.affine_property f ↔
    is_affine Y ∧ compact_space X.carrier :=
by { delta affine_target_morphism_property.to_property quasi_compact.affine_property, simp }

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
    ∃ (s : finset { U : opens X.carrier | is_affine_open U }), U = ⋃ (i : s), i :=
begin
  classical,
  split,
  { rintro ⟨h₁, h₂⟩,
    obtain ⟨β, f, e, hf⟩ := (is_basis_affine_open X).open_eq_Union h₂,
    let hf' := λ i, (show is_open (f i), from (hf i).some_spec.2 ▸ (hf i).some.prop),
    obtain ⟨t, ht⟩ := h₁.elim_finite_subcover f hf' (by rw e),
    let f' : β → { U : opens X.carrier | is_affine_open U } :=
      λ i, ⟨⟨f i, hf' i⟩, by { convert (hf i).some_spec.1, ext1, exact (hf i).some_spec.2.symm }⟩,
    use t.image f',
    apply le_antisymm,
    { refine set.subset.trans ht _,
      simp only [set.Union_subset_iff, coe_coe],
      intros i hi,
      exact set.subset_Union (coe : t.image f' → set X.carrier) ⟨_, finset.mem_image_of_mem _ hi⟩ },
    { apply set.Union_subset,
      rintro ⟨i, hi⟩,
      obtain ⟨j, hj, rfl⟩ := finset.mem_image.mp hi,
      rw e,
      exact set.subset_Union f j } },
  { rintro ⟨s, rfl⟩,
    split,
    { convert @finset.compact_bUnion _ _ _ s.attach coe _,
      { ext, simpa },
      { exact λ i _, i.1.prop.is_compact } },
    { apply is_open_Union, rintro i, exact i.1.1.prop } },
end

lemma quasi_compact_iff_forall_affine : quasi_compact f ↔
  ∀ U : opens Y.carrier, is_affine_open U → is_compact (f.1.base ⁻¹' (U : set Y.carrier)) :=
begin
  rw quasi_compact_iff,
  refine ⟨λ H U hU, H U U.prop hU.is_compact, _⟩,
  intros H U hU hU',
  obtain ⟨S, rfl⟩ := (is_compact_open_iff_eq_finset_affine_union U).mp ⟨hU', hU⟩,
  simp only [set.preimage_Union, subtype.val_eq_coe],
  convert S.compact_bUnion (λ i _, H i i.prop) using 1,
  exact set.Union_subtype _ _
end

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
  obtain ⟨s, hs⟩ := (is_compact_open_iff_eq_finset_affine_union _).mp ⟨hU, U.prop⟩,
  let g : s → X.affine_opens,
  { intro V,
    use V.1 ∩ X.basic_open f,
    have : V.1.1 ⟶ U,
    { apply hom_of_le, change _ ⊆ (U : set X.carrier), rw hs, exact set.subset_Union _ V },
    erw ← X.to_LocallyRingedSpace.to_RingedSpace.basic_open_res this.op,
    exact is_affine_open.basic_open_is_affine V.1.prop _ },
  use s.attach.image g,
  refine (set.inter_eq_right_iff_subset.mpr (RingedSpace.basic_open_subset _ _)).symm.trans _,
  rw [hs, set.Union_inter],
  apply le_antisymm; apply set.Union_subset,
  { intro i,
    refine set.subset.trans _
      (set.subset_Union _ (⟨_, finset.mem_image_of_mem g (s.mem_attach i)⟩ : s.attach.image g)),
    exact set.subset.rfl },
  { rintro ⟨i, hi⟩,
    obtain ⟨j : s, hj, rfl⟩ := finset.mem_image.mp hi,
    refine set.subset.trans _ (set.subset_Union _ j),
    exact set.subset.rfl }
end

lemma quasi_compact_affine_property_is_local :
  affine_target_morphism_property.is_local quasi_compact.affine_property :=
begin
  split,
  { split; intros X Y Z _ _ _ H,
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
    simp only [opens.supr_s, set.preimage_Union, subtype.val_eq_coe],
    exacts [compact_Union (λ i, is_compact_iff_compact_space.mpr (hS' i)), top_is_affine_open _] }
end

lemma Scheme.open_cover.Union_range {X : Scheme} (𝒰 : X.open_cover) :
  (⋃ i, set.range (𝒰.map i).1.base) = set.univ :=
begin
  rw set.eq_univ_iff_forall,
  intros x,
  rw set.mem_Union,
  exact ⟨𝒰.f x, 𝒰.covers x⟩
end

lemma Scheme.open_cover.compact_space {X : Scheme} (𝒰 : X.open_cover) [fintype 𝒰.J]
  [H : ∀ i, compact_space (𝒰.obj i).carrier] : compact_space X.carrier :=
begin
  rw [← is_compact_univ_iff, ← 𝒰.Union_range],
  apply compact_Union,
  intro i,
  rw is_compact_iff_compact_space,
  exact @@homeomorph.compact_space _ _ (H i)
    (Top.homeo_of_iso (as_iso (is_open_immersion.iso_of_range_eq (𝒰.map i)
    (X.of_restrict (opens.open_embedding ⟨_, (𝒰.is_open i).base_open.open_range⟩))
    subtype.range_coe.symm).hom.1.base))
end

lemma quasi_compact_affine_property_stable_under_base_change :
  affine_target_morphism_property.stable_under_base_change quasi_compact.affine_property :=
begin
  introv X H,
  delta quasi_compact.affine_property at H ⊢,
  resetI,
  apply_with Scheme.open_cover.compact_space { instances := ff },
  swap 3,
  { exact Scheme.pullback.open_cover_of_right Y.affine_cover.finite_subcover f g },
  { change fintype Y.affine_cover.finite_subcover.J,
    apply_instance },
  { intro i,
    haveI : is_affine (Y.affine_cover.finite_subcover.obj i),
    { dsimp, apply_instance },
    change compact_space (pullback f _).carrier,
    apply_instance }
end

lemma quasi_compact.affine_open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [quasi_compact f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)],
      ∀ (i : 𝒰.J), compact_space (pullback f (𝒰.map i)).carrier,
    ∀ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)] (i : 𝒰.J),
      compact_space (pullback f (𝒰.map i)).carrier,
    ∀ {U : Scheme} (g : U ⟶ Y) [is_affine U] [is_open_immersion g],
      compact_space (pullback f g).carrier] :=
quasi_compact_eq_affine_property.symm ▸
  quasi_compact_affine_property_is_local.affine_open_cover_tfae f

lemma quasi_compact.open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [quasi_compact f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
      quasi_compact (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
      quasi_compact (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (U : opens Y.carrier), quasi_compact (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
      quasi_compact (pullback.snd : pullback f g ⟶ _)] :=
quasi_compact_eq_affine_property.symm ▸
  quasi_compact_affine_property_is_local.open_cover_tfae f

lemma quasi_compact_over_affine_iff {X Y : Scheme} (f : X ⟶ Y) [is_affine Y] :
  quasi_compact f ↔ compact_space X.carrier :=
quasi_compact_eq_affine_property.symm ▸
  quasi_compact_affine_property_is_local.affine_target_iff f

lemma compact_space_iff_quasi_compact (X : Scheme) :
  compact_space X.carrier ↔ quasi_compact (terminal.from X) :=
(quasi_compact_over_affine_iff _).symm

lemma quasi_compact.affine_open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
  quasi_compact f ↔ ∀ i, compact_space (pullback f (𝒰.map i)).carrier :=
quasi_compact_eq_affine_property.symm ▸
  quasi_compact_affine_property_is_local.affine_open_cover_iff f 𝒰

lemma quasi_compact.open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
  quasi_compact f ↔ ∀ i, quasi_compact (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
quasi_compact_eq_affine_property.symm ▸
  quasi_compact_affine_property_is_local.open_cover_iff f 𝒰

lemma quasi_compact_stable_under_base_change :
  stable_under_base_change @quasi_compact :=
quasi_compact_eq_affine_property.symm ▸
  quasi_compact_affine_property_is_local.stable_under_base_change
    quasi_compact_affine_property_stable_under_base_change

lemma quasi_compact_respects_iso : respects_iso @quasi_compact :=
quasi_compact_eq_affine_property.symm ▸
  target_affine_locally_respects_iso quasi_compact_affine_property_is_local.1

lemma quasi_compact_stable_under_composition :
  stable_under_composition @quasi_compact :=
λ _ _ _ _ _ _ _, by exactI infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [quasi_compact g] :
  quasi_compact (pullback.fst : pullback f g ⟶ X) :=
quasi_compact_stable_under_base_change f g infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [quasi_compact f] :
  quasi_compact (pullback.snd : pullback f g ⟶ Y) :=
quasi_compact_stable_under_base_change.symmetry quasi_compact_respects_iso f g infer_instance


end algebraic_geometry

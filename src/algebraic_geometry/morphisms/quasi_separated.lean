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

def quasi_separated.affine_property : affine_target_morphism_property :=
λ X Y f hf, is_quasi_separated X

@[simp] lemma quasi_separated_affine_property_to_property {X Y : Scheme} (f : X ⟶ Y) :
  affine_target_morphism_property.to_property quasi_separated.affine_property f ↔
    is_affine Y ∧ is_quasi_separated X :=
by { delta affine_target_morphism_property.to_property quasi_separated.affine_property, simp }

@[priority 900]
instance quasi_separated_of_mono {X Y : Scheme} (f : X ⟶ Y) [mono f] : quasi_separated f :=
⟨infer_instance⟩
.
lemma quasi_separated_eq_diagonal_is_quasi_compact :
  @quasi_separated = diagonal_is @quasi_compact :=
by { ext, exact quasi_separated_iff _ }

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

/-- Given an open cover `{ Yᵢ }` of `Y`, then `X ×[Z] Y` is covered by `X ×[Z] Yᵢ`. -/
@[simps J obj map]
def Scheme.pullback.open_cover_of_left_right {X Y Z : Scheme} (𝒰X : X.open_cover) (𝒰Y : Y.open_cover)
  (f : X ⟶ Z) (g : Y ⟶ Z) : (pullback f g).open_cover :=
begin
  fapply ((Scheme.pullback.open_cover_of_left 𝒰X f g).bind
    (λ x, Scheme.pullback.open_cover_of_right 𝒰Y (𝒰X.map x ≫ f) g)).copy
    (𝒰X.J × 𝒰Y.J)
    (λ ij, pullback (𝒰X.map ij.1 ≫ f) (𝒰Y.map ij.2 ≫ g))
    (λ ij, pullback.map _ _ _ _ (𝒰X.map ij.1) (𝒰Y.map ij.2) (𝟙 _)
      (category.comp_id _) (category.comp_id _))
    (equiv.sigma_equiv_prod _ _).symm
    (λ _, iso.refl _),
  rintro ⟨i, j⟩,
  apply pullback.hom_ext; simpa,
end

def de {X Y U V₁ V₂ : Scheme} (f : X ⟶ Y) (i : U ⟶ Y) (i₁ : V₁ ⟶ pullback f i)
  (i₂ : V₂ ⟶ pullback f i) [mono i] :
  pullback i₁ i₂ ≅ pullback (pullback.diagonal f)
    (pullback.map (i₁ ≫ pullback.snd) (i₂ ≫ pullback.snd) f f (i₁ ≫ pullback.fst)
      (i₂ ≫ pullback.fst) i (by sorry; simp [pullback.condition]) (by sorry; simp [pullback.condition])) :=
{ hom := pullback.lift (pullback.fst ≫ i₁ ≫ pullback.fst) (pullback.map _ _ _ _ (𝟙 _) (𝟙 _)
      pullback.snd (category.id_comp _).symm (category.id_comp _).symm)
    begin
      sorry; apply pullback.hom_ext; simp only [pullback.diagonal_snd, category.comp_id, category.assoc,
        pullback.lift_snd, pullback.lift_snd_assoc, pullback.diagonal_fst, pullback.lift_fst,
        pullback.lift_fst_assoc, pullback.condition_assoc],
    end,
  inv := pullback.lift (pullback.snd ≫ pullback.fst) (pullback.snd ≫ pullback.snd)
    begin
      rw ← cancel_mono pullback.fst,
      transitivity pullback.fst ≫ 𝟙 _,
      rw [← pullback.diagonal_fst f, pullback.condition_assoc, pullback.lift_fst],
    end,
  hom_inv_id' := _,
  inv_hom_id' := _ }

lemma quasi_separated_of_affine_open_cover {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (𝒰' : Π i, Scheme.open_cover.{u} (pullback f (𝒰.map i)))
    [∀ i j, is_affine ((𝒰' i).obj j)]
    [∀ i j j', compact_space (pullback ((𝒰' i).map j) ((𝒰' i).map j')).carrier] :
    quasi_separated f :=
begin
  rw quasi_separated_eq_diagonal_is_quasi_compact,
  refine (quasi_compact.affine_open_cover_iff _ _).mpr _,
  { exact ((Scheme.pullback.open_cover_of_base 𝒰 f f).bind (λ i,
      Scheme.pullback.open_cover_of_left_right.{u u} (𝒰' i) (𝒰' i) pullback.snd pullback.snd)) },
  { intro i,
    dsimp at *,
    apply_instance },
  { rintro ⟨i, j, k⟩,
    dsimp,
    have := pullback.pullback_diagonal_map_iso ((𝒰' i).map j) ((𝒰' i).map k) pullback.snd,
  }

end


lemma quasi_separated_iff_affine_property :
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
  { split,
    all_goals
    { rintros X Y Z _ _ H,
      rw quasi_compact_affine_property_to_property at H ⊢,
      cases H with h₁ h₂,
      resetI,
      split },
    exacts [h₁, @@homeomorph.compact_space _ _ h₂ (Top.homeo_of_iso (as_iso e.inv.1.base)),
      is_affine_of_iso e.inv, h₂] },
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

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [quasi_compact g] :
  quasi_compact (pullback.fst : pullback f g ⟶ X) :=
quasi_compact_stable_under_base_change f g infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [quasi_compact f] :
  quasi_compact (pullback.snd : pullback f g ⟶ Y) :=
quasi_compact_stable_under_base_change.symmetry quasi_compact_respects_iso f g infer_instance


end algebraic_geometry

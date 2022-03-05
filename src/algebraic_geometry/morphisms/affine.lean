/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.morphisms.open_immersion
import algebraic_geometry.morphisms.quasi_separated

/-!
# Affine morphisms

A morphism of schemes is affine if the preimages of affine open sets are affine.

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
class affine (f : X ⟶ Y) : Prop :=
(is_affine_preimage : ∀ U : opens Y.carrier,
  is_affine_open U → is_affine_open ((opens.map f.1.base).obj U))

def affine.affine_property : affine_target_morphism_property :=
λ X Y f hf, is_affine X

@[simp] lemma affine_affine_property_to_property {X Y : Scheme} (f : X ⟶ Y) :
  affine_target_morphism_property.to_property affine.affine_property f ↔
    is_affine Y ∧ is_affine X :=
by { delta affine_target_morphism_property.to_property affine.affine_property, simp }

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

lemma prime_spectrum.Union_basic_open_eq_top_iff {R : Type*} [comm_ring R] {ι : Type*}
  (f : ι → R) : (⨆ i : ι, prime_spectrum.basic_open (f i)) = ⊤ ↔ ideal.span (set.range f) = ⊤ :=
begin
  erw opens.supr_mk (λ i : ι, (prime_spectrum.basic_open (f i)).1),
  rw [← opens.ext_iff, subtype.coe_mk],
  simp_rw [subtype.val_eq_coe, prime_spectrum.basic_open_eq_zero_locus_compl],
  rw [← set.compl_Inter, opens.coe_top],
  erw compl_eq_top,
  rw [← prime_spectrum.zero_locus_Union, ← prime_spectrum.zero_locus_span],
  erw prime_spectrum.zero_locus_empty_iff_eq_top,
  simp,
end

lemma CommRing.is_iso_iff_bijective {R S : CommRing} (f : R ⟶ S) :
  is_iso f ↔ function.bijective f :=
begin
  rw ← is_iso_iff_bijective,
  change is_iso f ↔ is_iso ((forget CommRing).map f),
  refine ⟨λ H, by exactI infer_instance, λ H, by exactI is_iso_of_reflects_iso f (forget CommRing)⟩,
end

lemma bijective_of_is_localization {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
  [algebra R S] [algebra R T] (M : submonoid R) [is_localization M S] [is_localization M T]
  (f : S →+* T) (hf : f.comp (algebra_map R S) = algebra_map R T) : function.bijective f :=
begin
  have : f = is_localization.alg_equiv M S T,
  { apply is_localization.ring_hom_ext M, { rw hf, simp }, { apply_instance } },
  rw this,
  exact (is_localization.alg_equiv M S T).to_equiv.bijective,
end

lemma Γ_Spec.adjunction.unit_app_map_basic_open {X : Scheme} (r : X.presheaf.obj (op ⊤)) :
  (opens.map (Γ_Spec.adjunction.unit.app X).1.base).obj (prime_spectrum.basic_open r) =
    X.basic_open r :=
begin
  rw ← basic_open_eq_of_affine,
  erw Scheme.preimage_basic_open,
  change X.basic_open _ = _,
  congr,
  rw [Γ_Spec.adjunction_unit_app_app_top, ← comp_apply],
  simp [-comp_apply]
end

lemma preimage_adjunction_unit_basic_open (X : Scheme) (r : X.presheaf.obj (op ⊤)) :
  (opens.map (Γ_Spec.adjunction.unit.app X).1.base).obj (prime_spectrum.basic_open r) =
    X.basic_open r :=
begin
  rw ← basic_open_eq_of_affine,
  erw Scheme.preimage_basic_open,
  congr',
  rw [Γ_Spec.adjunction_unit_app_app_top, ← comp_apply],
  simp [-comp_apply]
end

lemma supr_basic_open_eq_top_of_span_eq_top (X : Scheme) (s : set (X.presheaf.obj $ op ⊤))
  (h : ideal.span s = ⊤) : (⨆ i : s, X.basic_open i.1) = ⊤ :=
begin
  have := prime_spectrum.Union_basic_open_eq_top_iff (coe : s → X.presheaf.obj (op ⊤)),
  rw subtype.range_coe at this,
  rw ← this at h,
  apply_fun (opens.map (Γ_Spec.adjunction.unit.app X).1.base).obj at h,
  rw opens.map_supr at h,
  convert h,
  ext1 i,
  exact (preimage_adjunction_unit_basic_open X _).symm
end


-- @[simp] lemma opens.coe_supr {α : Type*} [topological_space α] {ι} (s : ι → opens α) :
--   ((⨆ i, s i : opens α) : set α) = ⋃ i, s i :=
-- by { rw opens.supr_def, refl }

lemma is_affine_of_span_top_of_is_affine_open (X : Scheme) (s : set (X.presheaf.obj $ op ⊤))
  (h₁ : ideal.span s = ⊤) (h₂ : ∀ r : s, is_affine_open (X.basic_open r.1)) : is_affine X :=
begin
  haveI : quasi_separated_space X.carrier,
  { obtain ⟨s', hs', e⟩ := (ideal.span_eq_top_iff_finite _).mp h₁,
    rw quasi_separated_space_iff_affine,
    intros U V,
    rw [← set.inter_univ (U ∩ V : set X.carrier), ← (show _ = set.univ, from
      (congr_arg subtype.val $ supr_basic_open_eq_top_of_span_eq_top _ _ e : _)), opens.supr_def,
      subtype.val_eq_coe, subtype.coe_mk, set.inter_Union],
    apply compact_Union,
    intro i,
    convert_to is_compact ((U.1 ⊓ (X.basic_open i.val)) ⊓ (V.1 ⊓ (X.basic_open i.val))).1,
    { conv_rhs { rw [inf_assoc, ← @inf_assoc _ _ (X.basic_open i.1),
        @inf_comm _ _ (X.basic_open i.1), inf_assoc, inf_idem, ← inf_assoc] },
      refl },
    have : ∀ (S : opens X.carrier), S ⊓ X.basic_open i.1 = X.basic_open
      (X.presheaf.map (hom_of_le le_top : S ⟶ _).op i.1) := λ S, (X.basic_open_res _ _).symm,
    apply (h₂ ⟨i.1, hs' i.2⟩).is_quasi_separated,
    { exact @inf_le_right _ _ U.1 _ },
    { exact (U.val ⊓ X.basic_open i.val).2 },
    { rw this, exact (U.prop.basic_open_is_affine _).is_compact },
    { exact @inf_le_right _ _ V.1 _ },
    { exact (V.val ⊓ X.basic_open i.val).2 },
    { rw this, exact (V.prop.basic_open_is_affine _).is_compact } },
  have hX : compact_space X.carrier,
  { obtain ⟨s', hs', e⟩ := (ideal.span_eq_top_iff_finite _).mp h₁,
    rw [← is_compact_univ_iff, ← (show _ = set.univ, from
      (congr_arg subtype.val $ supr_basic_open_eq_top_of_span_eq_top _ _ e : _)), opens.supr_def],
    apply compact_Union,
    intro i, exact (h₂ ⟨i.1, hs' i.2⟩).is_compact },
  constructor,
  rw (is_iso.open_cover_tfae (Γ_Spec.adjunction.unit.app X)).out 0 5,
  refine ⟨s, λ i, prime_spectrum.basic_open i.1, _, _⟩,
  { rw prime_spectrum.Union_basic_open_eq_top_iff, convert h₁, simp },
  { intro r,
    apply_with is_iso_of_is_affine_is_iso { instances := ff },
    { change is_affine_open _,
      rw preimage_adjunction_unit_basic_open,
      exact h₂ r },
    { change is_affine_open _,
      rw ← basic_open_eq_of_affine,
      apply is_affine_open.basic_open_is_affine,
      apply_with top_is_affine_open { instances := ff },
      exact algebraic_geometry.Spec_is_affine _ },
    { suffices : ∀ (U = prime_spectrum.basic_open r.val),
        is_iso ((Γ_Spec.adjunction.unit.app X).val.c.app (op $ U)),
      { rw morphism_restrict_c_app,
        apply_with is_iso.comp_is_iso { instances := ff },
        { apply this, rw opens.open_embedding_obj_top },
        { apply_instance } },
      rintros _ rfl,
      rw CommRing.is_iso_iff_bijective,
      fapply bijective_of_is_localization (submonoid.powers r.1),
      rotate,
      { apply structure_sheaf.open_algebra },
      { apply ring_hom.to_algebra,
        exact X.presheaf.map (hom_of_le le_top :
          (opens.map (Γ_Spec.adjunction.unit.app X).val.base).obj _ ⟶ _).op },
      { apply structure_sheaf.is_localization.to_basic_open },
      { dsimp,
        rw ← is_compact_univ_iff at hX,
        convert is_localization_basic_open_of_is_compact
          (show is_compact (⊤ : opens _).1, from hX) r.1;
          apply Γ_Spec.adjunction.unit_app_map_basic_open },
      { rw [ring_hom.algebra_map_to_algebra, ring_hom.algebra_map_to_algebra,
          Γ_Spec.adjunction_unit_app],
        exact X.1.to_Γ_Spec_SheafedSpace_app_spec r.1 } } }
end

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
    apply_fun ideal.map (f.1.c.app (op ⊤)) at hS,
    rw [ideal.map_span, ideal.map_top] at hS,
    delta affine.affine_property,
    unfreezingI { change ∀ (i : S), is_affine_open _ at hS',
      simp_rw Scheme.preimage_basic_open at hS' },
    apply is_affine_of_span_top_of_is_affine_open X _ hS,
    rintro ⟨_, r, hr, rfl⟩,
    exact hS' ⟨r, hr⟩ }
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
      is_affine (pullback f g),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤) (hU' : ∀ i, is_affine_open (U i)),
      ∀ i, is_affine_open ((opens.map f.1.base).obj $ U i)] :=
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
      affine (pullback.snd : pullback f g ⟶ _),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤),
      ∀ i, affine (f ∣_ (U i))] :=
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

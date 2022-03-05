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

/-- If `α` has a basis consisting of compact opens, then an open set in `α` is compact open iff
  it is a finite union of some elements in the basis -/
lemma is_compact_open_iff_eq_finset_Union_of_is_topological_basis {α : Type*} [topological_space α]
  {ι : Type*} (b : ι → set α) (hb : is_topological_basis (set.range b))
  (hb' : ∀ i, is_compact (b i)) (U : set α) :
  is_compact U ∧ is_open U ↔ ∃ (s : finset ι), U = ⋃ i : s, b i :=
begin
  classical,
  split,
  { rintro ⟨h₁, h₂⟩,
    obtain ⟨β, f, e, hf⟩ := hb.open_eq_Union h₂,
    choose f' hf' using hf,
    have : b ∘ f' = f := funext hf', subst this,
    obtain ⟨t, ht⟩ := h₁.elim_finite_subcover (b ∘ f')
      (λ i, hb.is_open (set.mem_range_self _)) (by rw e),
    use t.image f',
    apply le_antisymm,
    { refine set.subset.trans ht _,
      simp only [set.Union_subset_iff, coe_coe],
      intros i hi,
      exact set.subset_Union (λ i : t.image f', b i) ⟨_, finset.mem_image_of_mem _ hi⟩ },
    { apply set.Union_subset,
      rintro ⟨i, hi⟩,
      obtain ⟨j, hj, rfl⟩ := finset.mem_image.mp hi,
      rw e,
      exact set.subset_Union (b ∘ f') j } },
  { rintro ⟨s, rfl⟩,
    split,
    { convert @finset.compact_bUnion _ _ _ s.attach _ _,
      { ext y, simp },
      { exact λ i _, hb' i } },
    { apply is_open_Union, rintro i, exact hb.is_open (set.mem_range_self _) } },
end


/-- If `α` has a basis consisting of compact opens, then an open set in `α` is compact open iff
  it is a finite union of some elements in the basis -/
lemma is_compact_open_iff_eq_finset_Union_of_opens_is_basis {α : Type*} [topological_space α]
  {ι : Type*} (b : ι → opens α) (hb : opens.is_basis (set.range b))
  (hb' : ∀ i, is_compact (b i : set α)) (U : set α) :
  is_compact U ∧ is_open U ↔ ∃ (s : finset ι), U = ⋃ i : s, b i :=
begin
  apply is_compact_open_iff_eq_finset_Union_of_is_topological_basis
    (λ i : ι, (b i).1),
  { convert hb, ext, simp },
  { exact hb' }
end

lemma is_compact_open_iff_eq_finset_affine_union {X : Scheme} (U : set X.carrier) :
  is_compact U ∧ is_open U ↔ ∃ (s : finset X.affine_opens), U = ⋃ (i : s), i :=
begin
  apply is_compact_open_iff_eq_finset_Union_of_opens_is_basis
    (coe : X.affine_opens → opens X.carrier),
  { rw subtype.range_coe, exact is_basis_affine_open X },
  { intro i, exact i.2.is_compact }
end

lemma is_compact_open_iff_eq_basic_open_union {X : Scheme} [is_affine X] (U : set X.carrier) :
  is_compact U ∧ is_open U ↔
    ∃ (s : finset (X.presheaf.obj (op ⊤))), U = ⋃ (i : s), X.basic_open i.1 :=
begin
  apply is_compact_open_iff_eq_finset_Union_of_opens_is_basis,
  { exact is_basis_basic_open X },
  { intro i, exact ((top_is_affine_open _).basic_open_is_affine _).is_compact }
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
      compact_space (pullback f g).carrier,
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤) (hU' : ∀ i, is_affine_open (U i)),
      ∀ i, compact_space (f.1.base ⁻¹' (U i).1)] :=
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
      quasi_compact (pullback.snd : pullback f g ⟶ _),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤), ∀ i, quasi_compact (f ∣_ (U i))] :=
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

lemma exists_power_mul_eq_zero_of_res_basic_open_eq_zero_of_is_affine_open (X : Scheme)
  {U : opens X.carrier} (hU : is_affine_open U) (x f : X.presheaf.obj (op U))
  (H : X.presheaf.map (hom_of_le $ X.basic_open_subset f : X.basic_open f ⟶ U).op x = 0) :
  ∃ n : ℕ, f ^ n * x = 0 :=
begin
  rw ← map_zero (X.presheaf.map (hom_of_le $ X.basic_open_subset f : X.basic_open f ⟶ U).op) at H,
  have := (is_localization_basic_open hU f).3,
  obtain ⟨⟨_, n, rfl⟩, e⟩ := this.mp H,
  exact ⟨n, by simpa [mul_comm x] using e⟩,
end

lemma exists_power_mul_eq_zero_of_res_basic_open_eq_zero_of_is_compact (X : Scheme)
  {U : opens X.carrier} (hU : is_compact U.1) (x f : X.presheaf.obj (op U))
  (H : X.presheaf.map (hom_of_le $ X.basic_open_subset f : X.basic_open f ⟶ U).op x = 0) :
  ∃ n : ℕ, f ^ n * x = 0 :=
begin
  obtain ⟨s, hs⟩ := (is_compact_open_iff_eq_finset_affine_union U.1).mp ⟨hU, U.2⟩,
  replace hs : U = supr (λ i : s, (i : opens X.carrier)),
  { ext1, simpa using hs, },
  have h₁ : ∀ i : s, i.1.1 ≤ U,
  { intro i, change (i : opens X.carrier) ≤ U, rw hs, exact le_supr _ _ },
  have H' := λ (i : s), exists_power_mul_eq_zero_of_res_basic_open_eq_zero_of_is_affine_open X i.1.2
    (X.presheaf.map (hom_of_le (h₁ i)).op x) (X.presheaf.map (hom_of_le (h₁ i)).op f) _,
  swap,
  { convert congr_arg (X.presheaf.map (hom_of_le _).op) H,
    { simp only [← comp_apply, ← functor.map_comp], congr },
    { rw map_zero },
    { rw X.basic_open_res, exact set.inter_subset_right _ _ } },
  choose n hn using H',
  use s.attach.sup n,
  suffices : ∀ (i : s), X.presheaf.map (hom_of_le (h₁ i)).op (f ^ (s.attach.sup n) * x) = 0,
  { subst hs,
    apply X.sheaf.eq_of_locally_eq (λ (i : s), (i : opens X.carrier)),
    intro i,
    rw map_zero,
    apply this },
  intro i,
  replace hn := congr_arg
    (λ x, X.presheaf.map (hom_of_le (h₁ i)).op (f ^ (s.attach.sup n - n i)) * x) (hn i),
  dsimp at hn,
  simp only [← map_mul, ← map_pow] at hn,
  rwa [mul_zero, ← mul_assoc, ← pow_add, tsub_add_cancel_of_le] at hn,
  apply finset.le_sup (s.mem_attach i)
end

lemma supr_insert {α β : Type*} (x : α) (s : set α) (f : α → β) [complete_lattice β] :
  (⨆ a : insert x s, f a) = (⨆ a : s, f a) ⊔ f x :=
begin
  apply le_antisymm,
  { suffices : ∀ (a : s), f a ≤ (⨆ a : s, f a) ⊔ f x,
    { simpa using this },
    intros a,
    exact le_trans (le_supr (λ x : s, f x) a : _) le_sup_left },
  { simp only [supr_le_iff, set_coe.forall, sup_le_iff], split,
    { intros a ha, exact le_supr (λ a : insert x s, f a) ⟨_, set.mem_insert_of_mem _ ha⟩ },
    { exact le_supr (λ a : insert x s, f a) ⟨_, set.mem_insert _ _⟩ } }
end

lemma supr_finset_insert {α β : Type*} (x : α) (s : finset α) (f : α → β) [complete_lattice β]
  [decidable_eq α] : (⨆ a : insert x s, f a) = (⨆ a : s, f a) ⊔ f x :=
begin
  convert supr_insert x s f using 1,
  rw ← finset.coe_insert,
  refl
end

lemma compact_open_induction_on (P : opens X.carrier → Prop)
  (h₁ : P ⊥)
  (h₂ : ∀ (S : opens X.carrier) (hS : is_compact S.1) (U : X.affine_opens), P S → P (S ⊔ U)) :
  ∀ (S : opens X.carrier) (hS : is_compact S.1), P S :=
begin
  classical,
  intros S hS,
  obtain ⟨s, hs⟩ := (is_compact_open_iff_eq_finset_affine_union S.1).mp ⟨hS, S.2⟩,
  replace hs : S = supr (λ i : s, (i : opens X.carrier)) := by { ext1, simpa using hs },
  subst hs,
  induction s using finset.induction with x s h₃ h₄,
  { convert h₁, rw supr_eq_bot, rintro ⟨_, h⟩, exact h.elim },
  { have : is_compact (⨆ i : s, (i : opens X.carrier)).1,
    { refine ((is_compact_open_iff_eq_finset_affine_union _).mpr _).1, use s, simp },
    convert h₂ _ this x (h₄ this), simp only [coe_coe], rw supr_finset_insert, refl }
end

end algebraic_geometry

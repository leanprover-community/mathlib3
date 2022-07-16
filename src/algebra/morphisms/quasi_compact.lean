/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.AffineScheme

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

instance Scheme.quasi_compact_of_affine (X : Scheme) [is_affine X] : compact_space X.carrier :=
⟨(top_is_affine_open X).is_compact⟩

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
  is_compact U ∧ is_open U ↔ ∃ (s : set X.affine_opens), s.finite ∧ U = ⋃ i ∈ s, i :=
begin
  apply is_compact_open_iff_eq_finite_Union_of_is_topological_basis
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
    convert h₂ _ this x (h₄ this),
    simp only [coe_coe],
    rw [supr_subtype, sup_comm],
    conv_rhs { rw supr_subtype },
    exact finset.supr_insert _ _ _ }
end

end algebraic_geometry

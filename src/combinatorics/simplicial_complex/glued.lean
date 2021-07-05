/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import logic.relation
import combinatorics.simplicial_complex.closure

namespace affine
open set relation
open_locale classical
variables {a b m n : ℕ} {E : Type*} [normed_group E] [normed_space ℝ E]
  {S S' S₁ S₂ : simplicial_complex E} {X Y Z : finset E}

--to add to mathlib?
lemma curry_eq_of_symmetric_transitive {α : Type*} {R : α → α → Prop} {a b : α}
  (hRsymm : symmetric R) (hRtrans : transitive R) (hab : R a b) :
  R a = R b :=
funext $ λ c, propext ⟨hRtrans (hRsymm hab), hRtrans hab⟩

def adjacent (X Y : finset E) :
  Prop :=
X.card = (X ∩ Y).card + 1 ∧ Y.card = (X ∩ Y).card + 1

lemma adjacent.symmetric :
  symmetric (adjacent : finset E → finset E → Prop) :=
begin
  rintro X Y ⟨hX, hY⟩,
  rw finset.inter_comm at hX hY,
  exact ⟨hY, hX⟩,
end

lemma adjacent.symm :
  adjacent X Y ↔ adjacent Y X :=
begin
  split;
  apply adjacent.symmetric,
end

lemma card_eq_of_adjacent (hX : X ∈ S.faces) (hY : adjacent X Y) :
  Y.card = X.card :=
eq.trans hY.2 hY.1.symm

def simplicial_complex.glued (S : simplicial_complex E) :
  finset E → finset E → Prop :=
refl_trans_gen (λ X Y, adjacent X Y ∧ X ∈ S.facets ∧ Y ∈ S.facets)

lemma glued.refl :
  S.glued X X :=
refl_trans_gen.refl

lemma glued.symmetric :
  symmetric S.glued :=
begin
  apply refl_trans_gen.symmetric,
  rintro X Y ⟨hXY, hX, hY⟩,
  rw adjacent.symm at hXY,
  exact ⟨hXY, hY, hX⟩,
end

lemma glued.symm :
  S.glued X Y ↔ S.glued Y X :=
begin
  split;
  apply glued.symmetric,
end

lemma glued.transitive :
  transitive S.glued :=
transitive_refl_trans_gen

lemma glued.trans (hXY : S.glued X Y) (hYZ : S.glued Y Z) :
  S.glued X Z :=
transitive_refl_trans_gen hXY hYZ

instance : is_equiv (finset E) S.glued :=
{ refl := reflexive_refl_trans_gen,
  trans := transitive_refl_trans_gen,
  symm := glued.symmetric }

lemma face_of_glued (hX : X ∈ S.faces) (hXY : S.glued X Y) :
  Y ∈ S.faces :=
begin
  cases refl_trans_gen.cases_tail hXY,
  { rw h,
    exact hX },
  { obtain ⟨W, _, _, _, hY⟩ := h,
    exact hY.1 }
end

lemma facet_of_glued (hX : X ∈ S.facets) (hXY : S.glued X Y) :
  Y ∈ S.facets :=
begin
  cases refl_trans_gen.cases_tail hXY,
  { rw h,
    exact hX },
  { obtain ⟨W, _, _, _, hY⟩ := h,
    exact hY }
end

lemma card_eq_of_glued (hY : S.glued X Y) :
  Y.card = X.card :=
refl_trans_gen.trans_induction_on hY
  (λ _, rfl)
  (λ X Y ⟨hXY, hX, _⟩, card_eq_of_adjacent hX.1 hXY)
  (λ X Y Z _ _ hYX hZY, eq.trans hZY hYX)

lemma setof_glued_subset (hX : X ∈ S.faces) :
  set_of (S.glued X) ⊆ S.faces :=
λ Y hY, face_of_glued hX hY

lemma setof_glued_attop ⦃Y Z : finset E⦄ (hY : Y ∈ set_of (S.glued X))
  (hZ : Z ∈ set_of (S.glued X)) (hYZ : Y ⊆ Z) :
  Y = Z :=
begin
  apply finset.eq_of_subset_of_card_le hYZ (le_of_eq _),
  rw [card_eq_of_glued hY, card_eq_of_glued hZ],
end

def simplicial_complex.pure_decomp (S : simplicial_complex E) :
  set (simplicial_complex E) :=
(λ X, S.closure (set_of (S.glued X))) '' S.facets

lemma pure_decomp_faces_subset (hS : S' ∈ S.pure_decomp) :
  S'.faces ⊆ S.faces :=
begin
  obtain ⟨_, _, rfl⟩ := hS,
  exact λ X hX, closure_subset hX,
end

lemma card_le_of_mem_element_pure_decomp (hY : Y ∈ (S.closure (set_of (S.glued X))).faces) :
  Y.card ≤ X.card :=
begin
  obtain ⟨hY, Z, hZ, hYZ⟩ := hY,
  rw ←card_eq_of_glued hZ,
  exact finset.card_le_of_subset hYZ,
end

lemma facet_pure_decomp_self (hX : X ∈ S.faces) :
  X ∈ (S.closure (set_of (S.glued X))).facets :=
⟨⟨hX, ⟨X, glued.refl, finset.subset.refl _⟩⟩, (λ Y hY hXY, finset.eq_of_subset_of_card_le hXY
  (card_le_of_mem_element_pure_decomp hY))⟩

lemma mem_pure_decomp_facets_iff (hX : X ∈ S.faces) :
  Y ∈ (S.closure (set_of (S.glued X))).facets ↔ S.glued X Y :=
by rw [closure_facets_eq (setof_glued_subset hX) setof_glued_attop, mem_set_of_eq]

lemma pure_decomp_facet_iff (hS : S' ∈ S.pure_decomp) :
  X ∈ S'.facets ↔ X ∈ S.faces ∧ S' = S.closure (set_of (S.glued X)) :=
begin
  split,
  { rintro hX,
    obtain ⟨Y, hY, rfl⟩ := hS,
    use closure_subset (facets_subset hX),
    rw mem_pure_decomp_facets_iff hY.1 at hX,
    rw ←curry_eq_of_symmetric_transitive glued.symmetric glued.transitive hX },
  { rintro ⟨hX, rfl⟩,
    exact ⟨faces_subset_closure ⟨hX, glued.refl⟩, (λ Y hY hXY,
      finset.eq_of_subset_of_card_le hXY (card_le_of_mem_element_pure_decomp hY))⟩ }
end

lemma pure_decomp_cover_facets (hX : X ∈ S.facets) :
  ∃ {S' : simplicial_complex E}, S' ∈ S.pure_decomp ∧ X ∈ S'.facets :=
begin
  use S.closure (set_of (S.glued X)),
  split,
  { use [X, hX] },
  use [faces_subset_closure ⟨hX.1, glued.refl⟩],
  rintro Y hY hXY,
  exact hX.2 (closure_subset hY) hXY,
end

lemma pure_decomp_disjoint_facets (hS₁ : S₁ ∈ S.pure_decomp)
  (hS₂ : S₂ ∈ S.pure_decomp) (hX : X ∈ S.facets) (hX₁ : X ∈ S₁.facets) (hX₂ : X ∈ S₂.facets) :
  S₁ = S₂ :=
begin
  obtain ⟨Y₁, hY₁, rfl⟩ := hS₁,
  obtain ⟨Y₂, hY₂, rfl⟩ := hS₂,
  simp at ⊢ hX₁ hX₂,
  rw mem_pure_decomp_facets_iff hY₁.1 at hX₁,
  rw mem_pure_decomp_facets_iff hY₂.1 at hX₂,
  rw ←curry_eq_of_symmetric_transitive glued.symmetric glued.transitive
    (glued.trans hX₁ (glued.symmetric hX₂)),
end

lemma pure_decomp_cover [finite_dimensional ℝ E] (hX : X ∈ S.faces) :
  ∃ {S' : simplicial_complex E}, S' ∈ S.pure_decomp ∧ X ∈ S'.faces :=
begin
  obtain ⟨Y, hY, hXY⟩ := subfacet hX,
  obtain ⟨S', hS', hYS'⟩ := pure_decomp_cover_facets hY,
  exact ⟨S', hS', S'.down_closed hYS'.1 hXY⟩,
end

lemma pure_decomp_facets_subset (hS : S' ∈ S.pure_decomp) (hX : X ∈ S'.facets) :
  X ∈ S.facets :=
begin
  obtain ⟨Y, hY, rfl⟩ := hS,
  exact facet_of_glued hY ((mem_pure_decomp_facets_iff hY.1).1 hX),
end

--lemma pure_decomp_facets_partition :

lemma pure_of_mem_pure_decomp (hS : S' ∈ S.pure_decomp) :
  S'.pure :=
begin
  obtain ⟨Y, hY, rfl⟩ := hS,
  exact ⟨Y.card, (λ X hX, card_eq_of_glued ((mem_pure_decomp_facets_iff hY.1).1 hX))⟩,
end

lemma pure_of_pure_decomp_singleton (hS : S.pure_decomp = {S}) :
  S.pure :=
begin
  refine pure_of_mem_pure_decomp (_ : S ∈ S.pure_decomp),
  rw hS,
  exact mem_singleton _,
end

lemma pure_decomp_space_subset_space :
  (⋃ (S' ∈ S.pure_decomp), (S' : simplicial_complex E).space) ⊆ S.space :=
begin
  rintro x hx,
  rw mem_bUnion_iff at hx,
  obtain ⟨S', hS', hx⟩ := hx,
  obtain ⟨X, hX, hxX⟩ := mem_space_iff.1 hx,
  exact mem_space_iff.2 ⟨X, pure_decomp_faces_subset hS' hX, hxX⟩,
end

lemma pure_decomp_space_eq_space [finite_dimensional ℝ E] :
  (⋃ (S' ∈ S.pure_decomp), (S' : simplicial_complex E).space) = S.space :=
begin
  apply subset.antisymm pure_decomp_space_subset_space,
  rintro x hx,
  obtain ⟨X, hX, hxX⟩ := mem_space_iff.1 hx,
  obtain ⟨S', hS', hx⟩ := pure_decomp_cover hX,
  exact mem_bUnion hS' (mem_space_iff.2 ⟨X, hx, hxX⟩),
end

end affine

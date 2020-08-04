/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.content
import measure_theory.group
/-!
# Haar measure

In this file we prove the existence of Haar measure for a locally compact Hausdorff topological
group.

## Main Declarations

* `haar_measure`: the Haar measure on a locally compact Hausdorff group. This is a left invariant
  regular measure. It takes as argument a compact set of the group (with non-empty interior),
  and is normalized so that the measure of the given set is 1.
* `haar_measure_self`: the Haar measure is normalized.
* `is_left_invariant_haar_measure`: the Haar measure is left invariant
* `regular_haar_measure`: the Haar measure is a regular measure.

## References
* Paul Halmos (1950), Measure Theory, §53
* Jonathan Gleason, Existence and Uniqueness of Haar Measure
  - Note: step 9, page 8 contains a mistake: the last defined `μ` does not extend the `μ` on compact
    sets, see Halmos (1950) p. 233, bottom of the page. This makes some other steps (like step 11)
    invalid.
-/
noncomputable theory

open set has_inv function topological_space measurable_space
open_locale nnreal

namespace measure_theory

variables {G : Type*}

namespace measure

/-! We put the internal functions in the construction of the Haar measure in a namespace,
  so that the chosen names don't clash with other declarations.
  We first define a couple of the functions before proving the properties (that require that `G`
  is a topological group). -/
namespace haar

variables [group G]

/-- The index or Haar covering number or ratio of `K` w.r.t. `V`, denoted `(K : V)`:
  it is the smallest number of (left) translates of `V` that is necessary to cover `K`.
  It is defined to be 0 if no finite number of translates cover `K`. -/
def index (K V : set G) : ℕ :=
Inf $ finset.card '' {t : finset G | K ⊆ ⋃ g ∈ t, (λ h, g * h) ⁻¹' V }

lemma index_empty {V : set G} : index ∅ V = 0 :=
begin
  simp only [index, nat.Inf_eq_zero], left, use ∅,
  simp only [finset.card_empty, empty_subset, mem_set_of_eq, eq_self_iff_true, and_self],
end

variables [topological_space G]

/-- `prehaar K₀ U K` is a weighted version of the index, defined as `(K : U)/(K₀ : U)`.
  In the applications `K₀` is compact with non-empty interior, `U` is open containing `1`,
  and `K` is any compact set.
  The argument `K` is a (bundled) compact set, so that we can consider `prehaar K₀ U` as an
  element of `haar_product` (below). -/
def prehaar (K₀ U : set G) (K : compacts G) : ℝ := (index K.1 U : ℝ) / index K₀ U

lemma prehaar_empty (K₀ : positive_compacts G) {U : set G} : prehaar K₀.1 U ⊥ = 0 :=
by { simp only [prehaar, compacts.bot_val, index_empty, nat.cast_zero, euclidean_domain.zero_div] }

/-- `haar_product K₀` is a product of intervals `[0, (K : K₀)]`, for all compact sets `K`.
  For all `U`, we can show that `prehaar K₀ U ∈ haar_product K₀`. -/
def haar_product (K₀ : set G) : set (compacts G → ℝ) :=
set.pi set.univ (λ K, Icc 0 $ index K.1 K₀)

/-- The closure of the collection of elements of the form `prehaar K₀ U`,
  for `U` open neighbourhoods of `1`, contained in `V`.
  We show that the intersection of all these sets is nonempty, and the Haar measure
  on compact sets is defined to be an element in the closure of this intersection. -/
def cl_prehaar (K₀ : set G) (V : open_nhds_of (1 : G)) : set (compacts G → ℝ) :=
closure $ prehaar K₀ '' { U : set G | U ⊆ V.1 ∧ is_open U ∧ (1 : G) ∈ U }

variables [topological_group G]

/-! lemmas about `index` -/

/-- If `K` is compact and `V` has nonempty interior, then the index `(K : V)` is well-defined,
  there is a finite set `t` satisfying the desired properties. -/
lemma index_defined {K V : set G} (hK : is_compact K) (hV : (interior V).nonempty) :
  ∃ n : ℕ, n ∈ finset.card '' {t : finset G | K ⊆ ⋃ g ∈ t, (λ h, g * h) ⁻¹' V } :=
by { rcases compact_covered_by_mul_left_translates hK hV with ⟨t, ht⟩, exact ⟨t.card, t, ht, rfl⟩ }

lemma index_elim {K V : set G} (hK : is_compact K) (hV : (interior V).nonempty) :
  ∃ (t : finset G), K ⊆ (⋃ g ∈ t, (λ h, g * h) ⁻¹' V) ∧ finset.card t = index K V :=
by { have := nat.Inf_mem (index_defined hK hV), rwa [mem_image] at this }

lemma le_index_mul (K₀ : positive_compacts G) (K : compacts G) {V : set G}
  (hV : (interior V).nonempty) : index K.1 V ≤ index K.1 K₀.1 * index K₀.1 V :=
begin
  classical,
  rcases index_elim K.2 K₀.2.2 with ⟨s, h1s, h2s⟩,
  rcases index_elim K₀.2.1 hV with ⟨t, h1t, h2t⟩,
  rw [← h2s, ← h2t, mul_comm],
  refine le_trans _ finset.mul_card_le,
  apply nat.Inf_le, refine ⟨_, _, rfl⟩, rw [mem_set_of_eq], refine subset.trans h1s _,
  apply bUnion_subset, intros g₁ hg₁, rw preimage_subset_iff, intros g₂ hg₂,
  have := h1t hg₂,
  rcases this with ⟨_, ⟨g₃, rfl⟩, A, ⟨hg₃, rfl⟩, h2V⟩, rw [mem_preimage, ← mul_assoc] at h2V,
  exact mem_bUnion (finset.mul_mem_mul hg₃ hg₁) h2V
end

lemma index_pos (K : positive_compacts G) {V : set G} (hV : (interior V).nonempty) :
  0 < index K.1 V :=
begin
  unfold index, rw [nat.Inf_def, nat.find_pos, mem_image],
  { rintro ⟨t, h1t, h2t⟩, rw [finset.card_eq_zero] at h2t, subst h2t,
    cases K.2.2 with g hg,
    show g ∈ (∅ : set G), convert h1t (interior_subset hg), symmetry, apply bUnion_empty },
  { exact index_defined K.2.1 hV }
end

lemma index_mono {K K' V : set G} (hK' : is_compact K') (h : K ⊆ K')
  (hV : (interior V).nonempty) : index K V ≤ index K' V :=
begin
  rcases index_elim hK' hV with ⟨s, h1s, h2s⟩,
  apply nat.Inf_le, rw [mem_image], refine ⟨s, subset.trans h h1s, h2s⟩
end

lemma index_union_le (K₁ K₂ : compacts G) {V : set G} (hV : (interior V).nonempty) :
  index (K₁.1 ∪ K₂.1) V ≤ index K₁.1 V + index K₂.1 V :=
begin
  classical,
  rcases index_elim K₁.2 hV with ⟨s, h1s, h2s⟩,
  rcases index_elim K₂.2 hV with ⟨t, h1t, h2t⟩,
  rw [← h2s, ← h2t],
  refine le_trans _ (finset.card_union_le _ _),
  apply nat.Inf_le, refine ⟨_, _, rfl⟩, rw [mem_set_of_eq],
  apply union_subset; refine subset.trans (by assumption) _; apply bUnion_subset_bUnion_left;
    intros g hg; simp only [mem_def] at hg;
    simp only [mem_def, multiset.mem_union, finset.union_val, hg, or_true, true_or]
end

lemma index_union_eq (K₁ K₂ : compacts G) {V : set G} (hV : (interior V).nonempty)
  (h : disjoint (K₁.1 * V⁻¹) (K₂.1 * V⁻¹)) :
  index (K₁.1 ∪ K₂.1) V = index K₁.1 V + index K₂.1 V :=
begin
  classical,
  apply le_antisymm (index_union_le K₁ K₂ hV),
  rcases index_elim (K₁.2.union K₂.2) hV with ⟨s, h1s, h2s⟩, rw [← h2s],
  have : ∀(K : set G) , K ⊆ (⋃ g ∈ s, (λ h, g * h) ⁻¹' V) →
    index K V ≤ (s.filter (λ g, ((λ (h : G), g * h) ⁻¹' V ∩ K).nonempty)).card,
  { intros K hK, apply nat.Inf_le, refine ⟨_, _, rfl⟩, rw [mem_set_of_eq],
    intros g hg, rcases hK hg with ⟨_, ⟨g₀, rfl⟩, _, ⟨h1g₀, rfl⟩, h2g₀⟩,
    simp only [mem_preimage] at h2g₀,
    simp only [mem_Union], use g₀, split,
    { simp only [finset.mem_filter, h1g₀, true_and], use g,
      simp only [hg, h2g₀, mem_inter_eq, mem_preimage, and_self] },
    exact h2g₀ },
  refine le_trans (add_le_add (this K₁.1 $ subset.trans (subset_union_left _ _) h1s)
    (this K₂.1 $ subset.trans (subset_union_right _ _) h1s)) _,
  rw [← finset.card_union_eq, finset.filter_union_right],
  { apply finset.card_le_of_subset, apply finset.filter_subset },
  apply finset.disjoint_filter.mpr,
  rintro g₁ h1g₁ ⟨g₂, h1g₂, h2g₂⟩ ⟨g₃, h1g₃, h2g₃⟩,
  simp only [mem_preimage] at h1g₃ h1g₂,
  apply @h g₁⁻¹,
  split; simp only [set.mem_inv, set.mem_mul, exists_exists_and_eq_and, exists_and_distrib_left],
  { refine ⟨_, h2g₂, (g₁ * g₂)⁻¹, _, _⟩, simp only [inv_inv, h1g₂],
    simp only [mul_inv_rev, mul_inv_cancel_left] },
  { refine ⟨_, h2g₃, (g₁ * g₃)⁻¹, _, _⟩, simp only [inv_inv, h1g₃],
    simp only [mul_inv_rev, mul_inv_cancel_left] }
end

lemma mul_left_index_le {K : set G} (hK : is_compact K) {V : set G} (hV : (interior V).nonempty)
  (g : G) : index ((λ h, g * h) '' K) V ≤ index K V :=
begin
  rcases index_elim hK hV with ⟨s, h1s, h2s⟩, rw [← h2s],
  apply nat.Inf_le, rw [mem_image],
  refine ⟨s.map (equiv.mul_right g⁻¹).to_embedding, _, finset.card_map _⟩,
  { simp only [mem_set_of_eq], refine subset.trans (image_subset _ h1s) _,
    rintro _ ⟨g₁, ⟨_, ⟨g₂, rfl⟩, ⟨_, ⟨hg₂, rfl⟩, hg₁⟩⟩, rfl⟩,
    simp only [mem_preimage] at hg₁, simp only [exists_prop, mem_Union, finset.mem_map,
      equiv.coe_mul_right, exists_exists_and_eq_and, mem_preimage, equiv.to_embedding_coe_fn],
    refine ⟨_, hg₂, _⟩, simp only [mul_assoc, hg₁, inv_mul_cancel_left] }
end

lemma is_left_invariant_index {K : set G} (hK : is_compact K) {V : set G}
  (hV : (interior V).nonempty) (g : G) : index ((λ h, g * h) '' K) V = index K V :=
begin
  refine le_antisymm (mul_left_index_le hK hV g) _,
  convert mul_left_index_le (hK.image $ continuous_mul_left g) hV g⁻¹,
  rw [image_image], symmetry, convert image_id' _, ext h, apply inv_mul_cancel_left
end

/-! lemmas about `prehaar` -/

lemma prehaar_nonneg (K₀ : positive_compacts G) {U : set G} (K : compacts G)
  (hU : (interior U).nonempty) : 0 ≤ prehaar K₀.1 U K :=
by { apply div_nonneg; norm_cast, apply zero_le, exact index_pos K₀ hU }

lemma prehaar_le_index (K₀ : positive_compacts G) {U : set G} (K : compacts G)
  (hU : (interior U).nonempty) : prehaar K₀.1 U K ≤ index K.1 K₀.1 :=
begin
  unfold prehaar, rw [div_le_iff]; norm_cast,
  { apply le_index_mul K₀ K hU },
  { exact index_pos K₀ hU }
end

lemma prehaar_pos (K₀ : positive_compacts G) {U : set G} (hU : (interior U).nonempty)
  {K : set G} (h1K : is_compact K) (h2K : (interior K).nonempty) : 0 < prehaar K₀.1 U ⟨K, h1K⟩ :=
by { apply div_pos; norm_cast, apply index_pos ⟨K, h1K, h2K⟩ hU, exact index_pos K₀ hU }

lemma prehaar_mono {K₀ : positive_compacts G} {U : set G} (hU : (interior U).nonempty)
  {K₁ K₂ : compacts G} (h : K₁.1 ⊆ K₂.1) : prehaar K₀.1 U K₁ ≤ prehaar K₀.1 U K₂ :=
begin
  simp only [prehaar], rw [div_le_div_right], exact_mod_cast index_mono K₂.2 h hU,
  exact_mod_cast index_pos K₀ hU
end

lemma prehaar_self {K₀ : positive_compacts G} {U : set G} (hU : (interior U).nonempty) :
  prehaar K₀.1 U ⟨K₀.1, K₀.2.1⟩ = 1 :=
by { simp only [prehaar], rw [div_self], apply ne_of_gt, exact_mod_cast index_pos K₀ hU }

lemma prehaar_sup_le {K₀ : positive_compacts G} {U : set G} (K₁ K₂ : compacts G)
  (hU : (interior U).nonempty) : prehaar K₀.1 U (K₁ ⊔ K₂) ≤ prehaar K₀.1 U K₁ + prehaar K₀.1 U K₂ :=
begin
  simp only [prehaar], rw [div_add_div_same, div_le_div_right],
  exact_mod_cast index_union_le K₁ K₂ hU, exact_mod_cast index_pos K₀ hU
end

lemma prehaar_sup_eq {K₀ : positive_compacts G} {U : set G} {K₁ K₂ : compacts G}
  (hU : (interior U).nonempty) (h : disjoint (K₁.1 * U⁻¹) (K₂.1 * U⁻¹)) :
  prehaar K₀.1 U (K₁ ⊔ K₂) = prehaar K₀.1 U K₁ + prehaar K₀.1 U K₂ :=
by { simp only [prehaar], rw [div_add_div_same], congr', exact_mod_cast index_union_eq K₁ K₂ hU h }

lemma is_left_invariant_prehaar {K₀ : positive_compacts G} {U : set G} (hU : (interior U).nonempty)
  {K : compacts G} {g : G} : prehaar K₀.1 U (K.map _ $ continuous_mul_left g) = prehaar K₀.1 U K :=
by simp only [prehaar, compacts.map_val, is_left_invariant_index K.2 hU]

/-! Lemmas about `haar_product` -/

lemma prehaar_mem_haar_product (K₀ : positive_compacts G) {U : set G}
  (hU : (interior U).nonempty) : prehaar K₀.1 U ∈ haar_product K₀.1 :=
by { rintro ⟨K, hK⟩ h2K, rw [mem_Icc],
     exact ⟨prehaar_nonneg K₀ _ hU, prehaar_le_index K₀ _ hU⟩ }

lemma nonempty_Inter_cl_prehaar (K₀ : positive_compacts G) :
  (haar_product K₀.1 ∩ ⋂ (V : open_nhds_of (1 : G)), cl_prehaar K₀.1 V).nonempty :=
begin
  have : is_compact (haar_product K₀.1), { apply compact_univ_pi, intro K, apply compact_Icc },
  rw [← ne_empty_iff_nonempty],
  have := is_compact.elim_finite_subfamily_closed this (cl_prehaar K₀.1) (λ s, is_closed_closure),
  apply mt this, rintro ⟨t, h1t⟩, rw [← not_nonempty_iff_eq_empty] at h1t, apply h1t,
  let V₀ := ⋂ (V ∈ t), (V : open_nhds_of 1).1,
  have h1V₀ : is_open V₀,
  { apply is_open_bInter, apply finite_mem_finset, rintro ⟨V, hV⟩ h2V, exact hV.1 },
  have h2V₀ : (1 : G) ∈ V₀, { simp only [mem_Inter], rintro ⟨V, hV⟩ h2V, exact hV.2 },
  refine ⟨prehaar K₀.1 V₀, _⟩,
  split,
  { apply prehaar_mem_haar_product K₀, use 1, rwa h1V₀.interior_eq  },
  { simp only [mem_Inter], rintro ⟨V, hV⟩ h2V, apply subset_closure,
    apply mem_image_of_mem, rw [mem_set_of_eq],
    exact ⟨subset.trans (Inter_subset _ ⟨V, hV⟩) (Inter_subset _ h2V), h1V₀, h2V₀⟩ },
end

/-- the Haar measure on compact sets, defined to be an arbitrary element in the closure of
  all the sets `cl_prehaar K₀ V` in `haar_product K₀`. -/
def chaar (K₀ : positive_compacts G) (K : compacts G) : ℝ :=
classical.some (nonempty_Inter_cl_prehaar K₀) K

lemma chaar_mem_haar_product (K₀ : positive_compacts G) : chaar K₀ ∈ haar_product K₀.1 :=
(classical.some_spec (nonempty_Inter_cl_prehaar K₀)).1

lemma chaar_mem_cl_prehaar (K₀ : positive_compacts G) (V : open_nhds_of (1 : G)) :
  chaar K₀ ∈ cl_prehaar K₀.1 V :=
by { have := (classical.some_spec (nonempty_Inter_cl_prehaar K₀)).2, rw [mem_Inter] at this,
     exact this V }

lemma chaar_nonneg (K₀ : positive_compacts G) (K : compacts G) : 0 ≤ chaar K₀ K :=
by { have := chaar_mem_haar_product K₀ K (mem_univ _), rw mem_Icc at this, exact this.1 }

lemma chaar_empty (K₀ : positive_compacts G) : chaar K₀ ⊥ = 0 :=
begin
  let eval : (compacts G → ℝ) → ℝ := λ f, f ⊥, have : continuous eval := continuous_apply ⊥,
  show chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)},
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨set.univ, is_open_univ, mem_univ _⟩),
  unfold cl_prehaar, rw is_closed.closure_subset_iff,
  { rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩, apply prehaar_empty },
  { apply continuous_iff_is_closed.mp this, exact is_closed_singleton },
end

lemma chaar_self (K₀ : positive_compacts G) : chaar K₀ ⟨K₀.1, K₀.2.1⟩ = 1 :=
begin
  let eval : (compacts G → ℝ) → ℝ := λ f, f ⟨K₀.1, K₀.2.1⟩,
  have : continuous eval := continuous_apply _,
  show chaar K₀ ∈ eval ⁻¹' {(1 : ℝ)},
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨set.univ, is_open_univ, mem_univ _⟩),
  unfold cl_prehaar, rw is_closed.closure_subset_iff,
  { rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩, apply prehaar_self,
    rw h2U.interior_eq, exact ⟨1, h3U⟩ },
  { apply continuous_iff_is_closed.mp this, exact is_closed_singleton }
end

lemma chaar_mono {K₀ : positive_compacts G} {K₁ K₂ : compacts G} (h : K₁.1 ⊆ K₂.1) :
  chaar K₀ K₁ ≤ chaar K₀ K₂ :=
begin
  let eval : (compacts G → ℝ) → ℝ := λ f, f K₂ - f K₁,
  have : continuous eval := continuous_sub.comp
    (continuous.prod_mk (continuous_apply K₂) (@continuous_apply _ (λ _, ℝ) _ K₁)),
  rw [← sub_nonneg], show chaar K₀ ∈ eval ⁻¹' (Ici (0 : ℝ)),
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨set.univ, is_open_univ, mem_univ _⟩),
  unfold cl_prehaar, rw is_closed.closure_subset_iff,
  { rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩, simp only [mem_preimage, mem_Ici, eval, sub_nonneg],
    apply prehaar_mono _ h, rw h2U.interior_eq, exact ⟨1, h3U⟩ },
  { apply continuous_iff_is_closed.mp this, exact is_closed_Ici },
end

lemma chaar_sup_le {K₀ : positive_compacts G} (K₁ K₂ : compacts G) :
  chaar K₀ (K₁ ⊔ K₂) ≤ chaar K₀ K₁ + chaar K₀ K₂ :=
begin
  let eval : (compacts G → ℝ) → ℝ := λ f, f K₁ + f K₂ - f (K₁ ⊔ K₂),
  have : continuous eval := continuous_sub.comp
    (continuous.prod_mk (continuous_add.comp
      (continuous.prod_mk (continuous_apply K₁) (@continuous_apply _ (λ _, ℝ) _ K₂)))
      (@continuous_apply _ (λ _, ℝ) _(K₁ ⊔ K₂))),
  rw [← sub_nonneg], show chaar K₀ ∈ eval ⁻¹' (Ici (0 : ℝ)),
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨set.univ, is_open_univ, mem_univ _⟩),
  unfold cl_prehaar, rw is_closed.closure_subset_iff,
  { rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩, simp only [mem_preimage, mem_Ici, eval, sub_nonneg],
    apply prehaar_sup_le, rw h2U.interior_eq, exact ⟨1, h3U⟩ },
  { apply continuous_iff_is_closed.mp this, exact is_closed_Ici },
end

lemma chaar_sup_eq [t2_space G] {K₀ : positive_compacts G} {K₁ K₂ : compacts G}
  (h : disjoint K₁.1 K₂.1) : chaar K₀ (K₁ ⊔ K₂) = chaar K₀ K₁ + chaar K₀ K₂ :=
begin
  rcases compact_compact_separated K₁.2 K₂.2 (disjoint_iff.mp h) with
    ⟨U₁, U₂, h1U₁, h1U₂, h2U₁, h2U₂, hU⟩,
  rw [← disjoint_iff_inter_eq_empty] at hU,
  rcases compact_open_separated_mul K₁.2 h1U₁ h2U₁ with ⟨V₁, h1V₁, h2V₁, h3V₁⟩,
  rcases compact_open_separated_mul K₂.2 h1U₂ h2U₂ with ⟨V₂, h1V₂, h2V₂, h3V₂⟩,
  let eval : (compacts G → ℝ) → ℝ := λ f, f K₁ + f K₂ - f (K₁ ⊔ K₂),
  have : continuous eval := continuous_sub.comp
    (continuous.prod_mk (continuous_add.comp
      (continuous.prod_mk (continuous_apply K₁) (@continuous_apply _ (λ _, ℝ) _ K₂)))
      (@continuous_apply _ (λ _, ℝ) _(K₁ ⊔ K₂))),
  rw [eq_comm, ← sub_eq_zero], show chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)},
  let V := V₁ ∩ V₂,
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀
    ⟨V⁻¹, continuous_inv V (is_open_inter h1V₁ h1V₂),
    by simp only [mem_inv, one_inv, h2V₁, h2V₂, V, mem_inter_eq, true_and]⟩),
  unfold cl_prehaar, rw is_closed.closure_subset_iff,
  { rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩,
    simp only [mem_preimage, eval, sub_eq_zero, mem_singleton_iff], rw [eq_comm],
    apply prehaar_sup_eq,
    { rw h2U.interior_eq, exact ⟨1, h3U⟩ },
    { refine disjoint_of_subset _ _ hU,
      { refine subset.trans (mul_subset_mul subset.rfl _) h3V₁,
        exact subset.trans (inv_subset.mpr h1U) (inter_subset_left _ _) },
      { refine subset.trans (mul_subset_mul subset.rfl _) h3V₂,
        exact subset.trans (inv_subset.mpr h1U) (inter_subset_right _ _) }}},
  { apply continuous_iff_is_closed.mp this, exact is_closed_singleton },
end

lemma is_left_invariant_chaar {K₀ : positive_compacts G} {K : compacts G} {g : G} :
  chaar K₀ (K.map _ $ continuous_mul_left g) = chaar K₀ K :=
begin
  let eval : (compacts G → ℝ) → ℝ := λ f, f (K.map _ $ continuous_mul_left g) - f K,
  have : continuous eval := continuous_sub.comp
    (continuous.prod_mk (continuous_apply (K.map _ _)) (@continuous_apply _ (λ _, ℝ) _ K)),
  rw [← sub_eq_zero], show chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)},
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨set.univ, is_open_univ, mem_univ _⟩),
  unfold cl_prehaar, rw is_closed.closure_subset_iff,
  { rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩,
    simp only [mem_singleton_iff, mem_preimage, eval, sub_eq_zero],
    apply is_left_invariant_prehaar, rw h2U.interior_eq, exact ⟨1, h3U⟩ },
  { apply continuous_iff_is_closed.mp this, exact is_closed_singleton },
end

/-- The function `chaar` interpreted in `ennreal` -/
@[reducible] def echaar (K₀ : positive_compacts G) (K : compacts G) : ennreal :=
show nnreal, from ⟨chaar K₀ K, chaar_nonneg _ _⟩

/-- The variant of `chaar_sup_le` for `echaar` -/
lemma echaar_sup_le {K₀ : positive_compacts G} (K₁ K₂ : compacts G) :
  echaar K₀ (K₁ ⊔ K₂) ≤ echaar K₀ K₁ + echaar K₀ K₂ :=
by { norm_cast, simp only [←nnreal.coe_le_coe, nnreal.coe_add, subtype.coe_mk, chaar_sup_le]}

/-- The variant of `chaar_mono` for `echaar` -/
lemma echaar_mono {K₀ : positive_compacts G} ⦃K₁ K₂ : compacts G⦄ (h : K₁.1 ⊆ K₂.1) :
  echaar K₀ K₁ ≤ echaar K₀ K₂ :=
by { norm_cast, simp only [←nnreal.coe_le_coe, subtype.coe_mk, chaar_mono, h] }

end haar
open haar

variables [topological_space G] [t2_space G] [group G] [topological_group G]

/-- The Haar outer measure on `G`. It is not normalized, and is mainly used to construct
  `haar_measure`, which is a normalized measure. -/
def haar_outer_measure (K₀ : positive_compacts G) : outer_measure G :=
outer_measure.of_content (echaar K₀) $
  by { rw echaar, norm_cast, rw [←nnreal.coe_eq, nnreal.coe_zero, subtype.coe_mk, chaar_empty] }

lemma haar_outer_measure_eq_infi (K₀ : positive_compacts G) (A : set G) :
  haar_outer_measure K₀ A = ⨅ (U : set G) (hU : is_open U) (h : A ⊆ U),
    inner_content (echaar K₀) ⟨U, hU⟩ :=
outer_measure.of_content_eq_infi echaar_sup_le A

lemma chaar_le_haar_outer_measure {K₀ : positive_compacts G} (K : compacts G) :
   (show ℝ≥0, from ⟨chaar K₀ K, chaar_nonneg K₀ K⟩ : ennreal) ≤ haar_outer_measure K₀ K.1 :=
outer_measure.le_of_content_compacts echaar_sup_le K

lemma haar_outer_measure_of_is_open {K₀ : positive_compacts G} (U : set G) (hU : is_open U) :
  haar_outer_measure K₀ U =
  inner_content (λ K, show ℝ≥0, from ⟨chaar K₀ K, chaar_nonneg K₀ K⟩) ⟨U, hU⟩ :=
outer_measure.of_content_opens echaar_sup_le ⟨U, hU⟩

lemma haar_outer_measure_le_chaar {K₀ : positive_compacts G} {U : set G} (hU : is_open U)
  (K : compacts G) (h : U ⊆ K.1) :
  haar_outer_measure K₀ U ≤ show ℝ≥0, from ⟨chaar K₀ K, chaar_nonneg K₀ K⟩ :=
begin
  rw haar_outer_measure_of_is_open U hU,
  refine inner_content_le _ _ K h, intros K₁ K₂ hK,
  norm_cast, rw [← nnreal.coe_le_coe], exact chaar_mono hK
end

lemma haar_outer_measure_exists_open {K₀ : positive_compacts G} {A : set G}
  (hA : haar_outer_measure K₀ A < ⊤) {ε : ℝ≥0} (hε : 0 < ε) :
  ∃ U : opens G, A ⊆ U ∧ haar_outer_measure K₀ U ≤ haar_outer_measure K₀ A + ε :=
outer_measure.of_content_exists_open echaar_sup_le hA hε

lemma haar_outer_measure_exists_compact {K₀ : positive_compacts G} {U : opens G}
  (hU : haar_outer_measure K₀ U < ⊤) {ε : ℝ≥0} (hε : 0 < ε) :
  ∃ K : compacts G, K.1 ⊆ U ∧ haar_outer_measure K₀ U ≤ haar_outer_measure K₀ K.1 + ε :=
outer_measure.of_content_exists_compact echaar_sup_le hU hε

lemma haar_outer_measure_caratheodory {K₀ : positive_compacts G} (A : set G) :
  (haar_outer_measure K₀).caratheodory.is_measurable A ↔ ∀ (U : opens G),
  haar_outer_measure K₀ (U ∩ A) + haar_outer_measure K₀ (U \ A) ≤ haar_outer_measure K₀ U :=
outer_measure.of_content_caratheodory echaar_sup_le A

lemma one_le_haar_outer_measure_self {K₀ : positive_compacts G} : 1 ≤ haar_outer_measure K₀ K₀.1 :=
begin
  rw [haar_outer_measure_eq_infi],
  refine le_binfi _, intros U hU, refine le_infi _, intros h2U,
  refine le_trans _ (le_supr _ ⟨K₀.1, K₀.2.1⟩), refine le_trans _ (le_supr _ h2U),
  simp only [←nnreal.coe_le_coe, subtype.coe_mk, ennreal.one_le_coe_iff, nnreal.coe_one],
  rw [chaar_self]
end

lemma haar_outer_measure_pos_of_is_open {K₀ : positive_compacts G}
  {U : set G} (hU : is_open U) (h2U : U.nonempty) : 0 < haar_outer_measure K₀ U :=
begin
  refine outer_measure.of_content_pos_of_is_open echaar_sup_le _ ⟨K₀.1, K₀.2.1⟩ _ hU h2U,
  { intros g K, simpa only [ennreal.coe_eq_coe, ←nnreal.coe_eq] using is_left_invariant_chaar },
  simp only [ennreal.coe_pos, ←nnreal.coe_pos, chaar_self, zero_lt_one, subtype.coe_mk]
end

lemma haar_outer_measure_self_pos {K₀ : positive_compacts G} :
  0 < haar_outer_measure K₀ K₀.1 :=
lt_of_lt_of_le (haar_outer_measure_pos_of_is_open is_open_interior K₀.2.2)
               ((haar_outer_measure K₀).mono interior_subset)

lemma haar_outer_measure_lt_top_of_is_compact [locally_compact_space G] {K₀ : positive_compacts G}
  {K : set G} (hK : is_compact K) : haar_outer_measure K₀ K < ⊤ :=
begin
  rcases exists_compact_superset hK with ⟨F, h1F, h2F⟩,
  refine lt_of_le_of_lt ((haar_outer_measure K₀).mono h2F) _,
  refine lt_of_le_of_lt (haar_outer_measure_le_chaar is_open_interior ⟨F, h1F⟩ interior_subset)
    ennreal.coe_lt_top
end

variables [S : measurable_space G] [borel_space G]
include S

lemma haar_caratheodory_measurable (K₀ : positive_compacts G) :
  S ≤ (haar_outer_measure K₀).caratheodory :=
begin
  rw [@borel_space.measurable_eq G _ _], refine generate_from_le _,
  intros U hU, rw haar_outer_measure_caratheodory, intro U',
  rw haar_outer_measure_of_is_open ((U' : set G) ∩ U) (is_open_inter U'.prop hU),
  simp only [inner_content, supr_subtype'], rw [opens.coe_mk],
  haveI : nonempty {L : compacts G // L.1 ⊆ U' ∩ U} := ⟨⟨⊥, empty_subset _⟩⟩,
  rw [ennreal.supr_add],
  refine supr_le _, rintro ⟨L, hL⟩, simp only [subset_inter_iff] at hL,
  have : ↑U' \ U ⊆ U' \ L.1 := diff_subset_diff_right hL.2,
  refine le_trans (add_le_add_left ((haar_outer_measure K₀).mono' this) _) _,
  rw haar_outer_measure_of_is_open (↑U' \ L.1) (is_open_diff U'.2 L.2.is_closed),
  simp only [inner_content, supr_subtype'], rw [opens.coe_mk],
  haveI : nonempty {M : compacts G // M.1 ⊆ ↑U' \ L.1} := ⟨⟨⊥, empty_subset _⟩⟩,
  rw [ennreal.add_supr], refine supr_le _, rintro ⟨M, hM⟩, simp only [subset_diff] at hM,
  have : (L ⊔ M).1 ⊆ U',
  { simp only [union_subset_iff, compacts.sup_val, hM, hL, and_self] },
  rw haar_outer_measure_of_is_open ↑U' U'.2,
  refine le_trans (ge_of_eq _) (le_inner_content _ _ this), norm_cast,
  simp only [←nnreal.coe_eq, nnreal.coe_add, subtype.coe_mk], exact chaar_sup_eq hM.2.symm
end

/-- the Haar measure on `G`, scaled so that `haar_measure K₀ K₀ = 1`. -/
def haar_measure (K₀ : positive_compacts G) : measure G :=
(haar_outer_measure K₀ K₀.1)⁻¹ •
  (haar_outer_measure K₀).to_measure (haar_caratheodory_measurable K₀)

lemma haar_measure_apply {K₀ : positive_compacts G} {s : set G} (hs : is_measurable s) :
  haar_measure K₀ s = haar_outer_measure K₀ s / haar_outer_measure K₀ K₀.1 :=
by { simp only [haar_measure, hs, ennreal.div_def, mul_comm, to_measure_apply,
      algebra.id.smul_eq_mul, pi.smul_apply, measure.coe_smul] }

lemma is_left_invariant_haar_measure (K₀ : positive_compacts G) :
  is_left_invariant (haar_measure K₀) :=
begin
  intros g A hA, rw [haar_measure_apply hA, haar_measure_apply],
  { congr' 1, refine outer_measure.is_left_invariant_of_content echaar_sup_le _ g A,
    intros g K, simpa only [ennreal.coe_eq_coe, ←nnreal.coe_eq] using is_left_invariant_chaar },
  { exact measurable_mul_left g hA }
end

lemma haar_measure_self [locally_compact_space G] {K₀ : positive_compacts G} :
  haar_measure K₀ K₀.1 = 1 :=
begin
  rw [haar_measure_apply K₀.2.1.is_measurable, ennreal.div_self],
  { rw [← zero_lt_iff_ne_zero], exact haar_outer_measure_self_pos },
  { exact ne_of_lt (haar_outer_measure_lt_top_of_is_compact K₀.2.1) }
end

lemma haar_measure_pos_of_is_open [locally_compact_space G] {K₀ : positive_compacts G}
  {U : set G} (hU : is_open U) (h2U : U.nonempty) : 0 < haar_measure K₀ U :=
begin
  rw [haar_measure_apply hU.is_measurable, ennreal.div_pos_iff],
  refine ⟨_, ne_of_lt $ haar_outer_measure_lt_top_of_is_compact K₀.2.1⟩,
  rw [← zero_lt_iff_ne_zero], apply haar_outer_measure_pos_of_is_open hU h2U
end

lemma regular_haar_measure [locally_compact_space G] {K₀ : positive_compacts G} :
  (haar_measure K₀).regular :=
begin
  apply measure.regular.smul, split,
  { intros K hK, rw [to_measure_apply _ _ hK.is_measurable],
    apply haar_outer_measure_lt_top_of_is_compact hK },
  { intros A hA, rw [to_measure_apply _ _ hA, haar_outer_measure_eq_infi],
    refine binfi_le_binfi _, intros U hU, refine infi_le_infi _, intro h2U,
    rw [to_measure_apply _ _ hU.is_measurable, haar_outer_measure_of_is_open U hU], refl' },
  { intros U hU, rw [to_measure_apply _ _ hU.is_measurable, haar_outer_measure_of_is_open U hU],
    dsimp only [inner_content], refine bsupr_le (λ K hK, _),
    refine le_supr_of_le K.1 _, refine le_supr_of_le K.2 _, refine le_supr_of_le hK _,
    rw [to_measure_apply _ _ K.2.is_measurable], apply chaar_le_haar_outer_measure },
  { rw ennreal.inv_lt_top, apply haar_outer_measure_self_pos }
end

end measure

end measure_theory

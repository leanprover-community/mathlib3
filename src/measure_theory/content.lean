/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.measure_space
import measure_theory.borel_space
import topology.opens
import topology.compacts
/-!
# Contents

In this file e work with *contents*. A content is a function from a certain class of subsets
to `ennreal` (or `nnreal`) that is additive, subadditive and monotone. We show that:
* Given a content `λ` on compact sets, we get a countably subadditive map that vanishes at `∅`.
  In Halmos (1950) this is called the *inner content* `λ*` of `λ`.
* Given an inner content, we define an outer measure.

We don't explicitly define the type of contents.
In this file we only work on contents on compact sets, and inner contents on open sets, and both
contents and inner contents map into the extended nonnegative reals. However, in other applications
other choices can be made, and it is not a priori clear what the best interface should be.

## Main definitions
* `measure_theory.inner_content`: define an inner content from an content
* `measure_theory.outer_measure.of_inner_content`: construct an outer measure from an inner content.
* `measure_theory.outer_measure.of_content`: construct an outer measure from a content
  (by concatenating the previous two constructions).

## References

* Paul Halmos (1950), Measure Theory, §53
-/
universe variables u v w
noncomputable theory

open set topological_space

namespace measure_theory

variables {G : Type w} [topological_space G]

/-- Constructing the inner content of a content. From a content defined on the compact sets, we
  obtain a function defined on all open sets, by taking the supremum of the content of all compact
  subsets. -/
def inner_content (μ : compacts G → ennreal) (U : opens G) : ennreal :=
⨆ (K : compacts G) (h : K.1 ⊆ U), μ K

lemma le_inner_content {μ : compacts G → ennreal} (K : compacts G) (U : opens G)
  (h2 : K.1 ⊆ U) : μ K ≤ inner_content μ U :=
le_supr_of_le K $ le_supr _ h2

lemma inner_content_le {μ : compacts G → ennreal}
  (h : ∀ (K₁ K₂ : compacts G), K₁.1 ⊆ K₂.1 → μ K₁ ≤ μ K₂)
  (U : opens G) (K : compacts G)
  (h2 : (U : set G) ⊆ K.1) : inner_content μ U ≤ μ K :=
supr_le $ λ K', supr_le $ λ hK', h _ _ (subset.trans hK' h2)

lemma inner_content_of_is_compact {μ : compacts G → ennreal}
  (h : ∀ (K₁ K₂ : compacts G), K₁.1 ⊆ K₂.1 → μ K₁ ≤ μ K₂) {K : set G} (h1K : is_compact K)
  (h2K : is_open K) : inner_content μ ⟨K, h2K⟩ = μ ⟨K, h1K⟩ :=
le_antisymm (supr_le $ λ K', supr_le $ λ hK', h _ ⟨K, h1K⟩ hK')
            (le_inner_content _ _ subset.rfl)

lemma inner_content_empty {μ : compacts G → ennreal} (h : μ ⊥ = 0) :
  inner_content μ ∅ = 0 :=
begin
  refine le_antisymm _ (zero_le _), rw ←h,
  refine supr_le (λ K, supr_le (λ hK, _)),
  have : K = ⊥, { ext1, rw [subset_empty_iff.mp hK, compacts.bot_val] }, rw this, refl'
end

lemma inner_content_mono {μ : compacts G → ennreal} {{U V : opens G}} (h2 : (U : set G) ⊆ V.1) :
  inner_content μ U ≤ inner_content μ V :=
supr_le_supr $ λ K, supr_le_supr_const $ λ hK, subset.trans hK h2

lemma inner_content_exists_compact {μ : compacts G → ennreal} {U : opens G}
  (hU : inner_content μ U < ⊤) {ε : nnreal} (hε : 0 < ε) :
  ∃ K : compacts G, K.1 ⊆ U ∧ inner_content μ U ≤ μ K + ε :=
begin
  have h'ε := ennreal.zero_lt_coe_iff.2 hε,
  cases le_or_lt (inner_content μ U) ε,
  { exact ⟨⊥, empty_subset _, le_trans h (le_add_of_nonneg_left (zero_le _))⟩ },
  have := ennreal.sub_lt_sub_self (ne_of_lt hU) (ne_of_gt $ lt_trans h'ε h) h'ε,
  conv at this {to_rhs, rw inner_content }, simp only [lt_supr_iff] at this,
  rcases this with ⟨U, h1U, h2U⟩, refine ⟨U, h1U, _⟩,
  rw [← ennreal.sub_le_iff_le_add], exact le_of_lt h2U
end

lemma inner_content_Sup_nat [t2_space G] {μ : compacts G → ennreal}
  (h1 : μ ⊥ = 0)
  (h2 : ∀ (K₁ K₂ : compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂) (U : ℕ → opens G) :
  inner_content μ (⨆ (i : ℕ), U i) ≤ ∑' (i : ℕ), inner_content μ (U i) :=
begin
  have h3 : ∀ (t : finset ℕ) (K : ℕ → compacts G), μ (t.sup K) ≤ t.sum (λ i, μ (K i)),
  { intros t K, refine finset.induction_on t _ _,
    { simp only [h1, le_zero_iff_eq, finset.sum_empty, finset.sup_empty] },
    { intros n s hn ih, rw [finset.sup_insert, finset.sum_insert hn],
      exact le_trans (h2 _ _) (add_le_add_left ih _) }},
  refine supr_le (λ K, supr_le (λ hK, _)),
  rcases is_compact.elim_finite_subcover K.2 _ (λ i, (U i).prop) _ with ⟨t, ht⟩, swap,
  { convert hK, rw [opens.supr_def, subtype.coe_mk] },
  rcases K.2.finite_compact_cover t (coe ∘ U) (λ i _, (U _).prop) (by simp only [ht])
    with ⟨K', h1K', h2K', h3K'⟩,
  let L : ℕ → compacts G := λ n, ⟨K' n, h1K' n⟩,
  convert le_trans (h3 t L) _,
  { ext1, rw [h3K', compacts.finset_sup_val, finset.sup_eq_supr] },
  refine le_trans (finset.sum_le_sum _) (ennreal.sum_le_tsum t),
  intros i hi, refine le_trans _ (le_supr _ (L i)),
  refine le_trans _ (le_supr _ (h2K' i)), refl'
end

lemma is_left_invariant_inner_content [group G] [topological_group G] {μ : compacts G → ennreal}
  (h : ∀ (g : G) {K : compacts G}, μ (K.map _ $ continuous_mul_left g) = μ K) (g : G)
  (U : opens G) : inner_content μ (U.comap $ continuous_mul_left g) = inner_content μ U :=
begin
  refine supr_congr _ ((compacts.equiv (homeomorph.mul_left g)).surjective) _,
  intro K, refine supr_congr_Prop image_subset_iff _,
  intro hK, simp only [equiv.coe_fn_mk, subtype.mk_eq_mk, ennreal.coe_eq_coe, compacts.equiv],
  apply h
end

lemma inner_content_pos [t2_space G] [group G] [topological_group G] {μ : compacts G → ennreal}
  (h1 : μ ⊥ = 0)
  (h2 : ∀ (K₁ K₂ : compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂)
  (h3 : ∀ (g : G) {K : compacts G}, μ (K.map _ $ continuous_mul_left g) = μ K)
  (K : compacts G) (hK : 0 < μ K) (U : opens G) (hU : (U : set G).nonempty) :
  0 < inner_content μ U :=
begin
  have : (interior (U : set G)).nonempty, rwa [interior_eq_of_open U.prop],
  rcases compact_covered_by_mul_left_translates K.2 this with ⟨s, hs⟩,
  suffices : μ K ≤ s.card * inner_content μ U,
  { exact (ennreal.mul_pos.mp $ lt_of_lt_of_le hK this).2 },
  have : K.1 ⊆ ↑⨆ (g ∈ s), U.comap $ continuous_mul_left g,
  { simpa only [opens.supr_def, opens.coe_comap, subtype.coe_mk] },
  refine le_trans (le_inner_content _ _ this) _,
  refine le_trans
    (rel_supr_sum (inner_content μ) (inner_content_empty h1) (≤) (inner_content_Sup_nat h1 h2) _ _) _,
  simp only [is_left_invariant_inner_content h3, finset.sum_const, nsmul_eq_mul, le_refl]
end

namespace outer_measure

/-- Extending an "inner content" on opens to an outer measure on all sets.
  This is only the underlying function.

  Remark: this is very similar to `outer_measure.of_function μ` (where we treat values where
  `μ` is undefined as `⊤`). -/
def of_inner_content_def (μ : opens G → ennreal) (A : set G) : ennreal :=
⨅ (U : opens G) (h : A ⊆ U), μ U

lemma of_inner_content_le_opens {μ : opens G → ennreal} (U : opens G) :
  of_inner_content_def μ U ≤ μ U :=
infi_le_of_le U (infi_le _ subset.rfl)

/-- We prove a second version of the previous lemma, because even though the previous lemma applies
  in this case, applying it will take 10+ seconds to unify, presumably because it unfolds all
  definitions involving (enn)reals. -/
lemma of_inner_content_le_of_is_open {μ : opens G → ennreal}
  {U : set G} (hU : is_open U) : of_inner_content_def μ U ≤ μ ⟨U, hU⟩ :=
infi_le_of_le ⟨U, hU⟩ (infi_le _ subset.rfl)

#exit
lemma of_inner_content_opens {μ : opens G → ennreal}
  (h : ∀ (U V : opens G), (U : set G) ⊆ V.1 → μ U ≤ μ V) (U : opens G) :
  of_inner_content_def μ U = μ U :=
le_antisymm (of_inner_content_le_opens U)
            (le_infi (λ V, le_infi $ λ hV, h U _ hV))

lemma of_inner_content_empty {μ : opens G → ennreal} (h : μ ∅ = 0) :
  of_inner_content_def μ ∅ = 0 :=
begin
  refine le_antisymm _ (zero_le _), rw ←h,
  exact infi_le_of_le ∅ (infi_le _ subset.rfl)
end

lemma of_inner_content_mono {μ : opens G → ennreal}
  {{A B : set G}} (h2 : A ⊆ B) : of_inner_content_def μ A ≤ of_inner_content_def μ B :=
infi_le_infi $ λ U, infi_le_infi_const (subset.trans h2)

lemma of_inner_content_exists_open' {μ : opens G → ennreal} {A : set G}
  (hA : of_inner_content_def μ A < ⊤) {ε : nnreal} (hε : 0 < ε) :
  ∃ U : opens G, A ⊆ U ∧ μ U ≤ of_inner_content_def μ A + ε :=
begin
  have := ennreal.lt_add_right hA (ennreal.zero_lt_coe_iff.2 hε),
  conv at this {to_lhs, rw of_inner_content_def }, simp only [infi_lt_iff] at this,
  rcases this with ⟨U, h1U, h2U⟩, exact ⟨U, h1U, le_of_lt h2U⟩
end

lemma of_inner_content_exists_open {μ : opens G → ennreal} {A : set G}
  (hA : of_inner_content_def μ A < ⊤) {ε : nnreal} (hε : 0 < ε) :
  ∃ U : opens G, A ⊆ U ∧ of_inner_content_def μ U ≤ of_inner_content_def μ A + ε :=
begin
  rcases of_inner_content_exists_open' hA hε with ⟨U, h1U, h2U⟩,
  refine ⟨U, h1U, le_trans (of_inner_content_le_opens U) h2U⟩
end

lemma of_inner_content_Union_nat {μ : opens G → ennreal}
  (h2 : ∀ (s : ℕ → opens G), μ (⨆ (i : ℕ), s i) ≤ ∑' (i : ℕ), μ (s i)) (s : ℕ → set G) :
  of_inner_content_def μ (⋃ (i : ℕ), s i) ≤ ∑' (i : ℕ), of_inner_content_def μ (s i) :=
begin
  apply ennreal.le_of_forall_epsilon_le, intros ε hε h3,
  rcases ennreal.exists_pos_sum_of_encodable (ennreal.zero_lt_coe_iff.2 hε) ℕ with ⟨ε', hε', h2ε'⟩,
  refine le_trans _ (add_le_add_left (le_of_lt h2ε') _),
  rw ← ennreal.tsum_add,
  have : ∀ i, ∃ U : opens G, s i ⊆ U ∧ μ U ≤ of_inner_content_def μ (s i) + ε' i :=
    λ i, of_inner_content_exists_open' (lt_of_le_of_lt (by exact ennreal.le_tsum i) h3) (hε' i),
  choose U hU using this,
  refine le_trans (of_inner_content_mono (Union_subset_Union (λ i, (hU i).1))) _,
  refine le_trans (of_inner_content_le_of_is_open $ is_open_Union (λ i, (U i).property)) _,
  rw ← opens.supr_def, refine le_trans (h2 _) _, convert ennreal.tsum_le_tsum (λ i, (hU i).2)
end

lemma is_left_invariant_of_inner_content [group G] [topological_group G] {μ : opens G → ennreal}
  (h : ∀ (g : G) (U : opens G), μ (U.comap $ continuous_mul_left g) = μ U) {g : G}
  {A : set G} : of_inner_content_def μ ((λ h, g * h) ⁻¹' A) = of_inner_content_def μ A :=
begin
  symmetry, refine infi_congr _ ((opens.equiv (homeomorph.mul_left g)).symm.surjective) _,
  intro U, refine infi_congr_Prop _ _,
  { apply preimage_subset_preimage_iff,
    rw function.surjective.range_eq, apply subset_univ, exact (equiv.mul_left g).surjective },
  intro hU, exact h g U
end

/-- Extending a inner content on opens to an outer measure. The underlying function is given by
  `outer_measure.of_inner_content_def`. -/
def of_inner_content (μ : opens G → ennreal) (h1 : μ ∅ = 0)
  (h2 : ∀ (s : ℕ → opens G), μ (⨆ (i : ℕ), s i) ≤ ∑' (i : ℕ), μ (s i)) : outer_measure G :=
{ measure_of := of_inner_content_def μ,
  empty := of_inner_content_empty h1,
  mono := of_inner_content_mono,
  Union_nat := of_inner_content_Union_nat h2 }

lemma of_inner_content_caratheodory {μ : opens G → ennreal} {h1 : μ ∅ = 0}
  {h2 : ∀ (s : ℕ → opens G), μ (⨆ (i : ℕ), s i) ≤ ∑' (i : ℕ), μ (s i)} (A : set G) :
  (of_inner_content μ h1 h2).caratheodory.is_measurable A ↔ ∀ (U : opens G),
  of_inner_content μ h1 h2 (U ∩ A) + of_inner_content μ h1 h2 (U \ A) ≤ of_inner_content μ h1 h2 U :=
begin
  split,
  { intros h U, exact ge_of_eq (h U) },
  { intros h B, refine le_antisymm (le_inter_add_diff _) _,
    refine le_infi _, intro U, refine le_infi _, intro hU,
    refine le_trans _ (le_trans (h U) $ of_inner_content_le_opens _),
    refine add_le_add (of_inner_content_mono $ inter_subset_inter_left _ hU)
      (of_inner_content_mono $ diff_subset_diff_left hU) }
end

/-- Extending a content on compact sets to an outer measure on all sets. -/
def of_content [t2_space G] (μ : compacts G → ennreal) (h1 : μ ⊥ = 0)
  (h2 : ∀ (K₁ K₂ : compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂) : outer_measure G :=
of_inner_content
  (inner_content μ)
  (inner_content_empty h1)
  (inner_content_Sup_nat h1 h2)

variables [t2_space G] {μ : compacts G → ennreal} {h1 : μ ⊥ = 0}
  {h2 : ∀ (K₁ K₂ : compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂}

lemma of_content_opens (U : opens G) : of_content μ h1 h2 U = inner_content μ U :=
of_inner_content_opens inner_content_mono U

lemma le_of_content_compacts (K : compacts G) : μ K ≤ of_content μ h1 h2 K.1 :=
le_infi $ λ U, le_infi $ le_inner_content K U

lemma of_content_interior_compacts (h3 : ∀ (K₁ K₂ : compacts G), K₁.1 ⊆ K₂.1 → μ K₁ ≤ μ K₂)
  (K : compacts G) : of_content μ h1 h2 (interior K.1) ≤ μ K :=
le_trans (le_of_eq $ of_content_opens (opens.interior K.1))
         (inner_content_le h3 _ _ interior_subset)

lemma of_content_exists_compact {U : opens G} (hU : of_content μ h1 h2 U < ⊤) {ε : nnreal}
  (hε : 0 < ε) : ∃ K : compacts G, K.1 ⊆ U ∧ of_content μ h1 h2 U ≤ of_content μ h1 h2 K.1 + ε :=
begin
  rw [of_content_opens] at hU ⊢,
  rcases inner_content_exists_compact hU hε with ⟨K, h1K, h2K⟩,
  exact ⟨K, h1K, le_trans h2K $ add_le_add_right (le_of_content_compacts K) _⟩
end

lemma of_content_exists_open {A : set G} (hA : of_content μ h1 h2 A < ⊤) {ε : nnreal} (hε : 0 < ε) :
  ∃ U : opens G, A ⊆ U ∧ of_content μ h1 h2 U ≤ of_content μ h1 h2 A + ε :=
of_inner_content_exists_open hA hε

lemma of_content_pos_of_is_open [group G] [topological_group G]
  (h3 : ∀ (g : G) {K : compacts G}, μ (K.map _ $ continuous_mul_left g) = μ K)
  (K : compacts G) (hK : 0 < μ K) {U : set G} (h1U : is_open U) (h2U : U.nonempty) :
  0 < of_content μ h1 h2 U :=
by { convert inner_content_pos h1 h2 h3 K hK ⟨U, h1U⟩ h2U, exact of_content_opens ⟨U, h1U⟩ }

end outer_measure
end measure_theory

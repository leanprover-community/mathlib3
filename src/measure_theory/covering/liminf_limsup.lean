/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import measure_theory.covering.density_theorem

/-!
# Liminf, limsup, and doubling measures.

This file is a place to collect lemmas about liminf and limsup for subsets of a metric space
carrying a doubling measure.

## Main results:

 * `blimsup_cthickening_mul_ae_eq`: the limsup of the closed thickening of a sequence of compact
   subsets is unchanged if the sequence of distances is multiplied by a positive scale factor.

-/

open set filter metric measure_theory
open_locale nnreal ennreal topological_space

variables {α : Type*} [metric_space α] [proper_space α] [measurable_space α] [borel_space α]
variables (μ : measure α) [is_locally_finite_measure μ] [is_doubling_measure μ]

/-- This is really an auxiliary result en route to `blimsup_cthickening_mul_ae_eq`.

NB: The `set : α` type ascription is present because of issue #16932 on GitHub. -/
lemma blimsup_cthickening_ae_le_of_eventually_mul_le
  (p : ℕ → Prop) {s : ℕ → set α} (hs : ∀ i, is_compact (s i)) {M : ℝ} (hM : 0 < M)
  {r₁ r₂ : ℕ → ℝ} (hr : tendsto r₁ at_top (𝓝[>] 0)) (hMr : ∀ᶠ i in at_top, M * r₁ i ≤ r₂ i) :
  (blimsup (λ i, cthickening (r₁ i) (s i)) at_top p : set α) ≤ᵐ[μ]
  (blimsup (λ i, cthickening (r₂ i) (s i)) at_top p : set α) :=
begin
  /- Sketch of proof:

  Assume that `p` is identically true for simplicity. We may also assume that `M < 1` and `0 ≤ r₁`.
  Let `Y₁ i = cthickening (r₁ i) (s i)`, define `Y₂` similarly except using `r₂`, and let
  `(Z i) = ⋃_{j ≥ i} (Y₂ j)`. Our goal is equivalent to showing that `μ ((limsup Y₁) \ (Z i)) = 0`
  for all `i`.

  Assume for contradiction that `μ ((limsup Y₁) \ (Z i)) ≠ 0` for some `i` and let
  `W = (limsup Y₁) \ (Z i)`. Apply Lebesgue's density theorem to obtain a point `d` in `W` of
  positive density. Since `d ∈ limsup Y₁`, there is a subsequence of `j ↦ Y₁ j`, indexed by
  `f 0 < f 1 < ...`, such that `d ∈ Y₁ (f j)` for all `j`. For each `j`, we may thus choose
  `w j ∈ s (f j)` such that `d ∈ B j`, where `B j = closed_ball (w j) (r₁ (f j))`. Note that
  since `d` has positive density `μ (W ∩ (B j)) / μ (B j) → 1`.

  We obtain our contradiction by showing that there exists `η < 1` such that
  `μ (W ∩ (B j)) / μ (B j) ≤ η` for sufficiently large `j`. In fact we claim that `η = 1 - C⁻¹`
  is such a value where `C` is the scaling constant of `M⁻¹` for the doubling measure `μ`.

  To prove the claim, let `b j = closed_ball (w j) (M * r₁ (f j))` and for given `j` consider the
  sets `b j` and `W ∩ (B j)`. These are both subsets of `B j` and are disjoint for large enough `j`
  since `M * r₁ j ≤ r₂ j` and thus `b j ⊆ Z i ⊆ Wᶜ`. We thus have:
  `μ (b j) + μ (W ∩ (B j)) ≤ μ (B j)`. Combining this with `μ (B j) ≤ C * μ (b j)` we obtain
  the required inequality. -/
  suffices : ∀ {r₁ r₂ : ℕ → ℝ} (hr : tendsto r₁ at_top (𝓝[>] 0)) (hrp : 0 ≤ r₁)
    {M : ℝ} (hM : 0 < M) (hM' : M < 1) (hMr : ∀ᶠ i in at_top, M * r₁ i ≤ r₂ i),
    (blimsup (λ i, cthickening (r₁ i) (s i)) at_top p : set α) ≤ᵐ[μ]
    (blimsup (λ i, cthickening (r₂ i) (s i)) at_top p : set α),
  { let R₁ := λ i, max 0 (r₁ i),
    let R₂ := λ i, max 0 (r₂ i),
    have hRp : 0 ≤ R₁ := λ i, le_max_left 0 (r₁ i),
    replace hMr : ∀ᶠ i in at_top, M * R₁ i ≤ R₂ i,
    { refine hMr.mono (λ i hi, _),
      rw [mul_max_of_nonneg _ _ hM.le, mul_zero],
      exact max_le_max (le_refl 0) hi, },
    simp_rw [← cthickening_max_zero (r₁ _), ← cthickening_max_zero (r₂ _)],
    cases le_or_lt 1 M with hM' hM',
    { apply has_subset.subset.eventually_le,
      change _ ≤ _,
      refine mono_blimsup' (hMr.mono $ λ i hi, cthickening_mono _ (s i)),
      exact (le_mul_of_one_le_left (hRp i) hM').trans hi, },
    { exact this (tendsto_nhds_max_right hr) hRp hM hM' hMr, }, },
  clear hr hMr r₁ r₂ hM M,
  intros,
  set Y₁ : ℕ → set α := λ i, cthickening (r₁ i) (s i),
  set Y₂ : ℕ → set α := λ i, cthickening (r₂ i) (s i),
  let Z : ℕ → set α := λ i, ⋃ j (h : p j ∧ i ≤ j), Y₂ j,
  suffices : ∀ i, μ (at_top.blimsup Y₁ p \ Z i) = 0,
  { rwa [ae_le_set, @blimsup_eq_infi_bsupr_of_nat _ _ _ Y₂, infi_eq_Inter, diff_Inter,
      measure_Union_null_iff], },
  intros,
  set W := at_top.blimsup Y₁ p \ Z i,
  by_contra contra,
  obtain ⟨d, hd, hd'⟩ : ∃ d, d ∈ W ∧ ∀ {ι : Type*} {l : filter ι} (w : ι → α) (δ : ι → ℝ),
    tendsto δ l (𝓝[>] 0) → (∀ᶠ j in l, d ∈ closed_ball (w j) (1 * δ j)) →
    tendsto (λ j, μ (W ∩ closed_ball (w j) (δ j)) / μ (closed_ball (w j) (δ j))) l (𝓝 1) :=
    measure.exists_mem_of_measure_ne_zero_of_ae contra
      (is_doubling_measure.ae_tendsto_measure_inter_div μ W 1),
  replace hd : d ∈ blimsup Y₁ at_top p := ((mem_diff _).mp hd).1,
  obtain ⟨f : ℕ → ℕ, hf⟩ := exists_forall_mem_of_has_basis_mem_blimsup' at_top_basis hd,
  simp only [forall_and_distrib] at hf,
  obtain ⟨hf₀ : ∀ j, d ∈ cthickening (r₁ (f j)) (s (f j)), hf₁, hf₂ : ∀ j, j ≤ f j⟩ := hf,
  have hf₃ : tendsto f at_top at_top :=
    tendsto_at_top_at_top.mpr (λ j, ⟨f j, λ i hi, (hf₂ j).trans (hi.trans $ hf₂ i)⟩),
  replace hr : tendsto (r₁ ∘ f) at_top (𝓝[>] 0) := hr.comp hf₃,
  replace hMr : ∀ᶠ j in at_top, M * r₁ (f j) ≤ r₂ (f j) := hf₃.eventually hMr,
  replace hf₀ : ∀ j, ∃ (w ∈ s (f j)), d ∈ closed_ball w (r₁ (f j)) := λ j,
    by simpa only [(hs (f j)).cthickening_eq_bUnion_closed_ball (hrp (f j)), mem_Union] using hf₀ j,
  choose w hw hw' using hf₀,
  let C := is_doubling_measure.scaling_constant_of μ M⁻¹,
  have hC : 0 < C :=
    lt_of_lt_of_le zero_lt_one (is_doubling_measure.one_le_scaling_constant_of μ M⁻¹),
  suffices : ∃ (η < (1 : ℝ≥0)), ∀ᶠ j in at_top,
    μ (W ∩ closed_ball (w j) (r₁ (f j))) / μ (closed_ball (w j) (r₁ (f j))) ≤ η,
  { obtain ⟨η, hη, hη'⟩ := this,
    replace hη' : 1 ≤ η := by simpa only [ennreal.one_le_coe_iff] using
      le_of_tendsto (hd' w (λ j, r₁ (f j)) hr $ eventually_of_forall (by simpa only [one_mul])) hη',
    exact (lt_self_iff_false _).mp (lt_of_lt_of_le hη hη'), },
  refine ⟨1 - C⁻¹, tsub_lt_self zero_lt_one (nnreal.inv_pos.mpr hC), _⟩,
  replace hC : C ≠ 0 := ne_of_gt hC,
  let b : ℕ → set α := λ j, closed_ball (w j) (M * r₁ (f j)),
  let B : ℕ → set α := λ j, closed_ball (w j) (r₁ (f j)),
  have h₁ : ∀ j, b j ⊆ B j :=
    λ j, closed_ball_subset_closed_ball (mul_le_of_le_one_left (hrp (f j)) hM'.le),
  have h₂ : ∀ j, W ∩ B j ⊆ B j := λ j, inter_subset_right W (B j),
  have h₃ : ∀ᶠ j in at_top, disjoint (b j) (W ∩ B j),
  { apply hMr.mp,
    rw eventually_at_top,
    refine ⟨i, λ j hj hj', disjoint.inf_right (B j) $ disjoint.inf_right' (blimsup Y₁ at_top p) _⟩,
    change disjoint (b j) (Z i)ᶜ,
    rw disjoint_compl_right_iff_subset,
    refine (closed_ball_subset_cthickening (hw j) (M * r₁ (f j))).trans
      ((cthickening_mono hj' _).trans (λ a ha, _)),
    simp only [mem_Union, exists_prop],
    exact ⟨f j, ⟨hf₁ j, hj.le.trans (hf₂ j)⟩, ha⟩, },
  have h₄ : ∀ᶠ j in at_top, μ (B j) ≤ C * μ (b j) :=
    (hr.eventually (is_doubling_measure.eventually_measure_le_scaling_constant_mul'
      μ M hM)).mono (λ j hj, hj (w j)),
  refine (h₃.and h₄).mono (λ j hj₀, ennreal.div_le_of_le_mul _),
  change μ (W ∩ B j) ≤ ↑(1 - C⁻¹) * μ (B j),
  have hB : μ (B j) ≠ ∞ := measure_closed_ball_lt_top.ne,
  rw [with_top.coe_sub, ennreal.coe_one, ennreal.sub_mul (λ _ _, hB), one_mul],
  replace hB : ↑C⁻¹ * μ (B j) ≠ ∞,
  { refine ennreal.mul_ne_top _ hB,
    rwa [ennreal.coe_inv hC, ne.def, ennreal.inv_eq_top, ennreal.coe_eq_zero], },
  obtain ⟨hj₁ : disjoint (b j) (W ∩ B j), hj₂ : μ (B j) ≤ C * μ (b j)⟩ := hj₀,
  replace hj₂ : ↑C⁻¹ * μ (B j) ≤ μ (b j),
  { rw [ennreal.coe_inv hC, ← ennreal.div_eq_inv_mul],
    exact ennreal.div_le_of_le_mul' hj₂, },
  have hj₃ : ↑C⁻¹ * μ (B j) + μ (W ∩ B j) ≤ μ (B j),
  { refine le_trans (add_le_add_right hj₂ _) _,
    rw ← measure_union' hj₁ measurable_set_closed_ball,
    exact measure_mono (union_subset (h₁ j) (h₂ j)), },
  replace hj₃ := tsub_le_tsub_right hj₃ (↑C⁻¹ * μ (B j)),
  rwa ennreal.add_sub_cancel_left hB at hj₃,
end

/-- This lemma is a generalisation of Lemma 9 appearing on page 217 of
[J.W.S. Cassels, *Some metrical theorems in Diophantine approximation. I*](cassels1950).

NB: The `set : α` type ascription is present because of issue #16932 on GitHub. -/
lemma blimsup_cthickening_mul_ae_eq
  (p : ℕ → Prop) (s : ℕ → set α) (hs : ∀ i, is_compact (s i)) {M : ℝ} (hM : 0 < M)
  (r : ℕ → ℝ) (hr : tendsto r at_top (𝓝 0)) :
  (blimsup (λ i, cthickening (M * r i) (s i)) at_top p : set α) =ᵐ[μ]
  (blimsup (λ i, cthickening (r i) (s i)) at_top p : set α) :=
begin
  have : ∀ (p : ℕ → Prop) {r : ℕ → ℝ} (hr : tendsto r at_top (𝓝[>] 0)),
    (blimsup (λ i, cthickening (M * r i) (s i)) at_top p : set α) =ᵐ[μ]
    (blimsup (λ i, cthickening (r i) (s i)) at_top p : set α),
  { clear p hr r, intros p r hr,
    have hr' : tendsto (λ i, M * r i) at_top (𝓝[>] 0),
    { convert tendsto_nhds_within_Ioi.const_mul hM hr; simp only [mul_zero], },
    refine eventually_le_antisymm_iff.mpr ⟨_, _⟩,
    { exact blimsup_cthickening_ae_le_of_eventually_mul_le μ p hs (inv_pos.mpr hM) hr'
        (eventually_of_forall $ λ i, by rw inv_mul_cancel_left₀ hM.ne' (r i)), },
    { exact blimsup_cthickening_ae_le_of_eventually_mul_le μ p hs hM hr
        (eventually_of_forall $ λ i, le_refl _), }, },
  let r' : ℕ → ℝ := λ i, if 0 < r i then r i else 1/((i : ℝ) + 1),
  have hr' : tendsto r' at_top (𝓝[>] 0),
  { refine tendsto_nhds_within_iff.mpr ⟨tendsto.if' hr tendsto_one_div_add_at_top_nhds_0_nat,
      eventually_of_forall $ λ i, _⟩,
    by_cases hi : 0 < r i,
    { simp [hi, r'], },
    { simp only [hi, r', one_div, mem_Ioi, if_false, inv_pos], positivity, }, },
  have h₀ : ∀ i, (p i ∧ 0 < r i) → cthickening (r i) (s i) = cthickening (r' i) (s i),
  { rintros i ⟨-, hi⟩, congr, change r i = ite (0 < r i) (r i) _, simp [hi], },
  have h₁ : ∀ i, (p i ∧ 0 < r i) → cthickening (M * r i) (s i) = cthickening (M * r' i) (s i),
  { rintros i ⟨-, hi⟩, simp only [hi, mul_ite, if_true], },
  have h₂ : ∀ i, (p i ∧ r i ≤ 0) → cthickening (M * r i) (s i) = cthickening (r i) (s i),
  { rintros i ⟨-, hi⟩,
    have hi' : M * r i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM.le hi,
    rw [cthickening_of_nonpos hi, cthickening_of_nonpos hi'], },
  have hp : p = λ i, (p i ∧ 0 < r i) ∨ (p i ∧ r i ≤ 0),
  { ext i, simp [← and_or_distrib_left, lt_or_le 0 (r i)], },
  rw [hp, blimsup_or_eq_sup, blimsup_or_eq_sup, sup_eq_union,
    blimsup_congr (eventually_of_forall h₀), blimsup_congr (eventually_of_forall h₁),
    blimsup_congr (eventually_of_forall h₂)],
  exact ae_eq_set_union (this (λ i, p i ∧ 0 < r i) hr') (ae_eq_refl _),
end

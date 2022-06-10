/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Yury G. Kudryashov, Patrick Massot
-/
import algebra.geom_sum
import order.filter.archimedean
import order.iterate
import topology.instances.ennreal

/-!
# A collection of specific limit computations

This file, by design, is independent of `normed_space` in the import hierarchy.  It contains
important specific limit computations in metric spaces, in ordered rings/fields, and in specific
instances of these such as `ℝ`, `ℝ≥0` and `ℝ≥0∞`.
-/

noncomputable theory
open classical set function filter finset metric

open_locale classical topological_space nat big_operators uniformity nnreal ennreal

variables {α : Type*} {β : Type*} {ι : Type*}

lemma tendsto_inverse_at_top_nhds_0_nat : tendsto (λ n : ℕ, (n : ℝ)⁻¹) at_top (𝓝 0) :=
tendsto_inv_at_top_zero.comp tendsto_coe_nat_at_top_at_top

lemma tendsto_const_div_at_top_nhds_0_nat (C : ℝ) : tendsto (λ n : ℕ, C / n) at_top (𝓝 0) :=
by simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_inverse_at_top_nhds_0_nat

lemma nnreal.tendsto_inverse_at_top_nhds_0_nat : tendsto (λ n : ℕ, (n : ℝ≥0)⁻¹) at_top (𝓝 0) :=
by { rw ← nnreal.tendsto_coe, convert tendsto_inverse_at_top_nhds_0_nat, simp }

lemma nnreal.tendsto_const_div_at_top_nhds_0_nat (C : ℝ≥0) :
  tendsto (λ n : ℕ, C / n) at_top (𝓝 0) :=
by simpa using tendsto_const_nhds.mul nnreal.tendsto_inverse_at_top_nhds_0_nat

lemma tendsto_one_div_add_at_top_nhds_0_nat :
  tendsto (λ n : ℕ, 1 / ((n : ℝ) + 1)) at_top (𝓝 0) :=
suffices tendsto (λ n : ℕ, 1 / (↑(n + 1) : ℝ)) at_top (𝓝 0), by simpa,
(tendsto_add_at_top_iff_nat 1).2 (tendsto_const_div_at_top_nhds_0_nat 1)

/-! ### Powers -/

lemma tendsto_add_one_pow_at_top_at_top_of_pos [linear_ordered_semiring α] [archimedean α] {r : α}
  (h : 0 < r) :
  tendsto (λ n:ℕ, (r + 1)^n) at_top at_top :=
tendsto_at_top_at_top_of_monotone' (λ n m, pow_le_pow (le_add_of_nonneg_left (le_of_lt h))) $
  not_bdd_above_iff.2 $ λ x, set.exists_range_iff.2 $ add_one_pow_unbounded_of_pos _ h

lemma tendsto_pow_at_top_at_top_of_one_lt [linear_ordered_ring α] [archimedean α]
  {r : α} (h : 1 < r) :
  tendsto (λn:ℕ, r ^ n) at_top at_top :=
sub_add_cancel r 1 ▸ tendsto_add_one_pow_at_top_at_top_of_pos (sub_pos.2 h)

lemma nat.tendsto_pow_at_top_at_top_of_one_lt {m : ℕ} (h : 1 < m) :
  tendsto (λn:ℕ, m ^ n) at_top at_top :=
tsub_add_cancel_of_le (le_of_lt h) ▸
  tendsto_add_one_pow_at_top_at_top_of_pos (tsub_pos_of_lt h)

lemma tendsto_pow_at_top_nhds_0_of_lt_1 {𝕜 : Type*} [linear_ordered_field 𝕜] [archimedean 𝕜]
  [topological_space 𝕜] [order_topology 𝕜] {r : 𝕜} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  tendsto (λn:ℕ, r^n) at_top (𝓝 0) :=
h₁.eq_or_lt.elim
  (assume : 0 = r,
    (tendsto_add_at_top_iff_nat 1).mp $ by simp [pow_succ, ← this, tendsto_const_nhds])
  (assume : 0 < r,
    have tendsto (λn, (r⁻¹ ^ n)⁻¹) at_top (𝓝 0),
      from tendsto_inv_at_top_zero.comp
        (tendsto_pow_at_top_at_top_of_one_lt $ one_lt_inv this h₂),
    this.congr (λ n, by simp))

lemma tendsto_pow_at_top_nhds_within_0_of_lt_1 {𝕜 : Type*} [linear_ordered_field 𝕜] [archimedean 𝕜]
  [topological_space 𝕜] [order_topology 𝕜] {r : 𝕜} (h₁ : 0 < r) (h₂ : r < 1) :
  tendsto (λn:ℕ, r^n) at_top (𝓝[>] 0) :=
tendsto_inf.2 ⟨tendsto_pow_at_top_nhds_0_of_lt_1 h₁.le h₂,
  tendsto_principal.2 $ eventually_of_forall $ λ n, pow_pos h₁ _⟩

lemma uniformity_basis_dist_pow_of_lt_1 {α : Type*} [pseudo_metric_space α]
  {r : ℝ} (h₀ : 0 < r) (h₁ : r < 1) :
  (𝓤 α).has_basis (λ k : ℕ, true) (λ k, {p : α × α | dist p.1 p.2 < r ^ k}) :=
metric.mk_uniformity_basis (λ i _, pow_pos h₀ _) $ λ ε ε0,
  (exists_pow_lt_of_lt_one ε0 h₁).imp $ λ k hk, ⟨trivial, hk.le⟩

lemma geom_lt {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n)
  (h : ∀ k < n, c * u k < u (k + 1)) :
  c ^ n * u 0 < u n :=
begin
  refine (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_le_of_lt hn _ _ h,
  { simp },
  { simp [pow_succ, mul_assoc, le_refl] }
end

lemma geom_le {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (h : ∀ k < n, c * u k ≤ u (k + 1)) :
  c ^ n * u 0 ≤ u n :=
by refine (monotone_mul_left_of_nonneg hc).seq_le_seq n _ _ h; simp [pow_succ, mul_assoc, le_refl]

lemma lt_geom {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n)
  (h : ∀ k < n, u (k + 1) < c * u k) :
  u n < c ^ n * u 0 :=
begin
  refine (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_lt_of_le hn _ h _,
  { simp },
  { simp [pow_succ, mul_assoc, le_refl] }
end

lemma le_geom {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (h : ∀ k < n, u (k + 1) ≤ c * u k) :
  u n ≤ (c ^ n) * u 0 :=
by refine (monotone_mul_left_of_nonneg hc).seq_le_seq n _ h _; simp [pow_succ, mul_assoc, le_refl]

/-- If a sequence `v` of real numbers satisfies `k * v n ≤ v (n+1)` with `1 < k`,
then it goes to +∞. -/
lemma tendsto_at_top_of_geom_le {v : ℕ → ℝ} {c : ℝ} (h₀ : 0 < v 0) (hc : 1 < c)
  (hu : ∀ n, c * v n ≤ v (n + 1)) : tendsto v at_top at_top :=
tendsto_at_top_mono (λ n, geom_le (zero_le_one.trans hc.le) n (λ k hk, hu k)) $
  (tendsto_pow_at_top_at_top_of_one_lt hc).at_top_mul_const h₀

lemma nnreal.tendsto_pow_at_top_nhds_0_of_lt_1 {r : ℝ≥0} (hr : r < 1) :
  tendsto (λ n:ℕ, r^n) at_top (𝓝 0) :=
nnreal.tendsto_coe.1 $ by simp only [nnreal.coe_pow, nnreal.coe_zero,
  tendsto_pow_at_top_nhds_0_of_lt_1 r.coe_nonneg hr]

lemma ennreal.tendsto_pow_at_top_nhds_0_of_lt_1 {r : ℝ≥0∞} (hr : r < 1) :
  tendsto (λ n:ℕ, r^n) at_top (𝓝 0) :=
begin
  rcases ennreal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩,
  rw [← ennreal.coe_zero],
  norm_cast at *,
  apply nnreal.tendsto_pow_at_top_nhds_0_of_lt_1 hr
end

/-! ### Geometric series-/
section geometric

lemma has_sum_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  has_sum (λn:ℕ, r ^ n) (1 - r)⁻¹ :=
have r ≠ 1, from ne_of_lt h₂,
have tendsto (λn, (r ^ n - 1) * (r - 1)⁻¹) at_top (𝓝 ((0 - 1) * (r - 1)⁻¹)),
  from ((tendsto_pow_at_top_nhds_0_of_lt_1 h₁ h₂).sub tendsto_const_nhds).mul tendsto_const_nhds,
(has_sum_iff_tendsto_nat_of_nonneg (pow_nonneg h₁) _).mpr $
  by simp [neg_inv, geom_sum_eq, div_eq_mul_inv, *] at *

lemma summable_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : summable (λn:ℕ, r ^ n) :=
⟨_, has_sum_geometric_of_lt_1 h₁ h₂⟩

lemma tsum_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : ∑'n:ℕ, r ^ n = (1 - r)⁻¹ :=
(has_sum_geometric_of_lt_1 h₁ h₂).tsum_eq

lemma has_sum_geometric_two : has_sum (λn:ℕ, ((1:ℝ)/2) ^ n) 2 :=
by convert has_sum_geometric_of_lt_1 _ _; norm_num

lemma summable_geometric_two : summable (λn:ℕ, ((1:ℝ)/2) ^ n) :=
⟨_, has_sum_geometric_two⟩

lemma summable_geometric_two_encode {ι : Type*} [encodable ι] :
  summable (λ (i : ι), (1/2 : ℝ)^(encodable.encode i)) :=
summable_geometric_two.comp_injective encodable.encode_injective

lemma tsum_geometric_two : ∑'n:ℕ, ((1:ℝ)/2) ^ n = 2 :=
has_sum_geometric_two.tsum_eq

lemma sum_geometric_two_le (n : ℕ) : ∑ (i : ℕ) in range n, (1 / (2 : ℝ)) ^ i ≤ 2 :=
begin
  have : ∀ i, 0 ≤ (1 / (2 : ℝ)) ^ i,
  { intro i, apply pow_nonneg, norm_num },
  convert sum_le_tsum (range n) (λ i _, this i) summable_geometric_two,
  exact tsum_geometric_two.symm
end

lemma tsum_geometric_inv_two : ∑' n : ℕ, (2 : ℝ)⁻¹ ^ n = 2 :=
(inv_eq_one_div (2 : ℝ)).symm ▸ tsum_geometric_two

/-- The sum of `2⁻¹ ^ i` for `n ≤ i` equals `2 * 2⁻¹ ^ n`. -/
lemma tsum_geometric_inv_two_ge (n : ℕ) :
  ∑' i, ite (n ≤ i) ((2 : ℝ)⁻¹ ^ i) 0 = 2 * 2⁻¹ ^ n :=
begin
  have A : summable (λ (i : ℕ), ite (n ≤ i) ((2⁻¹ : ℝ) ^ i) 0),
  { apply summable_of_nonneg_of_le _ _ summable_geometric_two;
    { intro i, by_cases hi : n ≤ i; simp [hi] } },
  have B : (finset.range n).sum (λ (i : ℕ), ite (n ≤ i) ((2⁻¹ : ℝ)^i) 0) = 0 :=
    finset.sum_eq_zero (λ i hi, ite_eq_right_iff.2 $ λ h,
      (lt_irrefl _ ((finset.mem_range.1 hi).trans_le h)).elim),
  simp only [← sum_add_tsum_nat_add n A, B, if_true, zero_add, zero_le',
    le_add_iff_nonneg_left, pow_add, tsum_mul_right, tsum_geometric_inv_two],
end

lemma has_sum_geometric_two' (a : ℝ) : has_sum (λn:ℕ, (a / 2) / 2 ^ n) a :=
begin
  convert has_sum.mul_left (a / 2) (has_sum_geometric_of_lt_1
    (le_of_lt one_half_pos) one_half_lt_one),
  { funext n, simp, refl, },
  { norm_num }
end

lemma summable_geometric_two' (a : ℝ) : summable (λ n:ℕ, (a / 2) / 2 ^ n) :=
⟨a, has_sum_geometric_two' a⟩

lemma tsum_geometric_two' (a : ℝ) : ∑' n:ℕ, (a / 2) / 2^n = a :=
(has_sum_geometric_two' a).tsum_eq

/-- **Sum of a Geometric Series** -/
lemma nnreal.has_sum_geometric {r : ℝ≥0} (hr : r < 1) :
  has_sum (λ n : ℕ, r ^ n) (1 - r)⁻¹ :=
begin
  apply nnreal.has_sum_coe.1,
  push_cast,
  rw [nnreal.coe_sub (le_of_lt hr)],
  exact has_sum_geometric_of_lt_1 r.coe_nonneg hr
end

lemma nnreal.summable_geometric {r : ℝ≥0} (hr : r < 1) : summable (λn:ℕ, r ^ n) :=
⟨_, nnreal.has_sum_geometric hr⟩

lemma tsum_geometric_nnreal {r : ℝ≥0} (hr : r < 1) : ∑'n:ℕ, r ^ n = (1 - r)⁻¹ :=
(nnreal.has_sum_geometric hr).tsum_eq

/-- The series `pow r` converges to `(1-r)⁻¹`. For `r < 1` the RHS is a finite number,
and for `1 ≤ r` the RHS equals `∞`. -/
@[simp] lemma ennreal.tsum_geometric (r : ℝ≥0∞) : ∑'n:ℕ, r ^ n = (1 - r)⁻¹ :=
begin
  cases lt_or_le r 1 with hr hr,
  { rcases ennreal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩,
    norm_cast at *,
    convert ennreal.tsum_coe_eq (nnreal.has_sum_geometric hr),
    rw [ennreal.coe_inv $ ne_of_gt $ tsub_pos_iff_lt.2 hr] },
  { rw [tsub_eq_zero_iff_le.mpr hr, ennreal.inv_zero, ennreal.tsum_eq_supr_nat, supr_eq_top],
    refine λ a ha, (ennreal.exists_nat_gt (lt_top_iff_ne_top.1 ha)).imp
      (λ n hn, lt_of_lt_of_le hn _),
    calc (n:ℝ≥0∞) = ∑ i in range n, 1     : by rw [sum_const, nsmul_one, card_range]
              ... ≤ ∑ i in range n, r ^ i : sum_le_sum (λ k _, one_le_pow_of_one_le' hr k) }
end

end geometric

/-!
### Sequences with geometrically decaying distance in metric spaces

In this paragraph, we discuss sequences in metric spaces or emetric spaces for which the distance
between two consecutive terms decays geometrically. We show that such sequences are Cauchy
sequences, and bound their distances to the limit. We also discuss series with geometrically
decaying terms.
-/
section edist_le_geometric

variables [pseudo_emetric_space α] (r C : ℝ≥0∞) (hr : r < 1) (hC : C ≠ ⊤) {f : ℕ → α}
  (hu : ∀n, edist (f n) (f (n+1)) ≤ C * r^n)

include hr hC hu

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, `C ≠ ∞`, `r < 1`,
then `f` is a Cauchy sequence.-/
lemma cauchy_seq_of_edist_le_geometric : cauchy_seq f :=
begin
  refine cauchy_seq_of_edist_le_of_tsum_ne_top _ hu _,
  rw [ennreal.tsum_mul_left, ennreal.tsum_geometric],
  refine ennreal.mul_ne_top hC (ennreal.inv_ne_top.2 _),
  exact (tsub_pos_iff_lt.2 hr).ne'
end

omit hr hC

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
lemma edist_le_of_edist_le_geometric_of_tendsto {a : α} (ha : tendsto f at_top (𝓝 a)) (n : ℕ) :
  edist (f n) a ≤ (C * r^n) / (1 - r) :=
begin
  convert edist_le_tsum_of_edist_le_of_tendsto _ hu ha _,
  simp only [pow_add, ennreal.tsum_mul_left, ennreal.tsum_geometric, div_eq_mul_inv, mul_assoc]
end

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
lemma edist_le_of_edist_le_geometric_of_tendsto₀ {a : α} (ha : tendsto f at_top (𝓝 a)) :
  edist (f 0) a ≤ C / (1 - r) :=
by simpa only [pow_zero, mul_one] using edist_le_of_edist_le_geometric_of_tendsto r C hu ha 0

end edist_le_geometric

section edist_le_geometric_two

variables [pseudo_emetric_space α] (C : ℝ≥0∞) (hC : C ≠ ⊤) {f : ℕ → α}
  (hu : ∀n, edist (f n) (f (n+1)) ≤ C / 2^n) {a : α} (ha : tendsto f at_top (𝓝 a))

include hC hu

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then `f` is a Cauchy sequence.-/
lemma cauchy_seq_of_edist_le_geometric_two : cauchy_seq f :=
begin
  simp only [div_eq_mul_inv, ennreal.inv_pow] at hu,
  refine cauchy_seq_of_edist_le_geometric 2⁻¹ C _ hC hu,
  simp [ennreal.one_lt_two]
end

omit hC
include ha

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f n` to the limit of `f` is bounded above by `2 * C * 2^-n`. -/
lemma edist_le_of_edist_le_geometric_two_of_tendsto (n : ℕ) :
  edist (f n) a ≤ 2 * C / 2^n :=
begin
  simp only [div_eq_mul_inv, ennreal.inv_pow] at *,
  rw [mul_assoc, mul_comm],
  convert edist_le_of_edist_le_geometric_of_tendsto 2⁻¹ C hu ha n,
  rw [ennreal.one_sub_inv_two, inv_inv]
end

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f 0` to the limit of `f` is bounded above by `2 * C`. -/
lemma edist_le_of_edist_le_geometric_two_of_tendsto₀: edist (f 0) a ≤ 2 * C :=
by simpa only [pow_zero, div_eq_mul_inv, ennreal.inv_one, mul_one]
  using edist_le_of_edist_le_geometric_two_of_tendsto C hu ha 0

end edist_le_geometric_two

section le_geometric

variables [pseudo_metric_space α] {r C : ℝ} (hr : r < 1) {f : ℕ → α}
  (hu : ∀n, dist (f n) (f (n+1)) ≤ C * r^n)

include hr hu

lemma aux_has_sum_of_le_geometric : has_sum (λ n : ℕ, C * r^n) (C / (1 - r)) :=
begin
  rcases sign_cases_of_C_mul_pow_nonneg (λ n, dist_nonneg.trans (hu n)) with rfl | ⟨C₀, r₀⟩,
  { simp [has_sum_zero] },
  { refine has_sum.mul_left C _,
    simpa using has_sum_geometric_of_lt_1 r₀ hr }
end

variables (r C)

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then `f` is a Cauchy sequence.
Note that this lemma does not assume `0 ≤ C` or `0 ≤ r`. -/
lemma cauchy_seq_of_le_geometric : cauchy_seq f :=
cauchy_seq_of_dist_le_of_summable _ hu ⟨_, aux_has_sum_of_le_geometric hr hu⟩

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
lemma dist_le_of_le_geometric_of_tendsto₀ {a : α} (ha : tendsto f at_top (𝓝 a)) :
  dist (f 0) a ≤ C / (1 - r) :=
(aux_has_sum_of_le_geometric hr hu).tsum_eq ▸
  dist_le_tsum_of_dist_le_of_tendsto₀ _ hu ⟨_, aux_has_sum_of_le_geometric hr hu⟩ ha

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
lemma dist_le_of_le_geometric_of_tendsto {a : α} (ha : tendsto f at_top (𝓝 a)) (n : ℕ) :
  dist (f n) a ≤ (C * r^n) / (1 - r) :=
begin
  have := aux_has_sum_of_le_geometric hr hu,
  convert dist_le_tsum_of_dist_le_of_tendsto _ hu ⟨_, this⟩ ha n,
  simp only [pow_add, mul_left_comm C, mul_div_right_comm],
  rw [mul_comm],
  exact (this.mul_left _).tsum_eq.symm
end

omit hr hu

variable (hu₂ : ∀ n, dist (f n) (f (n+1)) ≤ (C / 2) / 2^n)

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then `f` is a Cauchy sequence. -/
lemma cauchy_seq_of_le_geometric_two : cauchy_seq f :=
cauchy_seq_of_dist_le_of_summable _ hu₂ $ ⟨_, has_sum_geometric_two' C⟩

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C`. -/
lemma dist_le_of_le_geometric_two_of_tendsto₀ {a : α} (ha : tendsto f at_top (𝓝 a)) :
  dist (f 0) a ≤ C :=
(tsum_geometric_two' C) ▸ dist_le_tsum_of_dist_le_of_tendsto₀ _ hu₂ (summable_geometric_two' C) ha

include hu₂

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C / 2^n`. -/
lemma dist_le_of_le_geometric_two_of_tendsto {a : α} (ha : tendsto f at_top (𝓝 a)) (n : ℕ) :
  dist (f n) a ≤ C / 2^n :=
begin
  convert dist_le_tsum_of_dist_le_of_tendsto _ hu₂ (summable_geometric_two' C) ha n,
  simp only [add_comm n, pow_add, ← div_div],
  symmetry,
  exact ((has_sum_geometric_two' C).div_const _).tsum_eq
end

end le_geometric

/-! ### Summability tests based on comparison with geometric series -/

/-- A series whose terms are bounded by the terms of a converging geometric series converges. -/
lemma summable_one_div_pow_of_le {m : ℝ} {f : ℕ → ℕ} (hm : 1 < m) (fi : ∀ i, i ≤ f i) :
  summable (λ i, 1 / m ^ f i) :=
begin
  refine summable_of_nonneg_of_le
    (λ a, one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _)) (λ a, _)
    (summable_geometric_of_lt_1 (one_div_nonneg.mpr (zero_le_one.trans hm.le))
      ((one_div_lt (zero_lt_one.trans hm) zero_lt_one).mpr (one_div_one.le.trans_lt hm))),
  rw [div_pow, one_pow],
  refine (one_div_le_one_div _ _).mpr (pow_le_pow hm.le (fi a));
  exact pow_pos (zero_lt_one.trans hm) _
end

/-! ### Positive sequences with small sums on encodable types -/

/-- For any positive `ε`, define on an encodable type a positive sequence with sum less than `ε` -/
def pos_sum_of_encodable {ε : ℝ} (hε : 0 < ε)
  (ι) [encodable ι] : {ε' : ι → ℝ // (∀ i, 0 < ε' i) ∧ ∃ c, has_sum ε' c ∧ c ≤ ε} :=
begin
  let f := λ n, (ε / 2) / 2 ^ n,
  have hf : has_sum f ε := has_sum_geometric_two' _,
  have f0 : ∀ n, 0 < f n := λ n, div_pos (half_pos hε) (pow_pos zero_lt_two _),
  refine ⟨f ∘ encodable.encode, λ i, f0 _, _⟩,
  rcases hf.summable.comp_injective (@encodable.encode_injective ι _) with ⟨c, hg⟩,
  refine ⟨c, hg, has_sum_le_inj _ (@encodable.encode_injective ι _) _ _ hg hf⟩,
  { assume i _, exact le_of_lt (f0 _) },
  { assume n, exact le_rfl }
end

lemma set.countable.exists_pos_has_sum_le {ι : Type*} {s : set ι} (hs : s.countable)
  {ε : ℝ} (hε : 0 < ε) :
  ∃ ε' : ι → ℝ, (∀ i, 0 < ε' i) ∧ ∃ c, has_sum (λ i : s, ε' i) c ∧ c ≤ ε :=
begin
  haveI := hs.to_encodable,
  rcases pos_sum_of_encodable hε s with ⟨f, hf0, ⟨c, hfc, hcε⟩⟩,
  refine ⟨λ i, if h : i ∈ s then f ⟨i, h⟩ else 1, λ i, _, ⟨c, _, hcε⟩⟩,
  { split_ifs, exacts [hf0 _, zero_lt_one] },
  { simpa only [subtype.coe_prop, dif_pos, subtype.coe_eta] }
end

lemma set.countable.exists_pos_forall_sum_le {ι : Type*} {s : set ι} (hs : s.countable)
  {ε : ℝ} (hε : 0 < ε) :
  ∃ ε' : ι → ℝ, (∀ i, 0 < ε' i) ∧ ∀ t : finset ι, ↑t ⊆ s → ∑ i in t, ε' i ≤ ε :=
begin
  rcases hs.exists_pos_has_sum_le hε with ⟨ε', hpos, c, hε'c, hcε⟩,
  refine ⟨ε', hpos, λ t ht, _⟩,
  rw [← sum_subtype_of_mem _ ht],
  refine (sum_le_has_sum _ _ hε'c).trans hcε,
  exact λ _ _, (hpos _).le
end

namespace nnreal

theorem exists_pos_sum_of_encodable {ε : ℝ≥0} (hε : ε ≠ 0) (ι) [encodable ι] :
  ∃ ε' : ι → ℝ≥0, (∀ i, 0 < ε' i) ∧ ∃c, has_sum ε' c ∧ c < ε :=
let ⟨a, a0, aε⟩ := exists_between (pos_iff_ne_zero.2 hε) in
let ⟨ε', hε', c, hc, hcε⟩ := pos_sum_of_encodable a0 ι in
⟨ λi, ⟨ε' i, le_of_lt $ hε' i⟩, assume i, nnreal.coe_lt_coe.1 $ hε' i,
  ⟨c, has_sum_le (assume i, le_of_lt $ hε' i) has_sum_zero hc ⟩, nnreal.has_sum_coe.1 hc,
   lt_of_le_of_lt (nnreal.coe_le_coe.1 hcε) aε ⟩

end nnreal

namespace ennreal

theorem exists_pos_sum_of_encodable {ε : ℝ≥0∞} (hε : ε ≠ 0) (ι) [encodable ι] :
  ∃ ε' : ι → ℝ≥0, (∀ i, 0 < ε' i) ∧ ∑' i, (ε' i : ℝ≥0∞) < ε :=
begin
  rcases exists_between (pos_iff_ne_zero.2 hε) with ⟨r, h0r, hrε⟩,
  rcases lt_iff_exists_coe.1 hrε with ⟨x, rfl, hx⟩,
  rcases nnreal.exists_pos_sum_of_encodable (coe_pos.1 h0r).ne' ι with ⟨ε', hp, c, hc, hcr⟩,
  exact ⟨ε', hp, (ennreal.tsum_coe_eq hc).symm ▸ lt_trans (coe_lt_coe.2 hcr) hrε⟩
end

theorem exists_pos_sum_of_encodable' {ε : ℝ≥0∞} (hε : ε ≠ 0) (ι) [encodable ι] :
  ∃ ε' : ι → ℝ≥0∞, (∀ i, 0 < ε' i) ∧ (∑' i, ε' i) < ε :=
let ⟨δ, δpos, hδ⟩ := exists_pos_sum_of_encodable hε ι in
  ⟨λ i, δ i, λ i, ennreal.coe_pos.2 (δpos i), hδ⟩

theorem exists_pos_tsum_mul_lt_of_encodable {ε : ℝ≥0∞} (hε : ε ≠ 0) {ι} [encodable ι]
  (w : ι → ℝ≥0∞) (hw : ∀ i, w i ≠ ∞) :
  ∃ δ : ι → ℝ≥0, (∀ i, 0 < δ i) ∧ ∑' i, (w i * δ i : ℝ≥0∞) < ε :=
begin
  lift w to ι → ℝ≥0 using hw,
  rcases exists_pos_sum_of_encodable hε ι with ⟨δ', Hpos, Hsum⟩,
  have : ∀ i, 0 < max 1 (w i), from λ i, zero_lt_one.trans_le (le_max_left _ _),
  refine ⟨λ i, δ' i / max 1 (w i), λ i, nnreal.div_pos (Hpos _) (this i), _⟩,
  refine lt_of_le_of_lt (ennreal.tsum_le_tsum $ λ i, _) Hsum,
  rw [coe_div (this i).ne'],
  refine mul_le_of_le_div' (ennreal.mul_le_mul le_rfl $ ennreal.inv_le_inv.2 _),
  exact coe_le_coe.2 (le_max_right _ _)
end

end ennreal

/-!
### Factorial
-/

lemma factorial_tendsto_at_top : tendsto nat.factorial at_top at_top :=
tendsto_at_top_at_top_of_monotone nat.monotone_factorial (λ n, ⟨n, n.self_le_factorial⟩)

lemma tendsto_factorial_div_pow_self_at_top : tendsto (λ n, n! / n^n : ℕ → ℝ) at_top (𝓝 0) :=
tendsto_of_tendsto_of_tendsto_of_le_of_le'
  tendsto_const_nhds
  (tendsto_const_div_at_top_nhds_0_nat 1)
  (eventually_of_forall $ λ n, div_nonneg (by exact_mod_cast n.factorial_pos.le)
    (pow_nonneg (by exact_mod_cast n.zero_le) _))
  begin
    refine (eventually_gt_at_top 0).mono (λ n hn, _),
    rcases nat.exists_eq_succ_of_ne_zero hn.ne.symm with ⟨k, rfl⟩,
    rw [← prod_range_add_one_eq_factorial, pow_eq_prod_const, div_eq_mul_inv, ← inv_eq_one_div,
      prod_nat_cast, nat.cast_succ, ← prod_inv_distrib', ← prod_mul_distrib,
      finset.prod_range_succ'],
    simp only [prod_range_succ', one_mul, nat.cast_add, zero_add, nat.cast_one],
    refine mul_le_of_le_one_left (inv_nonneg.mpr $ by exact_mod_cast hn.le) (prod_le_one _ _);
      intros x hx; rw finset.mem_range at hx,
    { refine mul_nonneg _ (inv_nonneg.mpr _); norm_cast; linarith },
    { refine (div_le_one $ by exact_mod_cast hn).mpr _, norm_cast, linarith }
  end

/-!
### Ceil and floor
-/

section

lemma tendsto_nat_floor_at_top {α : Type*} [linear_ordered_semiring α] [floor_semiring α] :
  tendsto (λ (x : α), ⌊x⌋₊) at_top at_top :=
nat.floor_mono.tendsto_at_top_at_top (λ x, ⟨max 0 (x + 1), by simp [nat.le_floor_iff]⟩)

variables {R : Type*} [topological_space R] [linear_ordered_field R] [order_topology R]
[floor_ring R]

lemma tendsto_nat_floor_mul_div_at_top {a : R} (ha : 0 ≤ a) :
  tendsto (λ x, (⌊a * x⌋₊ : R) / x) at_top (𝓝 a) :=
begin
  have A : tendsto (λ (x : R), a - x⁻¹) at_top (𝓝 (a - 0)) :=
    tendsto_const_nhds.sub tendsto_inv_at_top_zero,
  rw sub_zero at A,
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' A tendsto_const_nhds,
  { refine eventually_at_top.2 ⟨1, λ x hx, _⟩,
    simp only [le_div_iff (zero_lt_one.trans_le hx), sub_mul,
      inv_mul_cancel (zero_lt_one.trans_le hx).ne'],
    have := nat.lt_floor_add_one (a * x),
    linarith },
  { refine eventually_at_top.2 ⟨1, λ x hx, _⟩,
    rw div_le_iff (zero_lt_one.trans_le hx),
    simp [nat.floor_le (mul_nonneg ha (zero_le_one.trans hx))] }
end

lemma tendsto_nat_floor_div_at_top :
  tendsto (λ x, (⌊x⌋₊ : R) / x) at_top (𝓝 1) :=
by simpa using tendsto_nat_floor_mul_div_at_top (@zero_le_one R _)

lemma tendsto_nat_ceil_mul_div_at_top {a : R} (ha : 0 ≤ a) :
  tendsto (λ x, (⌈a * x⌉₊ : R) / x) at_top (𝓝 a) :=
begin
  have A : tendsto (λ (x : R), a + x⁻¹) at_top (𝓝 (a + 0)) :=
    tendsto_const_nhds.add tendsto_inv_at_top_zero,
  rw add_zero at A,
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds A,
  { refine eventually_at_top.2 ⟨1, λ x hx, _⟩,
    rw le_div_iff (zero_lt_one.trans_le hx),
    exact nat.le_ceil _ },
  { refine eventually_at_top.2 ⟨1, λ x hx, _⟩,
    simp [div_le_iff (zero_lt_one.trans_le hx), inv_mul_cancel (zero_lt_one.trans_le hx).ne',
      (nat.ceil_lt_add_one ((mul_nonneg ha (zero_le_one.trans hx)))).le, add_mul] }
end

lemma tendsto_nat_ceil_div_at_top :
  tendsto (λ x, (⌈x⌉₊ : R) / x) at_top (𝓝 1) :=
by simpa using tendsto_nat_ceil_mul_div_at_top (@zero_le_one R _)

end

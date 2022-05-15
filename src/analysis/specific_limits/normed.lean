/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Sébastien Gouëzel, Yury G. Kudryashov, Dylan MacKenzie, Patrick Massot
-/
import analysis.asymptotics.asymptotics
import analysis.specific_limits.basic

/-!
# A collection of specific limit computations

This file contains important specific limit computations in (semi-)normed groups/rings/spaces, as
as well as such computations in `ℝ` when the natural proof passes through a fact about normed
spaces.

-/

noncomputable theory
open classical set function filter finset metric asymptotics

open_locale classical topological_space nat big_operators uniformity nnreal ennreal

variables {α : Type*} {β : Type*} {ι : Type*}

lemma tendsto_norm_at_top_at_top : tendsto (norm : ℝ → ℝ) at_top at_top :=
tendsto_abs_at_top_at_top

lemma summable_of_absolute_convergence_real {f : ℕ → ℝ} :
  (∃r, tendsto (λn, (∑ i in range n, |f i|)) at_top (𝓝 r)) → summable f
| ⟨r, hr⟩ :=
  begin
    refine summable_of_summable_norm ⟨r, (has_sum_iff_tendsto_nat_of_nonneg _ _).2 _⟩,
    exact assume i, norm_nonneg _,
    simpa only using hr
  end

/-! ### Powers -/

lemma tendsto_norm_zero' {𝕜 : Type*} [normed_group 𝕜] :
  tendsto (norm : 𝕜 → ℝ) (𝓝[≠] 0) (𝓝[>] 0) :=
tendsto_norm_zero.inf $ tendsto_principal_principal.2 $ λ x hx, norm_pos_iff.2 hx

namespace normed_field

lemma tendsto_norm_inverse_nhds_within_0_at_top {𝕜 : Type*} [normed_field 𝕜] :
  tendsto (λ x:𝕜, ∥x⁻¹∥) (𝓝[≠] 0) at_top :=
(tendsto_inv_zero_at_top.comp tendsto_norm_zero').congr $ λ x, (norm_inv x).symm

lemma tendsto_norm_zpow_nhds_within_0_at_top {𝕜 : Type*} [normed_field 𝕜] {m : ℤ}
  (hm : m < 0) :
  tendsto (λ x : 𝕜, ∥x ^ m∥) (𝓝[≠] 0) at_top :=
begin
  rcases neg_surjective m with ⟨m, rfl⟩,
  rw neg_lt_zero at hm, lift m to ℕ using hm.le, rw int.coe_nat_pos at hm,
  simp only [norm_pow, zpow_neg₀, zpow_coe_nat, ← inv_pow₀],
  exact (tendsto_pow_at_top hm).comp normed_field.tendsto_norm_inverse_nhds_within_0_at_top
end

/-- The (scalar) product of a sequence that tends to zero with a bounded one also tends to zero. -/
lemma tendsto_zero_smul_of_tendsto_zero_of_bounded {ι 𝕜 𝔸 : Type*} [normed_field 𝕜]
  [normed_group 𝔸] [normed_space 𝕜 𝔸] {l : filter ι} {ε : ι → 𝕜} {f : ι → 𝔸}
  (hε : tendsto ε l (𝓝 0)) (hf : filter.is_bounded_under (≤) l (norm ∘ f)) :
  tendsto (ε • f) l (𝓝 0) :=
begin
  rw ← is_o_one_iff 𝕜 at hε ⊢,
  simpa using is_o.smul_is_O hε (hf.is_O_const (one_ne_zero : (1 : 𝕜) ≠ 0))
end

@[simp] lemma continuous_at_zpow {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {m : ℤ} {x : 𝕜} :
  continuous_at (λ x, x ^ m) x ↔ x ≠ 0 ∨ 0 ≤ m :=
begin
  refine ⟨_, continuous_at_zpow₀ _ _⟩,
  contrapose!, rintro ⟨rfl, hm⟩ hc,
  exact not_tendsto_at_top_of_tendsto_nhds (hc.tendsto.mono_left nhds_within_le_nhds).norm
      (tendsto_norm_zpow_nhds_within_0_at_top hm)
end

@[simp] lemma continuous_at_inv {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {x : 𝕜} :
  continuous_at has_inv.inv x ↔ x ≠ 0 :=
by simpa [(@zero_lt_one ℤ _ _).not_le] using @continuous_at_zpow _ _ (-1) x

end normed_field

lemma is_o_pow_pow_of_lt_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ < r₂) :
  is_o (λ n : ℕ, r₁ ^ n) (λ n, r₂ ^ n) at_top :=
have H : 0 < r₂ := h₁.trans_lt h₂,
is_o_of_tendsto (λ n hn, false.elim $ H.ne' $ pow_eq_zero hn) $
  (tendsto_pow_at_top_nhds_0_of_lt_1 (div_nonneg h₁ (h₁.trans h₂.le)) ((div_lt_one H).2 h₂)).congr
    (λ n, div_pow _ _ _)

lemma is_O_pow_pow_of_le_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ ≤ r₂) :
  is_O (λ n : ℕ, r₁ ^ n) (λ n, r₂ ^ n) at_top :=
h₂.eq_or_lt.elim (λ h, h ▸ is_O_refl _ _) (λ h, (is_o_pow_pow_of_lt_left h₁ h).is_O)

lemma is_o_pow_pow_of_abs_lt_left {r₁ r₂ : ℝ} (h : |r₁| < |r₂|) :
  is_o (λ n : ℕ, r₁ ^ n) (λ n, r₂ ^ n) at_top :=
begin
  refine (is_o.of_norm_left _).of_norm_right,
  exact (is_o_pow_pow_of_lt_left (abs_nonneg r₁) h).congr (pow_abs r₁) (pow_abs r₂)
end

/-- Various statements equivalent to the fact that `f n` grows exponentially slower than `R ^ n`.

* 0: $f n = o(a ^ n)$ for some $-R < a < R$;
* 1: $f n = o(a ^ n)$ for some $0 < a < R$;
* 2: $f n = O(a ^ n)$ for some $-R < a < R$;
* 3: $f n = O(a ^ n)$ for some $0 < a < R$;
* 4: there exist `a < R` and `C` such that one of `C` and `R` is positive and $|f n| ≤ Ca^n$
     for all `n`;
* 5: there exists `0 < a < R` and a positive `C` such that $|f n| ≤ Ca^n$ for all `n`;
* 6: there exists `a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`;
* 7: there exists `0 < a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`.

NB: For backwards compatibility, if you add more items to the list, please append them at the end of
the list. -/
lemma tfae_exists_lt_is_o_pow (f : ℕ → ℝ) (R : ℝ) :
  tfae [∃ a ∈ Ioo (-R) R, is_o f (pow a) at_top,
    ∃ a ∈ Ioo 0 R, is_o f (pow a) at_top,
    ∃ a ∈ Ioo (-R) R, is_O f (pow a) at_top,
    ∃ a ∈ Ioo 0 R, is_O f (pow a) at_top,
    ∃ (a < R) C (h₀ : 0 < C ∨ 0 < R), ∀ n, |f n| ≤ C * a ^ n,
    ∃ (a ∈ Ioo 0 R) (C > 0), ∀ n, |f n| ≤ C * a ^ n,
    ∃ a < R, ∀ᶠ n in at_top, |f n| ≤ a ^ n,
    ∃ a ∈ Ioo 0 R, ∀ᶠ n in at_top, |f n| ≤ a ^ n] :=
begin
  have A : Ico 0 R ⊆ Ioo (-R) R,
    from λ x hx, ⟨(neg_lt_zero.2 (hx.1.trans_lt hx.2)).trans_le hx.1, hx.2⟩,
  have B : Ioo 0 R ⊆ Ioo (-R) R := subset.trans Ioo_subset_Ico_self A,
  -- First we prove that 1-4 are equivalent using 2 → 3 → 4, 1 → 3, and 2 → 1
  tfae_have : 1 → 3, from λ ⟨a, ha, H⟩, ⟨a, ha, H.is_O⟩,
  tfae_have : 2 → 1, from λ ⟨a, ha, H⟩, ⟨a, B ha, H⟩,
  tfae_have : 3 → 2,
  { rintro ⟨a, ha, H⟩,
    rcases exists_between (abs_lt.2 ha) with ⟨b, hab, hbR⟩,
    exact ⟨b, ⟨(abs_nonneg a).trans_lt hab, hbR⟩,
      H.trans_is_o (is_o_pow_pow_of_abs_lt_left (hab.trans_le (le_abs_self b)))⟩ },
  tfae_have : 2 → 4, from λ ⟨a, ha, H⟩, ⟨a, ha, H.is_O⟩,
  tfae_have : 4 → 3, from λ ⟨a, ha, H⟩, ⟨a, B ha, H⟩,
  -- Add 5 and 6 using 4 → 6 → 5 → 3
  tfae_have : 4 → 6,
  { rintro ⟨a, ha, H⟩,
    rcases bound_of_is_O_nat_at_top H with ⟨C, hC₀, hC⟩,
    refine ⟨a, ha, C, hC₀, λ n, _⟩,
    simpa only [real.norm_eq_abs, abs_pow, abs_of_nonneg ha.1.le]
      using hC (pow_ne_zero n ha.1.ne') },
  tfae_have : 6 → 5, from λ ⟨a, ha, C, H₀, H⟩, ⟨a, ha.2, C, or.inl H₀, H⟩,
  tfae_have : 5 → 3,
  { rintro ⟨a, ha, C, h₀, H⟩,
    rcases sign_cases_of_C_mul_pow_nonneg (λ n, (abs_nonneg _).trans (H n)) with rfl | ⟨hC₀, ha₀⟩,
    { obtain rfl : f = 0, by { ext n, simpa using H n },
      simp only [lt_irrefl, false_or] at h₀,
      exact ⟨0, ⟨neg_lt_zero.2 h₀, h₀⟩, is_O_zero _ _⟩ },
    exact ⟨a, A ⟨ha₀, ha⟩,
      is_O_of_le' _ (λ n, (H n).trans $ mul_le_mul_of_nonneg_left (le_abs_self _) hC₀.le)⟩ },
  -- Add 7 and 8 using 2 → 8 → 7 → 3
  tfae_have : 2 → 8,
  { rintro ⟨a, ha, H⟩,
    refine ⟨a, ha, (H.def zero_lt_one).mono (λ n hn, _)⟩,
    rwa [real.norm_eq_abs, real.norm_eq_abs, one_mul, abs_pow, abs_of_pos ha.1] at hn },
  tfae_have : 8 → 7, from λ ⟨a, ha, H⟩, ⟨a, ha.2, H⟩,
  tfae_have : 7 → 3,
  { rintro ⟨a, ha, H⟩,
    have : 0 ≤ a, from nonneg_of_eventually_pow_nonneg (H.mono $ λ n, (abs_nonneg _).trans),
    refine ⟨a, A ⟨this, ha⟩, is_O.of_bound 1 _⟩,
    simpa only [real.norm_eq_abs, one_mul, abs_pow, abs_of_nonneg this] },
  tfae_finish
end

/-- For any natural `k` and a real `r > 1` we have `n ^ k = o(r ^ n)` as `n → ∞`. -/
lemma is_o_pow_const_const_pow_of_one_lt {R : Type*} [normed_ring R] (k : ℕ) {r : ℝ} (hr : 1 < r) :
  is_o (λ n, n ^ k : ℕ → R) (λ n, r ^ n) at_top :=
begin
  have : tendsto (λ x : ℝ, x ^ k) (𝓝[>] 1) (𝓝 1),
    from ((continuous_id.pow k).tendsto' (1 : ℝ) 1 (one_pow _)).mono_left inf_le_left,
  obtain ⟨r' : ℝ, hr' : r' ^ k < r, h1 : 1 < r'⟩ :=
    ((this.eventually (gt_mem_nhds hr)).and self_mem_nhds_within).exists,
  have h0 : 0 ≤ r' := zero_le_one.trans h1.le,
  suffices : is_O _ (λ n : ℕ, (r' ^ k) ^ n) at_top,
    from this.trans_is_o (is_o_pow_pow_of_lt_left (pow_nonneg h0 _) hr'),
  conv in ((r' ^ _) ^ _) { rw [← pow_mul, mul_comm, pow_mul] },
  suffices : ∀ n : ℕ, ∥(n : R)∥ ≤ (r' - 1)⁻¹ * ∥(1 : R)∥ * ∥r' ^ n∥,
    from (is_O_of_le' _ this).pow _,
  intro n, rw mul_right_comm,
  refine n.norm_cast_le.trans (mul_le_mul_of_nonneg_right _ (norm_nonneg _)),
  simpa [div_eq_inv_mul, real.norm_eq_abs, abs_of_nonneg h0] using n.cast_le_pow_div_sub h1
end

/-- For a real `r > 1` we have `n = o(r ^ n)` as `n → ∞`. -/
lemma is_o_coe_const_pow_of_one_lt {R : Type*} [normed_ring R] {r : ℝ} (hr : 1 < r) :
  is_o (coe : ℕ → R) (λ n, r ^ n) at_top :=
by simpa only [pow_one] using is_o_pow_const_const_pow_of_one_lt 1 hr

/-- If `∥r₁∥ < r₂`, then for any naturak `k` we have `n ^ k r₁ ^ n = o (r₂ ^ n)` as `n → ∞`. -/
lemma is_o_pow_const_mul_const_pow_const_pow_of_norm_lt {R : Type*} [normed_ring R] (k : ℕ)
  {r₁ : R} {r₂ : ℝ} (h : ∥r₁∥ < r₂) :
  is_o (λ n, n ^ k * r₁ ^ n : ℕ → R) (λ n, r₂ ^ n) at_top :=
begin
  by_cases h0 : r₁ = 0,
  { refine (is_o_zero _ _).congr' (mem_at_top_sets.2 $ ⟨1, λ n hn, _⟩) eventually_eq.rfl,
    simp [zero_pow (zero_lt_one.trans_le hn), h0] },
  rw [← ne.def, ← norm_pos_iff] at h0,
  have A : is_o (λ n, n ^ k : ℕ → R) (λ n, (r₂ / ∥r₁∥) ^ n) at_top,
    from is_o_pow_const_const_pow_of_one_lt k ((one_lt_div h0).2 h),
  suffices : is_O (λ n, r₁ ^ n) (λ n, ∥r₁∥ ^ n) at_top,
    by simpa [div_mul_cancel _ (pow_pos h0 _).ne'] using A.mul_is_O this,
  exact is_O.of_bound 1 (by simpa using eventually_norm_pow_le r₁)
end

lemma tendsto_pow_const_div_const_pow_of_one_lt (k : ℕ) {r : ℝ} (hr : 1 < r) :
  tendsto (λ n, n ^ k / r ^ n : ℕ → ℝ) at_top (𝓝 0) :=
(is_o_pow_const_const_pow_of_one_lt k hr).tendsto_div_nhds_zero

/-- If `|r| < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`. -/
lemma tendsto_pow_const_mul_const_pow_of_abs_lt_one (k : ℕ) {r : ℝ} (hr : |r| < 1) :
  tendsto (λ n, n ^ k * r ^ n : ℕ → ℝ) at_top (𝓝 0) :=
begin
  by_cases h0 : r = 0,
  { exact tendsto_const_nhds.congr'
      (mem_at_top_sets.2 ⟨1, λ n hn, by simp [zero_lt_one.trans_le hn, h0]⟩) },
  have hr' : 1 < (|r|)⁻¹, from one_lt_inv (abs_pos.2 h0) hr,
  rw tendsto_zero_iff_norm_tendsto_zero,
  simpa [div_eq_mul_inv] using tendsto_pow_const_div_const_pow_of_one_lt k hr'
end

/-- If `0 ≤ r < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`.
This is a specialized version of `tendsto_pow_const_mul_const_pow_of_abs_lt_one`, singled out
for ease of application. -/
lemma tendsto_pow_const_mul_const_pow_of_lt_one (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
  tendsto (λ n, n ^ k * r ^ n : ℕ → ℝ) at_top (𝓝 0) :=
tendsto_pow_const_mul_const_pow_of_abs_lt_one k (abs_lt.2 ⟨neg_one_lt_zero.trans_le hr, h'r⟩)

/-- If `|r| < 1`, then `n * r ^ n` tends to zero. -/
lemma tendsto_self_mul_const_pow_of_abs_lt_one {r : ℝ} (hr : |r| < 1) :
  tendsto (λ n, n * r ^ n : ℕ → ℝ) at_top (𝓝 0) :=
by simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr

/-- If `0 ≤ r < 1`, then `n * r ^ n` tends to zero. This is a specialized version of
`tendsto_self_mul_const_pow_of_abs_lt_one`, singled out for ease of application. -/
lemma tendsto_self_mul_const_pow_of_lt_one {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
  tendsto (λ n, n * r ^ n : ℕ → ℝ) at_top (𝓝 0) :=
by simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_lt_one 1 hr h'r

/-- In a normed ring, the powers of an element x with `∥x∥ < 1` tend to zero. -/
lemma tendsto_pow_at_top_nhds_0_of_norm_lt_1 {R : Type*} [normed_ring R] {x : R}
  (h : ∥x∥ < 1) : tendsto (λ (n : ℕ), x ^ n) at_top (𝓝 0) :=
begin
  apply squeeze_zero_norm' (eventually_norm_pow_le x),
  exact tendsto_pow_at_top_nhds_0_of_lt_1 (norm_nonneg _) h,
end

lemma tendsto_pow_at_top_nhds_0_of_abs_lt_1 {r : ℝ} (h : |r| < 1) :
  tendsto (λn:ℕ, r^n) at_top (𝓝 0) :=
tendsto_pow_at_top_nhds_0_of_norm_lt_1 h

/-! ### Geometric series-/
section geometric

variables {K : Type*} [normed_field K] {ξ : K}

lemma has_sum_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : has_sum (λn:ℕ, ξ ^ n) (1 - ξ)⁻¹ :=
begin
  have xi_ne_one : ξ ≠ 1, by { contrapose! h, simp [h] },
  have A : tendsto (λn, (ξ ^ n - 1) * (ξ - 1)⁻¹) at_top (𝓝 ((0 - 1) * (ξ - 1)⁻¹)),
    from ((tendsto_pow_at_top_nhds_0_of_norm_lt_1 h).sub tendsto_const_nhds).mul tendsto_const_nhds,
  have B : (λ n, (∑ i in range n, ξ ^ i)) = (λ n, geom_sum ξ n) := rfl,
  rw [has_sum_iff_tendsto_nat_of_summable_norm, B],
  { simpa [geom_sum_eq, xi_ne_one, neg_inv, div_eq_mul_inv] using A },
  { simp [norm_pow, summable_geometric_of_lt_1 (norm_nonneg _) h] }
end

lemma summable_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : summable (λn:ℕ, ξ ^ n) :=
⟨_, has_sum_geometric_of_norm_lt_1 h⟩

lemma tsum_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : ∑'n:ℕ, ξ ^ n = (1 - ξ)⁻¹ :=
(has_sum_geometric_of_norm_lt_1 h).tsum_eq

lemma has_sum_geometric_of_abs_lt_1 {r : ℝ} (h : |r| < 1) : has_sum (λn:ℕ, r ^ n) (1 - r)⁻¹ :=
has_sum_geometric_of_norm_lt_1 h

lemma summable_geometric_of_abs_lt_1 {r : ℝ} (h : |r| < 1) : summable (λn:ℕ, r ^ n) :=
summable_geometric_of_norm_lt_1 h

lemma tsum_geometric_of_abs_lt_1 {r : ℝ} (h : |r| < 1) : ∑'n:ℕ, r ^ n = (1 - r)⁻¹ :=
tsum_geometric_of_norm_lt_1 h

/-- A geometric series in a normed field is summable iff the norm of the common ratio is less than
one. -/
@[simp] lemma summable_geometric_iff_norm_lt_1 : summable (λ n : ℕ, ξ ^ n) ↔ ∥ξ∥ < 1 :=
begin
  refine ⟨λ h, _, summable_geometric_of_norm_lt_1⟩,
  obtain ⟨k : ℕ, hk : dist (ξ ^ k) 0 < 1⟩ :=
    (h.tendsto_cofinite_zero.eventually (ball_mem_nhds _ zero_lt_one)).exists,
  simp only [norm_pow, dist_zero_right] at hk,
  rw [← one_pow k] at hk,
  exact lt_of_pow_lt_pow _ zero_le_one hk
end

end geometric

section mul_geometric

lemma summable_norm_pow_mul_geometric_of_norm_lt_1 {R : Type*} [normed_ring R]
  (k : ℕ) {r : R} (hr : ∥r∥ < 1) : summable (λ n : ℕ, ∥(n ^ k * r ^ n : R)∥) :=
begin
  rcases exists_between hr with ⟨r', hrr', h⟩,
  exact summable_of_is_O_nat (summable_geometric_of_lt_1 ((norm_nonneg _).trans hrr'.le) h)
    (is_o_pow_const_mul_const_pow_const_pow_of_norm_lt _ hrr').is_O.norm_left
end

lemma summable_pow_mul_geometric_of_norm_lt_1 {R : Type*} [normed_ring R] [complete_space R]
  (k : ℕ) {r : R} (hr : ∥r∥ < 1) : summable (λ n, n ^ k * r ^ n : ℕ → R) :=
summable_of_summable_norm $ summable_norm_pow_mul_geometric_of_norm_lt_1 _ hr

/-- If `∥r∥ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, `has_sum` version. -/
lemma has_sum_coe_mul_geometric_of_norm_lt_1 {𝕜 : Type*} [normed_field 𝕜] [complete_space 𝕜]
  {r : 𝕜} (hr : ∥r∥ < 1) : has_sum (λ n, n * r ^ n : ℕ → 𝕜) (r / (1 - r) ^ 2) :=
begin
  have A : summable (λ n, n * r ^ n : ℕ → 𝕜),
    by simpa using summable_pow_mul_geometric_of_norm_lt_1 1 hr,
  have B : has_sum (pow r : ℕ → 𝕜) (1 - r)⁻¹, from has_sum_geometric_of_norm_lt_1 hr,
  refine A.has_sum_iff.2 _,
  have hr' : r ≠ 1, by { rintro rfl, simpa [lt_irrefl] using hr },
  set s : 𝕜 := ∑' n : ℕ, n * r ^ n,
  calc s = (1 - r) * s / (1 - r) : (mul_div_cancel_left _ (sub_ne_zero.2 hr'.symm)).symm
  ... = (s - r * s) / (1 - r) : by rw [sub_mul, one_mul]
  ... = ((0 : ℕ) * r ^ 0 + (∑' n : ℕ, (n + 1) * r ^ (n + 1)) - r * s) / (1 - r) :
    by { congr, exact tsum_eq_zero_add A }
  ... = (r * (∑' n : ℕ, (n + 1) * r ^ n) - r * s) / (1 - r) :
    by simp [pow_succ, mul_left_comm _ r, tsum_mul_left]
  ... = r / (1 - r) ^ 2 :
    by simp [add_mul, tsum_add A B.summable, mul_add, B.tsum_eq, ← div_eq_mul_inv, sq,
      div_div]
end

/-- If `∥r∥ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`. -/
lemma tsum_coe_mul_geometric_of_norm_lt_1 {𝕜 : Type*} [normed_field 𝕜] [complete_space 𝕜]
  {r : 𝕜} (hr : ∥r∥ < 1) :
  (∑' n : ℕ, n * r ^ n : 𝕜) = (r / (1 - r) ^ 2) :=
(has_sum_coe_mul_geometric_of_norm_lt_1 hr).tsum_eq

end mul_geometric

section summable_le_geometric

variables [semi_normed_group α] {r C : ℝ} {f : ℕ → α}

lemma semi_normed_group.cauchy_seq_of_le_geometric {C : ℝ} {r : ℝ} (hr : r < 1)
  {u : ℕ → α} (h : ∀ n, ∥u n - u (n + 1)∥ ≤ C*r^n) : cauchy_seq u :=
cauchy_seq_of_le_geometric r C hr (by simpa [dist_eq_norm] using h)

lemma dist_partial_sum_le_of_le_geometric (hf : ∀n, ∥f n∥ ≤ C * r^n) (n : ℕ) :
  dist (∑ i in range n, f i) (∑ i in range (n+1), f i) ≤ C * r ^ n :=
begin
  rw [sum_range_succ, dist_eq_norm, ← norm_neg, neg_sub, add_sub_cancel'],
  exact hf n,
end

/-- If `∥f n∥ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` form a
Cauchy sequence. This lemma does not assume `0 ≤ r` or `0 ≤ C`. -/
lemma cauchy_seq_finset_of_geometric_bound (hr : r < 1) (hf : ∀n, ∥f n∥ ≤ C * r^n) :
  cauchy_seq (λ s : finset (ℕ), ∑ x in s, f x) :=
cauchy_seq_finset_of_norm_bounded _
  (aux_has_sum_of_le_geometric hr (dist_partial_sum_le_of_le_geometric hf)).summable hf

/-- If `∥f n∥ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` are within
distance `C * r ^ n / (1 - r)` of the sum of the series. This lemma does not assume `0 ≤ r` or
`0 ≤ C`. -/
lemma norm_sub_le_of_geometric_bound_of_has_sum (hr : r < 1) (hf : ∀n, ∥f n∥ ≤ C * r^n)
  {a : α} (ha : has_sum f a) (n : ℕ) :
  ∥(∑ x in finset.range n, f x) - a∥ ≤ (C * r ^ n) / (1 - r) :=
begin
  rw ← dist_eq_norm,
  apply dist_le_of_le_geometric_of_tendsto r C hr (dist_partial_sum_le_of_le_geometric hf),
  exact ha.tendsto_sum_nat
end

@[simp] lemma dist_partial_sum (u : ℕ → α) (n : ℕ) :
 dist (∑ k in range (n + 1), u k) (∑ k in range n, u k) = ∥u n∥ :=
by simp [dist_eq_norm, sum_range_succ]

@[simp] lemma dist_partial_sum' (u : ℕ → α) (n : ℕ) :
 dist (∑ k in range n, u k) (∑ k in range (n+1), u k) = ∥u n∥ :=
by simp [dist_eq_norm', sum_range_succ]

lemma cauchy_series_of_le_geometric {C : ℝ} {u : ℕ → α}
  {r : ℝ} (hr : r < 1) (h : ∀ n, ∥u n∥ ≤ C*r^n) : cauchy_seq (λ n, ∑ k in range n, u k) :=
cauchy_seq_of_le_geometric r C hr (by simp [h])

lemma normed_group.cauchy_series_of_le_geometric' {C : ℝ} {u : ℕ → α} {r : ℝ} (hr : r < 1)
  (h : ∀ n, ∥u n∥ ≤ C*r^n) : cauchy_seq (λ n, ∑ k in range (n + 1), u k) :=
(cauchy_series_of_le_geometric hr h).comp_tendsto $ tendsto_add_at_top_nat 1

lemma normed_group.cauchy_series_of_le_geometric'' {C : ℝ} {u : ℕ → α} {N : ℕ} {r : ℝ}
  (hr₀ : 0 < r) (hr₁ : r < 1)
  (h : ∀ n ≥ N, ∥u n∥ ≤ C*r^n) : cauchy_seq (λ n, ∑ k in range (n + 1), u k) :=
begin
  set v : ℕ → α := λ n, if n < N then 0 else u n,
  have hC : 0 ≤ C,
    from (zero_le_mul_right $ pow_pos hr₀ N).mp ((norm_nonneg _).trans $ h N $ le_refl N),
  have : ∀ n ≥ N, u n = v n,
  { intros n hn,
    simp [v, hn, if_neg (not_lt.mpr hn)] },
  refine cauchy_seq_sum_of_eventually_eq this (normed_group.cauchy_series_of_le_geometric' hr₁ _),
  { exact C },
  intro n,
  dsimp [v],
  split_ifs with H H,
  { rw norm_zero,
    exact mul_nonneg hC (pow_nonneg hr₀.le _) },
  { push_neg at H,
    exact h _ H }
end

end summable_le_geometric

section normed_ring_geometric
variables {R : Type*} [normed_ring R] [complete_space R]

open normed_space

/-- A geometric series in a complete normed ring is summable.
Proved above (same name, different namespace) for not-necessarily-complete normed fields. -/
lemma normed_ring.summable_geometric_of_norm_lt_1
  (x : R) (h : ∥x∥ < 1) : summable (λ (n:ℕ), x ^ n) :=
begin
  have h1 : summable (λ (n:ℕ), ∥x∥ ^ n) := summable_geometric_of_lt_1 (norm_nonneg _) h,
  refine summable_of_norm_bounded_eventually _ h1 _,
  rw nat.cofinite_eq_at_top,
  exact eventually_norm_pow_le x,
end

/-- Bound for the sum of a geometric series in a normed ring.  This formula does not assume that the
normed ring satisfies the axiom `∥1∥ = 1`. -/
lemma normed_ring.tsum_geometric_of_norm_lt_1
  (x : R) (h : ∥x∥ < 1) : ∥∑' n:ℕ, x ^ n∥ ≤ ∥(1:R)∥ - 1 + (1 - ∥x∥)⁻¹ :=
begin
  rw tsum_eq_zero_add (normed_ring.summable_geometric_of_norm_lt_1 x h),
  simp only [pow_zero],
  refine le_trans (norm_add_le _ _) _,
  have : ∥∑' b : ℕ, (λ n, x ^ (n + 1)) b∥ ≤ (1 - ∥x∥)⁻¹ - 1,
  { refine tsum_of_norm_bounded _ (λ b, norm_pow_le' _ (nat.succ_pos b)),
    convert (has_sum_nat_add_iff' 1).mpr (has_sum_geometric_of_lt_1 (norm_nonneg x) h),
    simp },
  linarith
end

lemma geom_series_mul_neg (x : R) (h : ∥x∥ < 1) :
  (∑' i:ℕ, x ^ i) * (1 - x) = 1 :=
begin
  have := ((normed_ring.summable_geometric_of_norm_lt_1 x h).has_sum.mul_right (1 - x)),
  refine tendsto_nhds_unique this.tendsto_sum_nat _,
  have : tendsto (λ (n : ℕ), 1 - x ^ n) at_top (𝓝 1),
  { simpa using tendsto_const_nhds.sub (tendsto_pow_at_top_nhds_0_of_norm_lt_1 h) },
  convert ← this,
  ext n,
  rw [←geom_sum_mul_neg, geom_sum_def, finset.sum_mul],
end

lemma mul_neg_geom_series (x : R) (h : ∥x∥ < 1) :
  (1 - x) * ∑' i:ℕ, x ^ i = 1 :=
begin
  have := (normed_ring.summable_geometric_of_norm_lt_1 x h).has_sum.mul_left (1 - x),
  refine tendsto_nhds_unique this.tendsto_sum_nat _,
  have : tendsto (λ (n : ℕ), 1 - x ^ n) at_top (nhds 1),
  { simpa using tendsto_const_nhds.sub
      (tendsto_pow_at_top_nhds_0_of_norm_lt_1 h) },
  convert ← this,
  ext n,
  rw [←mul_neg_geom_sum, geom_sum_def, finset.mul_sum]
end

end normed_ring_geometric

/-! ### Summability tests based on comparison with geometric series -/

lemma summable_of_ratio_norm_eventually_le {α : Type*} [semi_normed_group α] [complete_space α]
  {f : ℕ → α} {r : ℝ} (hr₁ : r < 1)
  (h : ∀ᶠ n in at_top, ∥f (n+1)∥ ≤ r * ∥f n∥) : summable f :=
begin
  by_cases hr₀ : 0 ≤ r,
  { rw eventually_at_top at h,
    rcases h with ⟨N, hN⟩,
    rw ← @summable_nat_add_iff α _ _ _ _ N,
    refine summable_of_norm_bounded (λ n, ∥f N∥ * r^n)
      (summable.mul_left _ $ summable_geometric_of_lt_1 hr₀ hr₁) (λ n, _),
    conv_rhs {rw [mul_comm, ← zero_add N]},
    refine le_geom hr₀ n (λ i _, _),
    convert hN (i + N) (N.le_add_left i) using 3,
    ac_refl },
  { push_neg at hr₀,
    refine summable_of_norm_bounded_eventually 0 summable_zero _,
    rw nat.cofinite_eq_at_top,
    filter_upwards [h] with _ hn,
    by_contra' h,
    exact not_lt.mpr (norm_nonneg _) (lt_of_le_of_lt hn $ mul_neg_of_neg_of_pos hr₀ h), },
end

lemma summable_of_ratio_test_tendsto_lt_one {α : Type*} [normed_group α] [complete_space α]
  {f : ℕ → α} {l : ℝ} (hl₁ : l < 1) (hf : ∀ᶠ n in at_top, f n ≠ 0)
  (h : tendsto (λ n, ∥f (n+1)∥/∥f n∥) at_top (𝓝 l)) : summable f :=
begin
  rcases exists_between hl₁ with ⟨r, hr₀, hr₁⟩,
  refine summable_of_ratio_norm_eventually_le hr₁ _,
  filter_upwards [eventually_le_of_tendsto_lt hr₀ h, hf] with _ _ h₁,
  rwa ← div_le_iff (norm_pos_iff.mpr h₁),
end

lemma not_summable_of_ratio_norm_eventually_ge {α : Type*} [semi_normed_group α]
  {f : ℕ → α} {r : ℝ} (hr : 1 < r) (hf : ∃ᶠ n in at_top, ∥f n∥ ≠ 0)
  (h : ∀ᶠ n in at_top, r * ∥f n∥ ≤ ∥f (n+1)∥) : ¬ summable f :=
begin
  rw eventually_at_top at h,
  rcases h with ⟨N₀, hN₀⟩,
  rw frequently_at_top at hf,
  rcases hf N₀ with ⟨N, hNN₀ : N₀ ≤ N, hN⟩,
  rw ← @summable_nat_add_iff α _ _ _ _ N,
  refine mt summable.tendsto_at_top_zero
    (λ h', not_tendsto_at_top_of_tendsto_nhds (tendsto_norm_zero.comp h') _),
  convert tendsto_at_top_of_geom_le _ hr _,
  { refine lt_of_le_of_ne (norm_nonneg _) _,
    intro h'',
    specialize hN₀ N hNN₀,
    simp only [comp_app, zero_add] at h'',
    exact hN h''.symm },
  { intro i,
    dsimp only [comp_app],
    convert (hN₀ (i + N) (hNN₀.trans (N.le_add_left i))) using 3,
    ac_refl }
end

lemma not_summable_of_ratio_test_tendsto_gt_one {α : Type*} [semi_normed_group α]
  {f : ℕ → α} {l : ℝ} (hl : 1 < l)
  (h : tendsto (λ n, ∥f (n+1)∥/∥f n∥) at_top (𝓝 l)) : ¬ summable f :=
begin
  have key : ∀ᶠ n in at_top, ∥f n∥ ≠ 0,
  { filter_upwards [eventually_ge_of_tendsto_gt hl h] with _ hn hc,
    rw [hc, div_zero] at hn,
    linarith },
  rcases exists_between hl with ⟨r, hr₀, hr₁⟩,
  refine not_summable_of_ratio_norm_eventually_ge hr₀ key.frequently _,
  filter_upwards [eventually_ge_of_tendsto_gt hr₁ h, key] with _ _ h₁,
  rwa ← le_div_iff (lt_of_le_of_ne (norm_nonneg _) h₁.symm)
end

section
/-! ### Dirichlet and alternating series tests -/

variables {E : Type*} [normed_group E] [normed_space ℝ E]
variables {b : ℝ} {f : ℕ → ℝ} {z : ℕ → E}

/-- **Dirichlet's Test** for monotone sequences. -/
theorem monotone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded
  (hfa : monotone f) (hf0 : tendsto f at_top (𝓝 0)) (hgb : ∀ n, ∥∑ i in range n, z i∥ ≤ b) :
  cauchy_seq (λ n, ∑ i in range (n + 1), (f i) • z i) :=
begin
  simp_rw [finset.sum_range_by_parts _ _ (nat.succ _), sub_eq_add_neg,
           nat.succ_sub_succ_eq_sub, tsub_zero],
  apply (normed_field.tendsto_zero_smul_of_tendsto_zero_of_bounded hf0
    ⟨b, eventually_map.mpr $ eventually_of_forall $ λ n, hgb $ n+1⟩).cauchy_seq.add,
  apply (cauchy_seq_range_of_norm_bounded _ _ (_ : ∀ n, _ ≤ b * |f(n+1) - f(n)|)).neg,
  { exact normed_uniform_group },
  { simp_rw [abs_of_nonneg (sub_nonneg_of_le (hfa (nat.le_succ _))), ← mul_sum],
    apply real.uniform_continuous_mul_const.comp_cauchy_seq,
    simp_rw [sum_range_sub, sub_eq_add_neg],
    exact (tendsto.cauchy_seq hf0).add_const },
  { intro n,
    rw [norm_smul, mul_comm],
    exact mul_le_mul_of_nonneg_right (hgb _) (abs_nonneg _) },
end

/-- **Dirichlet's test** for antitone sequences. -/
theorem antitone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded
  (hfa : antitone f) (hf0 : tendsto f at_top (𝓝 0)) (hzb : ∀ n, ∥∑ i in range n, z i∥ ≤ b) :
  cauchy_seq (λ n, ∑ i in range (n+1), (f i) • z i) :=
begin
  have hfa': monotone (λ n, -f n) := λ _ _ hab, neg_le_neg $ hfa hab,
  have hf0': tendsto (λ n, -f n) at_top (𝓝 0) := by { convert hf0.neg, norm_num },
  convert (hfa'.cauchy_seq_series_mul_of_tendsto_zero_of_bounded hf0' hzb).neg,
  funext,
  simp
end

lemma norm_sum_neg_one_pow_le (n : ℕ) : ∥∑ i in range n, (-1 : ℝ) ^ i∥ ≤ 1 :=
by { rw [←geom_sum_def, neg_one_geom_sum], split_ifs; norm_num }

/-- The **alternating series test** for monotone sequences.
See also `tendsto_alternating_series_of_monotone_tendsto_zero`. -/
theorem monotone.cauchy_seq_alternating_series_of_tendsto_zero
  (hfa : monotone f) (hf0 : tendsto f at_top (𝓝 0)) :
  cauchy_seq (λ n, ∑ i in range (n+1), (-1) ^ i * f i) :=
begin
  simp_rw [mul_comm],
  exact hfa.cauchy_seq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le
end

/-- The **alternating series test** for monotone sequences. -/
theorem monotone.tendsto_alternating_series_of_tendsto_zero
  (hfa : monotone f) (hf0 : tendsto f at_top (𝓝 0)) :
  ∃ l, tendsto (λ n, ∑ i in range (n+1), (-1) ^ i * f i) at_top (𝓝 l) :=
cauchy_seq_tendsto_of_complete $ hfa.cauchy_seq_alternating_series_of_tendsto_zero hf0

/-- The **alternating series test** for antitone sequences.
See also `tendsto_alternating_series_of_antitone_tendsto_zero`. -/
theorem antitone.cauchy_seq_alternating_series_of_tendsto_zero
  (hfa : antitone f) (hf0 : tendsto f at_top (𝓝 0)) :
  cauchy_seq (λ n, ∑ i in range (n+1), (-1) ^ i * f i) :=
begin
  simp_rw [mul_comm],
  exact
    hfa.cauchy_seq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le
end

/-- The **alternating series test** for antitone sequences. -/
theorem antitone.tendsto_alternating_series_of_tendsto_zero
  (hfa : antitone f) (hf0 : tendsto f at_top (𝓝 0)) :
  ∃ l, tendsto (λ n, ∑ i in range (n+1), (-1) ^ i * f i) at_top (𝓝 l) :=
cauchy_seq_tendsto_of_complete $ hfa.cauchy_seq_alternating_series_of_tendsto_zero hf0

end

/-!
### Factorial
-/

/-- The series `∑' n, x ^ n / n!` is summable of any `x : ℝ`. See also `exp_series_div_summable`
for a version that also works in `ℂ`, and `exp_series_summable'` for a version that works in
any normed algebra over `ℝ` or `ℂ`. -/
lemma real.summable_pow_div_factorial (x : ℝ) :
  summable (λ n, x ^ n / n! : ℕ → ℝ) :=
begin
  -- We start with trivial extimates
  have A : (0 : ℝ) < ⌊∥x∥⌋₊ + 1, from zero_lt_one.trans_le (by simp),
  have B : ∥x∥ / (⌊∥x∥⌋₊ + 1) < 1, from (div_lt_one A).2 (nat.lt_floor_add_one _),
  -- Then we apply the ratio test. The estimate works for `n ≥ ⌊∥x∥⌋₊`.
  suffices : ∀ n ≥ ⌊∥x∥⌋₊, ∥x ^ (n + 1) / (n + 1)!∥ ≤ ∥x∥ / (⌊∥x∥⌋₊ + 1) * ∥x ^ n / ↑n!∥,
    from summable_of_ratio_norm_eventually_le B (eventually_at_top.2 ⟨⌊∥x∥⌋₊, this⟩),
  -- Finally, we prove the upper estimate
  intros n hn,
  calc ∥x ^ (n + 1) / (n + 1)!∥ = (∥x∥ / (n + 1)) * ∥x ^ n / n!∥ :
    by rw [pow_succ, nat.factorial_succ, nat.cast_mul, ← div_mul_div_comm,
      norm_mul, norm_div, real.norm_coe_nat, nat.cast_succ]
  ... ≤ (∥x∥ / (⌊∥x∥⌋₊ + 1)) * ∥x ^ n / n!∥ :
    by mono* with [0 ≤ ∥x ^ n / n!∥, 0 ≤ ∥x∥]; apply norm_nonneg
end

lemma real.tendsto_pow_div_factorial_at_top (x : ℝ) :
  tendsto (λ n, x ^ n / n! : ℕ → ℝ) at_top (𝓝 0) :=
(real.summable_pow_div_factorial x).tendsto_at_top_zero

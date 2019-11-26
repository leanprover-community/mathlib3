/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

A collection of specific limit computations.
-/
import analysis.normed_space.basic algebra.geom_sum
import topology.instances.ennreal

noncomputable theory
open_locale classical topological_space

open classical function lattice filter finset metric

variables {α : Type*} {β : Type*} {ι : Type*}

lemma summable_of_absolute_convergence_real {f : ℕ → ℝ} :
  (∃r, tendsto (λn, (range n).sum (λi, abs (f i))) at_top (𝓝 r)) → summable f
| ⟨r, hr⟩ :=
  begin
    refine summable_of_summable_norm ⟨r, (has_sum_iff_tendsto_nat_of_nonneg _ _).2 _⟩,
    exact assume i, norm_nonneg _,
    simpa only using hr
  end

lemma tendsto_pow_at_top_at_top_of_gt_1 {r : ℝ} (h : r > 1) :
  tendsto (λn:ℕ, r ^ n) at_top at_top :=
(tendsto_at_top_at_top _).2 $ assume p,
  let ⟨n, hn⟩ := pow_unbounded_of_one_lt p h in
  ⟨n, λ m hnm, le_of_lt $
    lt_of_lt_of_le hn (pow_le_pow (le_of_lt h) hnm)⟩

lemma tendsto_inverse_at_top_nhds_0 : tendsto (λr:ℝ, r⁻¹) at_top (𝓝 0) :=
tendsto_orderable_unbounded (no_top 0) (no_bot 0) $ assume l u hl hu,
  mem_at_top_sets.mpr ⟨u⁻¹ + 1, assume b hb,
    have u⁻¹ < b, from lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one) hb,
    ⟨lt_trans hl $ inv_pos $ lt_trans (inv_pos hu) this,
    lt_of_one_div_lt_one_div hu $
    begin
      rw [inv_eq_one_div],
      simp [-one_div_eq_inv, div_div_eq_mul_div, div_one],
      simp [this]
    end⟩⟩

lemma tendsto_pow_at_top_nhds_0_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  tendsto (λn:ℕ, r^n) at_top (𝓝 0) :=
by_cases
  (assume : r = 0, (tendsto_add_at_top_iff_nat 1).mp $ by simp [pow_succ, this, tendsto_const_nhds])
  (assume : r ≠ 0,
    have tendsto (λn, (r⁻¹ ^ n)⁻¹) at_top (𝓝 0),
      from tendsto.comp tendsto_inverse_at_top_nhds_0
        (tendsto_pow_at_top_at_top_of_gt_1 $ one_lt_inv (lt_of_le_of_ne h₁ this.symm) h₂),
    tendsto.congr' (univ_mem_sets' $ by simp *) this)

lemma tendsto_pow_at_top_nhds_0_of_lt_1_normed_field {K : Type*} [normed_field K] {ξ : K}
  (_ : ∥ξ∥ < 1) : tendsto (λ n : ℕ, ξ^n) at_top (𝓝 0) :=
begin
  rw[tendsto_iff_norm_tendsto_zero],
  convert tendsto_pow_at_top_nhds_0_of_lt_1 (norm_nonneg ξ) ‹∥ξ∥ < 1›,
  ext n,
  simp
end

lemma tendsto_pow_at_top_at_top_of_gt_1_nat {k : ℕ} (h : 1 < k) :
  tendsto (λn:ℕ, k ^ n) at_top at_top :=
tendsto_coe_nat_real_at_top_iff.1 $
  have hr : 1 < (k : ℝ), by rw [← nat.cast_one, nat.cast_lt]; exact h,
  by simpa using tendsto_pow_at_top_at_top_of_gt_1 hr

lemma tendsto_inverse_at_top_nhds_0_nat : tendsto (λ n : ℕ, (n : ℝ)⁻¹) at_top (𝓝 0) :=
tendsto.comp tendsto_inverse_at_top_nhds_0 (tendsto_coe_nat_real_at_top_iff.2 tendsto_id)

lemma tendsto_const_div_at_top_nhds_0_nat (C : ℝ) : tendsto (λ n : ℕ, C / n) at_top (𝓝 0) :=
by simpa only [mul_zero] using tendsto_mul tendsto_const_nhds tendsto_inverse_at_top_nhds_0_nat

lemma tendsto_one_div_add_at_top_nhds_0_nat :
  tendsto (λ n : ℕ, 1 / ((n : ℝ) + 1)) at_top (𝓝 0) :=
suffices tendsto (λ n : ℕ, 1 / (↑(n + 1) : ℝ)) at_top (𝓝 0), by simpa,
(tendsto_add_at_top_iff_nat 1).2 (tendsto_const_div_at_top_nhds_0_nat 1)

lemma has_sum_geometric {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  has_sum (λn:ℕ, r ^ n) (1 - r)⁻¹ :=
have r ≠ 1, from ne_of_lt h₂,
have r + -1 ≠ 0,
  by rw [←sub_eq_add_neg, ne, sub_eq_iff_eq_add]; simp; assumption,
have tendsto (λn, (r ^ n - 1) * (r - 1)⁻¹) at_top (𝓝 ((0 - 1) * (r - 1)⁻¹)),
  from tendsto_mul
    (tendsto_sub (tendsto_pow_at_top_nhds_0_of_lt_1 h₁ h₂) tendsto_const_nhds) tendsto_const_nhds,
have (λ n, (range n).sum (λ i, r ^ i)) = (λ n, geom_series r n) := rfl,
(has_sum_iff_tendsto_nat_of_nonneg (pow_nonneg h₁) _).mpr $
  by simp [neg_inv, geom_sum, div_eq_mul_inv, *] at *

lemma summable_geometric {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : summable (λn:ℕ, r ^ n) :=
⟨_, has_sum_geometric h₁ h₂⟩

lemma tsum_geometric {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : (∑n:ℕ, r ^ n) = (1 - r)⁻¹ :=
tsum_eq_has_sum (has_sum_geometric h₁ h₂)

lemma has_sum_geometric_two : has_sum (λn:ℕ, ((1:ℝ)/2) ^ n) 2 :=
by convert has_sum_geometric _ _; norm_num

lemma summable_geometric_two : summable (λn:ℕ, ((1:ℝ)/2) ^ n) :=
⟨_, has_sum_geometric_two⟩

lemma tsum_geometric_two : (∑n:ℕ, ((1:ℝ)/2) ^ n) = 2 :=
tsum_eq_has_sum has_sum_geometric_two

lemma has_sum_geometric_two' (a : ℝ) : has_sum (λn:ℕ, (a / 2) / 2 ^ n) a :=
begin
  convert has_sum_mul_left (a / 2) (has_sum_geometric
    (le_of_lt one_half_pos) one_half_lt_one),
  { funext n, simp,
    rw ← pow_inv; [refl, exact two_ne_zero] },
  { norm_num, rw div_mul_cancel _ two_ne_zero }
end

lemma summable_geometric_two' (a : ℝ) : summable (λ n:ℕ, (a / 2) / 2 ^ n) :=
⟨a, has_sum_geometric_two' a⟩

lemma tsum_geometric_two' (a : ℝ) : (∑ n:ℕ, (a / 2) / 2^n) = a :=
tsum_eq_has_sum $ has_sum_geometric_two' a

lemma has_sum_geometric_nnreal {r : nnreal} (hr : r < 1) :
  has_sum (λ n : ℕ, r ^ n) (1 - r)⁻¹ :=
begin
  apply nnreal.has_sum_coe.1,
  push_cast,
  rw [nnreal.coe_sub (le_of_lt hr)],
  exact has_sum_geometric r.coe_nonneg hr
end

lemma summable_geometric_nnreal {r : nnreal} (hr : r < 1) : summable (λn:ℕ, r ^ n) :=
⟨_, has_sum_geometric_nnreal hr⟩

lemma tsum_geometric_nnreal {r : nnreal} (hr : r < 1) : (∑n:ℕ, r ^ n) = (1 - r)⁻¹ :=
tsum_eq_has_sum (has_sum_geometric_nnreal hr)

def pos_sum_of_encodable {ε : ℝ} (hε : 0 < ε)
  (ι) [encodable ι] : {ε' : ι → ℝ // (∀ i, 0 < ε' i) ∧ ∃ c, has_sum ε' c ∧ c ≤ ε} :=
begin
  let f := λ n, (ε / 2) / 2 ^ n,
  have hf : has_sum f ε := has_sum_geometric_two' _,
  have f0 : ∀ n, 0 < f n := λ n, div_pos (half_pos hε) (pow_pos two_pos _),
  refine ⟨f ∘ encodable.encode, λ i, f0 _, _⟩,
  rcases summable_comp_of_summable_of_injective f (summable_spec hf) (@encodable.encode_injective ι _)
    with ⟨c, hg⟩,
  refine ⟨c, hg, has_sum_le_inj _ (@encodable.encode_injective ι _) _ _ hg hf⟩,
  { assume i _, exact le_of_lt (f0 _) },
  { assume n, exact le_refl _ }
end

section edist_le_geometric

variables [emetric_space α] (r C : nnreal) (hr : r < 1) {f : ℕ → α}
  (hu : ∀n, edist (f n) (f (n+1)) ≤ C * r^n)

include hr hu

lemma cauchy_seq_of_edist_le_geometric : cauchy_seq f :=
begin
  norm_cast at hu,
  exact cauchy_seq_of_edist_le_of_summable _ hu
   (summable_mul_left C $ summable_geometric_nnreal hr)
end

lemma edist_le_of_edist_le_geometric_of_tendsto {a : α} (ha : tendsto f at_top (𝓝 a)) (n : ℕ) :
  edist (f n) a ≤ (C * r^n) / (1 - r) :=
begin
  norm_cast at hu,
  rw_mod_cast [← ennreal.coe_one, ← ennreal.coe_div (ne_of_gt $ nnreal.sub_pos.2 hr)],
  convert edist_le_tsum_of_edist_le_of_tendsto _ hu
    (summable_mul_left C $ summable_geometric_nnreal hr) ha _,
  refine eq.symm (tsum_eq_has_sum _),
  simp only [pow_add, nnreal.div_def, mul_assoc],
  exact has_sum_mul_left C (has_sum_mul_left (r ^ n) (has_sum_geometric_nnreal hr))
end

lemma edist_le_of_edist_le_geometric_of_tendsto₀ {a : α} (ha : tendsto f at_top (𝓝 a)) :
  edist (f 0) a ≤ C / (1 - r) :=
by simpa only [pow_zero, mul_one] using edist_le_of_edist_le_geometric_of_tendsto r C hr hu ha 0

end edist_le_geometric

section le_geometric

variables [metric_space α] {r C : ℝ} (hr : r < 1) {f : ℕ → α}
  (hu : ∀n, dist (f n) (f (n+1)) ≤ C * r^n)

include hr hu

lemma aux_has_sum_of_le_geometric : has_sum (λ n : ℕ, C * r^n) (C / (1 - r)) :=
begin
  have h0 : 0 ≤ C,
    by simpa using le_trans dist_nonneg (hu 0),
  rcases eq_or_lt_of_le h0 with rfl | Cpos,
  { simp [has_sum_zero] },
  { have rnonneg: r ≥ 0, from nonneg_of_mul_nonneg_left
      (by simpa only [pow_one] using le_trans dist_nonneg (hu 1)) Cpos,
    refine has_sum_mul_left C _,
    by simpa using has_sum_geometric rnonneg hr }
end

variables (r C)

lemma cauchy_seq_of_le_geometric : cauchy_seq f :=
cauchy_seq_of_dist_le_of_summable _ hu ⟨_, aux_has_sum_of_le_geometric hr hu⟩

lemma dist_le_of_le_geometric_of_tendsto₀ {a : α} (ha : tendsto f at_top (𝓝 a)) :
  dist (f 0) a ≤ C / (1 - r) :=
(tsum_eq_has_sum $ aux_has_sum_of_le_geometric hr hu) ▸
  dist_le_tsum_of_dist_le_of_tendsto₀ _ hu ⟨_, aux_has_sum_of_le_geometric hr hu⟩ ha

lemma dist_le_of_le_geometric_of_tendsto {a : α} (ha : tendsto f at_top (𝓝 a)) (n : ℕ) :
  dist (f n) a ≤ (C * r^n) / (1 - r) :=
begin
  have := aux_has_sum_of_le_geometric hr hu,
  convert dist_le_tsum_of_dist_le_of_tendsto _ hu ⟨_, this⟩ ha n,
  simp only [pow_add, mul_left_comm C, mul_div_right_comm],
  rw [mul_comm],
  exact (eq.symm $ tsum_eq_has_sum $ has_sum_mul_left _ this)
end

omit hr hu

variable (hu₂ : ∀ n, dist (f n) (f (n+1)) ≤ (C / 2) / 2^n)

lemma cauchy_seq_of_le_geometric_two : cauchy_seq f :=
cauchy_seq_of_dist_le_of_summable _ hu₂ $ ⟨_, has_sum_geometric_two' C⟩

lemma dist_le_of_le_geometric_two_of_tendsto₀ {a : α} (ha : tendsto f at_top (𝓝 a)) :
  dist (f 0) a ≤ C :=
(tsum_geometric_two' C) ▸ dist_le_tsum_of_dist_le_of_tendsto₀ _ hu₂ (summable_geometric_two' C) ha

include hu₂

lemma dist_le_of_le_geometric_two_of_tendsto {a : α} (ha : tendsto f at_top (𝓝 a)) (n : ℕ) :
  dist (f n) a ≤ C / 2^n :=
begin
  convert dist_le_tsum_of_dist_le_of_tendsto _ hu₂ (summable_geometric_two' C) ha n,
  simp only [add_comm n, pow_add, (div_div_eq_div_mul _ _ _).symm],
  symmetry,
  exact tsum_eq_has_sum (has_sum_mul_right _ $ has_sum_geometric_two' C)
end

end le_geometric

namespace nnreal

theorem exists_pos_sum_of_encodable {ε : nnreal} (hε : 0 < ε) (ι) [encodable ι] :
  ∃ ε' : ι → nnreal, (∀ i, 0 < ε' i) ∧ ∃c, has_sum ε' c ∧ c < ε :=
let ⟨a, a0, aε⟩ := dense hε in
let ⟨ε', hε', c, hc, hcε⟩ := pos_sum_of_encodable a0 ι in
⟨ λi, ⟨ε' i, le_of_lt $ hε' i⟩, assume i, nnreal.coe_lt.2 $ hε' i,
  ⟨c, has_sum_le (assume i, le_of_lt $ hε' i) has_sum_zero hc ⟩, nnreal.has_sum_coe.1 hc,
   lt_of_le_of_lt (nnreal.coe_le.1 hcε) aε ⟩

end nnreal

namespace ennreal

theorem exists_pos_sum_of_encodable {ε : ennreal} (hε : 0 < ε) (ι) [encodable ι] :
  ∃ ε' : ι → nnreal, (∀ i, 0 < ε' i) ∧ (∑ i, (ε' i : ennreal)) < ε :=
begin
  rcases dense hε with ⟨r, h0r, hrε⟩,
  rcases lt_iff_exists_coe.1 hrε with ⟨x, rfl, hx⟩,
  rcases nnreal.exists_pos_sum_of_encodable (coe_lt_coe.1 h0r) ι with ⟨ε', hp, c, hc, hcr⟩,
  exact ⟨ε', hp, (ennreal.tsum_coe_eq hc).symm ▸ lt_trans (coe_lt_coe.2 hcr) hrε⟩
end

end ennreal

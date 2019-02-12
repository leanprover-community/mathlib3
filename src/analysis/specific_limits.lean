/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

A collection of specific limit computations.
-/
import analysis.normed_space.basic
import topology.instances.ennreal

noncomputable theory
local attribute [instance] classical.prop_decidable

open classical function lattice filter finset metric

variables {α : Type*} {β : Type*} {ι : Type*}

lemma has_sum_iff_cauchy [normed_group α] [complete_space α] {f : ι → α} :
  has_sum f ↔ ∀ε>0, (∃s:finset ι, ∀t, disjoint t s → ∥ t.sum f ∥ < ε) :=
begin
  refine iff.trans (cauchy_map_iff_exists_tendsto at_top_ne_bot).symm _,
  simp only [cauchy_map_iff, and_iff_right at_top_ne_bot, prod_at_top_at_top_eq, uniformity_dist,
    tendsto_infi, tendsto_at_top_principal, set.mem_set_of_eq],
  split,
  { assume h ε hε,
    rcases h ε hε with ⟨⟨s₁, s₂⟩, h⟩,
    use [s₁ ∪ s₂],
    assume t ht,
    have : (s₁ ∪ s₂) ∩ t = ∅ := finset.disjoint_iff_inter_eq_empty.1 ht.symm,
    specialize h (s₁ ∪ s₂, (s₁ ∪ s₂) ∪ t) ⟨le_sup_left, le_sup_left_of_le le_sup_right⟩,
    simpa only [finset.sum_union this, dist_eq_norm,
      sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg] using h },
  { assume h' ε hε,
    rcases h' (ε / 2) (half_pos hε) with ⟨s, h⟩,
    use [(s, s)],
    rintros ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩,
    dsimp at ht₁ ht₂,
    calc dist (t₁.sum f) (t₂.sum f) = ∥sum (t₁ \ s) f - sum (t₂ \ s) f∥ :
        by simp only [(finset.sum_sdiff ht₁).symm, (finset.sum_sdiff ht₂).symm,
          dist_eq_norm, add_sub_add_right_eq_sub]
      ... ≤ ∥sum (t₁ \ s) f∥ + ∥ sum (t₂ \ s) f∥ : norm_triangle_sub
      ... < ε / 2 + ε / 2 : add_lt_add (h _ finset.disjoint_sdiff) (h _ finset.disjoint_sdiff)
      ... = ε : add_halves _ }
end

lemma has_sum_of_has_sum_norm [normed_group α] [complete_space α] {f : ι → α}
  (hf : has_sum (λa, norm (f a))) : has_sum f :=
has_sum_iff_cauchy.2 $ assume ε hε,
  let ⟨s, hs⟩ := has_sum_iff_cauchy.1 hf ε hε in
  ⟨s, assume t ht,
    have ∥t.sum (λa, ∥f a∥)∥ < ε := hs t ht,
    have nn : 0 ≤ t.sum (λa, ∥f a∥) := finset.zero_le_sum (assume a _, norm_nonneg _),
    lt_of_le_of_lt (norm_triangle_sum t f) $ by rwa [real.norm_eq_abs, abs_of_nonneg nn] at this⟩

lemma has_sum_of_absolute_convergence_real {f : ℕ → ℝ} (hf : ∀n, 0 ≤ f n) :
  (∃r, tendsto (λn, (range n).sum (λi, abs (f i))) at_top (nhds r)) → has_sum f
| ⟨r, hr⟩ :=
  begin
    refine has_sum_of_has_sum_norm ⟨r, (is_sum_iff_tendsto_nat_of_nonneg _ _).2 _⟩,
    exact assume i, norm_nonneg _,
    simpa only using hr
  end

lemma tendsto_pow_at_top_at_top_of_gt_1 {r : ℝ} (h : r > 1) : tendsto (λn:ℕ, r ^ n) at_top at_top :=
tendsto_infi.2 $ assume p, tendsto_principal.2 $
  let ⟨n, hn⟩ := exists_nat_gt (p / (r - 1)) in
  have hn_nn : (0:ℝ) ≤ n, from nat.cast_nonneg n,
  have r - 1 > 0, from sub_lt_iff_lt_add.mp $ by simp; assumption,
  have p ≤ r ^ n,
    from calc p = (p / (r - 1)) * (r - 1) : (div_mul_cancel _ $ ne_of_gt this).symm
      ... ≤ n * (r - 1) : mul_le_mul (le_of_lt hn) (le_refl _) (le_of_lt this) hn_nn
      ... ≤ 1 + n * (r - 1) : le_add_of_nonneg_of_le zero_le_one (le_refl _)
      ... = 1 + add_monoid.smul n (r - 1) : by rw [add_monoid.smul_eq_mul]
      ... ≤ (1 + (r - 1)) ^ n : pow_ge_one_add_mul (le_of_lt this) _
      ... ≤ r ^ n : by simp; exact le_refl _,
  show {n | p ≤ r ^ n} ∈ at_top.sets,
    from mem_at_top_sets.mpr ⟨n, assume m hnm, le_trans this (pow_le_pow (le_of_lt h) hnm)⟩

lemma tendsto_inverse_at_top_nhds_0 : tendsto (λr:ℝ, r⁻¹) at_top (nhds 0) :=
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
  tendsto (λn:ℕ, r^n) at_top (nhds 0) :=
by_cases
  (assume : r = 0, (tendsto_add_at_top_iff_nat 1).mp $ by simp [pow_succ, this, tendsto_const_nhds])
  (assume : r ≠ 0,
    have tendsto (λn, (r⁻¹ ^ n)⁻¹) at_top (nhds 0),
      from (tendsto_pow_at_top_at_top_of_gt_1 $ one_lt_inv (lt_of_le_of_ne h₁ this.symm) h₂).comp
        tendsto_inverse_at_top_nhds_0,
    tendsto_cong this $ univ_mem_sets' $ by simp *)

lemma tendsto_pow_at_top_at_top_of_gt_1_nat {k : ℕ} (h : 1 < k) :
  tendsto (λn:ℕ, k ^ n) at_top at_top :=
tendsto_coe_nat_real_at_top_iff.1 $
  have hr : 1 < (k : ℝ), by rw [← nat.cast_one, nat.cast_lt]; exact h,
  by simpa using tendsto_pow_at_top_at_top_of_gt_1 hr

lemma tendsto_inverse_at_top_nhds_0_nat : tendsto (λ n : ℕ, (n : ℝ)⁻¹) at_top (nhds 0) :=
tendsto.comp (tendsto_coe_nat_real_at_top_iff.2 tendsto_id) tendsto_inverse_at_top_nhds_0

lemma tendsto_one_div_at_top_nhds_0_nat : tendsto (λ n : ℕ, 1/(n : ℝ)) at_top (nhds 0) :=
by simpa only [inv_eq_one_div] using tendsto_inverse_at_top_nhds_0_nat

lemma tendsto_one_div_add_at_top_nhds_0_nat :
  tendsto (λ n : ℕ, 1 / ((n : ℝ) + 1)) at_top (nhds 0) :=
suffices tendsto (λ n : ℕ, 1 / (↑(n + 1) : ℝ)) at_top (nhds 0), by simpa,
(tendsto_add_at_top_iff_nat 1).2 tendsto_one_div_at_top_nhds_0_nat

lemma is_sum_geometric {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  is_sum (λn:ℕ, r ^ n) (1 / (1 - r)) :=
have r ≠ 1, from ne_of_lt h₂,
have r + -1 ≠ 0,
  by rw [←sub_eq_add_neg, ne, sub_eq_iff_eq_add]; simp; assumption,
have tendsto (λn, (r ^ n - 1) * (r - 1)⁻¹) at_top (nhds ((0 - 1) * (r - 1)⁻¹)),
  from tendsto_mul
    (tendsto_sub (tendsto_pow_at_top_nhds_0_of_lt_1 h₁ h₂) tendsto_const_nhds) tendsto_const_nhds,
(is_sum_iff_tendsto_nat_of_nonneg (pow_nonneg h₁) _).mpr $
  by simp [neg_inv, geom_sum, div_eq_mul_inv, *] at *

lemma is_sum_geometric_two (a : ℝ) : is_sum (λn:ℕ, (a / 2) / 2 ^ n) a :=
begin
  convert is_sum_mul_left (a / 2) (is_sum_geometric
    (le_of_lt one_half_pos) one_half_lt_one),
  { funext n, simp,
    rw ← pow_inv; [refl, exact two_ne_zero] },
  { norm_num, rw div_mul_cancel _ two_ne_zero }
end

def pos_sum_of_encodable {ε : ℝ} (hε : 0 < ε)
  (ι) [encodable ι] : {ε' : ι → ℝ // (∀ i, 0 < ε' i) ∧ ∃ c, is_sum ε' c ∧ c ≤ ε} :=
begin
  let f := λ n, (ε / 2) / 2 ^ n,
  have hf : is_sum f ε := is_sum_geometric_two _,
  have f0 : ∀ n, 0 < f n := λ n, div_pos (half_pos hε) (pow_pos two_pos _),
  refine ⟨f ∘ encodable.encode, λ i, f0 _, _⟩,
  let g : ℕ → ℝ := λ n, option.cases_on (encodable.decode2 ι n) 0 (f ∘ encodable.encode),
  have : ∀ n, g n = 0 ∨ g n = f n,
  { intro n, dsimp [g], cases e : encodable.decode2 ι n with a,
    { exact or.inl rfl },
    { simp [encodable.mem_decode2.1 e] } },
  cases has_sum_of_has_sum_of_sub ⟨_, hf⟩ this with c hg,
  have cε : c ≤ ε,
  { refine is_sum_le (λ n, _) hg hf,
    cases this n; rw h, exact le_of_lt (f0 _) },
  have hs : ∀ n, g n ≠ 0 → (encodable.decode2 ι n).is_some,
  { intros n h, dsimp [g] at h,
    cases encodable.decode2 ι n,
    exact (h rfl).elim, exact rfl },
  refine ⟨c, _, cε⟩,
  refine is_sum_of_is_sum_ne_zero
    (λ n h, option.get (hs n h)) (λ n _, ne_of_gt (f0 _))
    (λ i _, encodable.encode i) (λ n h, ne_of_gt _)
    (λ n h, _) (λ i _, _) (λ i _, _) hg,
  { dsimp [g], rw encodable.encodek2, exact f0 _ },
  { exact encodable.mem_decode2.1 (option.get_mem _) },
  { exact option.get_of_mem _ (encodable.encodek2 _) },
  { dsimp [g], rw encodable.encodek2 }
end

namespace nnreal

theorem exists_pos_sum_of_encodable {ε : nnreal} (hε : 0 < ε) (ι) [encodable ι] :
  ∃ ε' : ι → nnreal, (∀ i, 0 < ε' i) ∧ ∃c, is_sum ε' c ∧ c < ε :=
let ⟨a, a0, aε⟩ := dense hε in
let ⟨ε', hε', c, hc, hcε⟩ := pos_sum_of_encodable a0 ι in
⟨ λi, ⟨ε' i, le_of_lt $ hε' i⟩, assume i, nnreal.coe_lt.2 $ hε' i,
  ⟨c, is_sum_le (assume i, le_of_lt $ hε' i) is_sum_zero hc ⟩, nnreal.is_sum_coe.1 hc,
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

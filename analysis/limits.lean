/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

A collection of limit properties.
-/
import algebra.big_operators algebra.group_power
  analysis.metric_space analysis.topology.infinite_sum
noncomputable theory
open classical set finset function filter
local attribute [instance] decidable_inhabited prop_decidable

infix ` ^ ` := pow_nat

section real

lemma has_sum_of_absolute_convergence {f : ℕ → ℝ}
  (hf : ∃r, tendsto (λn, (range n).sum (λi, abs (f i))) at_top (nhds r)) : has_sum f :=
let f' := λs:finset ℕ, s.sum (λi, abs (f i)) in
suffices cauchy (map (λs:finset ℕ, s.sum f) at_top),
  from complete_space.complete this,
cauchy_iff.mpr $ and.intro (map_ne_bot at_top_ne_bot) $
assume s hs,
let ⟨ε, hε, hsε⟩ := mem_uniformity_dist.mp hs, ⟨r, hr⟩ := hf in
have hε' : {p : ℝ × ℝ | dist p.1 p.2 < ε / 2} ∈ (@uniformity ℝ _).sets,
  from mem_uniformity_dist.mpr ⟨ε / 2, div_pos_of_pos_of_pos hε two_pos, assume a b h, h⟩,
have cauchy (at_top.map $ λn, f' (range n)),
  from cauchy_downwards cauchy_nhds (map_ne_bot at_top_ne_bot) hr,
have ∃n, ∀{n'}, n ≤ n' → dist (f' (range n)) (f' (range n')) < ε / 2,
  by simp [cauchy_iff, mem_at_top_iff] at this;
  from let ⟨t, ht, u, hu⟩ := this _ hε' in
    ⟨u, assume n' hn, ht $ prod_mk_mem_set_prod_eq.mpr ⟨hu _ (le_refl _), hu _ hn⟩⟩,
let ⟨n, hn⟩ := this in
have ∀{s}, range n ⊆ s → abs ((s \ range n).sum f) < ε / 2,
  from assume s hs,
  let ⟨n', hn'⟩ := @exists_nat_subset_range s in
  have range n ⊆ range n', from subset.trans hs hn',
  have f'_nn : 0 ≤ f' (range n' \ range n), from zero_le_sum $ assume _ _, abs_nonneg _,
  calc abs ((s \ range n).sum f) ≤ f' (s \ range n) : abs_sum_le_sum_abs
    ... ≤ f' (range n' \ range n) : sum_le_sum_of_subset_of_nonneg
      (finset.sdiff_subset_sdiff hn' (finset.subset.refl _))
      (assume _ _ _, abs_nonneg _)
    ... = abs (f' (range n' \ range n)) : (abs_of_nonneg f'_nn).symm
    ... = abs (f' (range n') - f' (range n)) :
      by simp [f', (sum_sdiff ‹range n ⊆ range n'›).symm]
    ... = abs (f' (range n) - f' (range n')) : abs_sub _ _
    ... < ε / 2 : hn $ range_subset.mp this,
have ∀{s t}, range n ⊆ s → range n ⊆ t → dist (s.sum f) (t.sum f) < ε,
  from assume s t hs ht,
  calc abs (s.sum f - t.sum f) = abs ((s \ range n).sum f + - (t \ range n).sum f) :
      by rw [←sum_sdiff hs, ←sum_sdiff ht]; simp
    ... ≤ abs ((s \ range n).sum f) + abs ((t \ range n).sum f) :
      le_trans (abs_add_le_abs_add_abs _ _) $ by rw [abs_neg]; exact le_refl _
    ... < ε / 2 + ε / 2 : add_lt_add (this hs) (this ht)
    ... = ε : by rw [←add_div, add_self_div_two],
⟨(λs:finset ℕ, s.sum f) '' {s | range n ⊆ s}, image_mem_map $ mem_at_top (range n),
  assume ⟨a, b⟩ ⟨⟨t, ht, ha⟩, ⟨s, hs, hb⟩⟩, by simp at ha hb; exact ha ▸ hb ▸ hsε _ _ (this ht hs)⟩

lemma is_sum_iff_tendsto_nat_of_nonneg {f : ℕ → ℝ} {r : ℝ} (hf : ∀n, 0 ≤ f n) :
  is_sum f r ↔ tendsto (λn, (range n).sum f) at_top (nhds r) :=
⟨tendsto_sum_nat_of_is_sum,
  assume hr,
  have tendsto (λn, (range n).sum (λn, abs (f n))) at_top (nhds r),
    by simp [(λi, abs_of_nonneg (hf i)), hr],
  let ⟨p, h⟩ := has_sum_of_absolute_convergence ⟨r, this⟩ in
  have hp : tendsto (λn, (range n).sum f) at_top (nhds p), from tendsto_sum_nat_of_is_sum h,
  have p = r, from tendsto_nhds_unique at_top_ne_bot hp hr,
  this ▸ h⟩

end real

lemma mul_add_one_le_pow {r : ℝ} (hr : 0 ≤ r) : ∀{n:ℕ}, (n:ℝ) * r + 1 ≤ (r + 1) ^ n
| 0       := by simp; exact le_refl 1
| (n + 1) :=
  let h : (n:ℝ) ≥ 0 := nat.cast_nonneg n in
  calc ↑(n + 1) * r + 1 ≤ ((n + 1) * r + 1) + r * r * n :
      le_add_of_le_of_nonneg (le_refl _) (mul_nonneg (mul_nonneg hr hr) h)
    ... = (r + 1) * (n * r + 1) : by simp [mul_add, add_mul]
    ... ≤ (r + 1) * (r + 1) ^ n : mul_le_mul (le_refl _) mul_add_one_le_pow
      (add_nonneg (mul_nonneg h hr) zero_le_one) (add_nonneg hr zero_le_one)

lemma tendsto_pow_at_top_at_top_of_gt_1 {r : ℝ} (h : r > 1) : tendsto (λn:ℕ, r ^ n) at_top at_top :=
tendsto_infi $ assume p, tendsto_principal $
  let ⟨n, hn⟩ := @exists_lt_nat (p / (r - 1)) in
  have hn_nn : (0:ℝ) ≤ n, from nat.cast_nonneg n,
  have r - 1 > 0, from sub_lt_iff.mp $ by simp; assumption,
  have p ≤ r ^ n,
    from calc p = (p / (r - 1)) * (r - 1) : (div_mul_cancel _ $ ne_of_gt this).symm
      ... ≤ n * (r - 1) : mul_le_mul (le_of_lt hn) (le_refl _) (le_of_lt this) hn_nn
      ... ≤ n * (r - 1) + 1 : le_add_of_le_of_nonneg (le_refl _) zero_le_one
      ... ≤ ((r - 1) + 1) ^ n : mul_add_one_le_pow $ le_of_lt this
      ... ≤ r ^ n : by simp; exact le_refl _,
  show {n | p ≤ r ^ n} ∈ at_top.sets,
    from mem_at_top_iff.mpr ⟨n, assume m hnm, le_trans this (pow_le_pow (le_of_lt h) hnm)⟩

lemma tendsto_inverse_at_top_nhds_0 : tendsto (λr:ℝ, r⁻¹) at_top (nhds 0) :=
tendsto_orderable_unbounded (no_top 0) (no_bot 0) $ assume l u hl hu,
  mem_at_top_iff.mpr ⟨u⁻¹ + 1, assume b hb,
    have u⁻¹ < b, from lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one) hb,
    ⟨lt_trans hl $ inv_pos $ lt_trans (inv_pos hu) this,
    lt_of_one_div_lt_one_div hu $
    begin
      rw [inv_eq_one_div],
      simp [-one_div_eq_inv, div_div_eq_mul_div, div_one],
      simp [this]
    end⟩⟩

lemma map_succ_at_top_eq : map nat.succ at_top = at_top :=
le_antisymm
  (assume s hs,
    let ⟨b, hb⟩ := mem_at_top_iff.mp hs in
    mem_at_top_iff.mpr ⟨b, assume c hc, hb (c + 1) $ le_trans hc $ nat.le_succ _⟩)
  (assume s hs,
    let ⟨b, hb⟩ := mem_at_top_iff.mp hs in
    mem_at_top_iff.mpr ⟨b + 1, assume c,
    match c with
    | 0     := assume h,
      have 0 > 0, from lt_of_lt_of_le (lt_add_of_le_of_pos (nat.zero_le _) zero_lt_one) h,
      (lt_irrefl 0 this).elim
    | (c+1) := assume h, hb _ (nat.le_of_succ_le_succ h)
    end⟩)

lemma tendsto_comp_succ_at_top_iff {α : Type*} {f : ℕ → α} {x : filter α} :
  tendsto (λn, f (nat.succ n)) at_top x ↔ tendsto f at_top x :=
calc tendsto (f ∘ nat.succ) at_top x ↔ tendsto f (map nat.succ at_top) x : by simp [tendsto, map_map]
 ... ↔ _ : by rw [map_succ_at_top_eq]

lemma tendsto_pow_at_top_nhds_0_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  tendsto (λn, r^n) at_top (nhds 0) :=
by_cases
  (assume : r = 0, tendsto_comp_succ_at_top_iff.mp $ by simp [pow_succ, this, tendsto_const_nhds])
  (assume : r ≠ 0,
    have tendsto (λn, (r⁻¹ ^ n)⁻¹) at_top (nhds 0),
      from tendsto_compose
        (tendsto_pow_at_top_at_top_of_gt_1 $ one_lt_inv (lt_of_le_of_ne h₁ this.symm) h₂)
        tendsto_inverse_at_top_nhds_0,
    tendsto_cong this $ univ_mem_sets' $ assume a, by simp [*, pow_inv])

lemma sum_geometric' {r : ℝ} (h : r ≠ 0) :
  ∀{n}, (finset.range n).sum (λi, (r + 1) ^ i) = ((r + 1) ^ n - 1) / r
| 0     := by simp [zero_div]
| (n+1) := by simp [@sum_geometric' n, h, pow_succ, add_div_eq_mul_add_div, add_mul]

lemma sum_geometric {r : ℝ} {n : ℕ} (h : r ≠ 1) :
  (range n).sum (λi, r ^ i) = (r ^ n - 1) / (r - 1) :=
calc (range n).sum (λi, r ^ i) = (range n).sum (λi, ((r - 1) + 1) ^ i) :
    by simp
  ... = (((r - 1) + 1) ^ n - 1) / (r - 1) :
    sum_geometric' $ by simp [sub_eq_iff_eq_add, -sub_eq_add_neg, h]
  ... = (r ^ n - 1) / (r - 1) :
    by simp

lemma is_sum_geometric {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  is_sum (λn, r ^ n) (1 / (1 - r)) :=
have r ≠ 1, from ne_of_lt h₂,
have r + -1 ≠ 0,
  by rw [←sub_eq_add_neg, ne, sub_eq_iff_eq_add]; simp; assumption,
have tendsto (λn, (r ^ n - 1) * (r - 1)⁻¹) at_top (nhds ((0 - 1) * (r - 1)⁻¹)),
  from tendsto_mul
    (tendsto_sub (tendsto_pow_at_top_nhds_0_of_lt_1 h₁ h₂) tendsto_const_nhds) tendsto_const_nhds,
(is_sum_iff_tendsto_nat_of_nonneg $ pow_nonneg h₁).mpr $
  by simp [neg_inv, sum_geometric, div_eq_mul_inv, *] at *

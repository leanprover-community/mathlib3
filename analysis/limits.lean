/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

A collection of limit properties.
-/
import algebra.big_operators algebra.group_power tactic.norm_num
  analysis.ennreal analysis.topology.infinite_sum
noncomputable theory
open classical finset function filter
local attribute [instance] prop_decidable

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
  by simp [cauchy_iff, mem_at_top_sets] at this;
  from let ⟨t, ⟨u, hu⟩, ht⟩ := this _ hε' in
    ⟨u, assume n' hn, ht $ set.prod_mk_mem_set_prod_eq.mpr ⟨hu _ (le_refl _), hu _ hn⟩⟩,
let ⟨n, hn⟩ := this in
have ∀{s}, range n ⊆ s → abs ((s \ range n).sum f) < ε / 2,
  from assume s hs,
  let ⟨n', hn'⟩ := @exists_nat_subset_range s in
  have range n ⊆ range n', from finset.subset.trans hs hn',
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
  assume ⟨a, b⟩ ⟨⟨t, ht, ha⟩, ⟨s, hs, hb⟩⟩, by simp at ha hb; exact ha ▸ hb ▸ hsε (this ht hs)⟩

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
    ... = (r + 1) * (n * r + 1) : by simp [mul_add, add_mul, mul_comm, mul_assoc]
    ... ≤ (r + 1) * (r + 1) ^ n : mul_le_mul (le_refl _) mul_add_one_le_pow
      (add_nonneg (mul_nonneg h hr) zero_le_one) (add_nonneg hr zero_le_one)

lemma tendsto_pow_at_top_at_top_of_gt_1 {r : ℝ} (h : r > 1) : tendsto (λn:ℕ, r ^ n) at_top at_top :=
tendsto_infi.2 $ assume p, tendsto_principal.2 $
  let ⟨n, hn⟩ := exists_nat_gt (p / (r - 1)) in
  have hn_nn : (0:ℝ) ≤ n, from nat.cast_nonneg n,
  have r - 1 > 0, from sub_lt_iff_lt_add.mp $ by simp; assumption,
  have p ≤ r ^ n,
    from calc p = (p / (r - 1)) * (r - 1) : (div_mul_cancel _ $ ne_of_gt this).symm
      ... ≤ n * (r - 1) : mul_le_mul (le_of_lt hn) (le_refl _) (le_of_lt this) hn_nn
      ... ≤ n * (r - 1) + 1 : le_add_of_le_of_nonneg (le_refl _) zero_le_one
      ... ≤ ((r - 1) + 1) ^ n : mul_add_one_le_pow $ le_of_lt this
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

lemma map_succ_at_top_eq : map nat.succ at_top = at_top :=
le_antisymm
  (assume s hs,
    let ⟨b, hb⟩ := mem_at_top_sets.mp hs in
    mem_at_top_sets.mpr ⟨b, assume c hc, hb (c + 1) $ le_trans hc $ nat.le_succ _⟩)
  (assume s hs,
    let ⟨b, hb⟩ := mem_at_top_sets.mp hs in
    mem_at_top_sets.mpr ⟨b + 1, assume c,
    match c with
    | 0     := assume h,
      have 0 > 0, from lt_of_lt_of_le (lt_add_of_le_of_pos (nat.zero_le _) zero_lt_one) h,
      (lt_irrefl 0 this).elim
    | (c+1) := assume h, hb _ (nat.le_of_succ_le_succ h)
    end⟩)

lemma tendsto_comp_succ_at_top_iff {α : Type*} {f : ℕ → α} {x : filter α} :
  tendsto (λn, f (nat.succ n)) at_top x ↔ tendsto f at_top x :=
calc tendsto (f ∘ nat.succ) at_top x ↔ tendsto f (map nat.succ at_top) x : by simp [tendsto, filter.map_map]
 ... ↔ _ : by rw [map_succ_at_top_eq]

lemma tendsto_pow_at_top_nhds_0_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  tendsto (λn:ℕ, r^n) at_top (nhds 0) :=
by_cases
  (assume : r = 0, tendsto_comp_succ_at_top_iff.mp $ by simp [pow_succ, this, tendsto_const_nhds])
  (assume : r ≠ 0,
    have tendsto (λn, (r⁻¹ ^ n)⁻¹) at_top (nhds 0),
      from (tendsto_pow_at_top_at_top_of_gt_1 $ one_lt_inv (lt_of_le_of_ne h₁ this.symm) h₂).comp
        tendsto_inverse_at_top_nhds_0,
    tendsto_cong this $ univ_mem_sets' $ by simp *)

lemma tendsto_coe_iff {f : ℕ → ℕ} : tendsto (λ n, (f n : ℝ)) at_top at_top ↔ tendsto f at_top at_top :=
⟨ λ h, tendsto_infi.2 $ λ i, tendsto_principal.2
    (have _, from tendsto_infi.1 h i, by simpa using tendsto_principal.1 this),
  λ h, tendsto.comp h tendsto_of_nat_at_top_at_top ⟩

lemma tendsto_pow_at_top_at_top_of_gt_1_nat {k : ℕ} (h : 1 < k) : tendsto (λn:ℕ, k ^ n) at_top at_top :=
tendsto_coe_iff.1 $
  have hr : 1 < (k : ℝ), by rw [← nat.cast_one, nat.cast_lt]; exact h,
  by simpa using tendsto_pow_at_top_at_top_of_gt_1 hr

lemma tendsto_inverse_at_top_nhds_0_nat : tendsto (λ n : ℕ, (n : ℝ)⁻¹) at_top (nhds 0) :=
tendsto.comp (tendsto_coe_iff.2 tendsto_id) tendsto_inverse_at_top_nhds_0

lemma tendsto_one_div_at_top_nhds_0_nat : tendsto (λ n : ℕ, 1/(n : ℝ)) at_top (nhds 0) :=
by simpa only [inv_eq_one_div] using tendsto_inverse_at_top_nhds_0_nat

lemma sum_geometric' {r : ℝ} (h : r ≠ 0) :
  ∀{n}, (finset.range n).sum (λi, (r + 1) ^ i) = ((r + 1) ^ n - 1) / r
| 0     := by simp [zero_div]
| (n+1) :=
  by simp [@sum_geometric' n, h, pow_succ, add_div_eq_mul_add_div, add_mul, mul_comm, mul_assoc]

lemma sum_geometric {r : ℝ} {n : ℕ} (h : r ≠ 1) :
  (range n).sum (λi, r ^ i) = (r ^ n - 1) / (r - 1) :=
calc (range n).sum (λi, r ^ i) = (range n).sum (λi, ((r - 1) + 1) ^ i) :
    by simp
  ... = (((r - 1) + 1) ^ n - 1) / (r - 1) :
    sum_geometric' $ by simp [sub_eq_iff_eq_add, -sub_eq_add_neg, h]
  ... = (r ^ n - 1) / (r - 1) :
    by simp

lemma is_sum_geometric {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  is_sum (λn:ℕ, r ^ n) (1 / (1 - r)) :=
have r ≠ 1, from ne_of_lt h₂,
have r + -1 ≠ 0,
  by rw [←sub_eq_add_neg, ne, sub_eq_iff_eq_add]; simp; assumption,
have tendsto (λn, (r ^ n - 1) * (r - 1)⁻¹) at_top (nhds ((0 - 1) * (r - 1)⁻¹)),
  from tendsto_mul
    (tendsto_sub (tendsto_pow_at_top_nhds_0_of_lt_1 h₁ h₂) tendsto_const_nhds) tendsto_const_nhds,
(is_sum_iff_tendsto_nat_of_nonneg $ pow_nonneg h₁).mpr $
  by simp [neg_inv, sum_geometric, div_eq_mul_inv, *] at *

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
⟨ λi, ⟨ε' i, le_of_lt $ hε' i⟩, assume i, (nnreal.coe_lt _ _).2 $ hε' i,
  ⟨c, is_sum_le (assume i, le_of_lt $ hε' i) is_sum_zero hc ⟩, nnreal.is_sum_coe.1 hc,
   lt_of_le_of_lt ((nnreal.coe_le _ _).1 hcε) aε ⟩

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
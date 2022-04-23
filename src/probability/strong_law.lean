/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import probability.ident_distrib
import measure_theory.function.l2_space
import measure_theory.integral.interval_integral

open measure_theory filter finset

noncomputable theory

open_locale topological_space big_operators measure_theory probability_theory ennreal nnreal


section

variables {R : Type*} [linear_ordered_ring R] [floor_ring R]

lemma tendsto_nat_floor_at_top :
  tendsto (λ (x : R), ⌊x⌋₊) at_top at_top :=
begin
  apply tendsto_at_top.2 (λ n, _),
  filter_upwards [Ici_mem_at_top (n : R)] with x hx,
  exact nat.le_floor hx,
end

end


lemma tendsto_sub_nhds_zero_iff
  {α : Type*} {l : filter α} {E : Type*} [normed_group E] {x : E} {u : α → E} :
  tendsto u l (𝓝 x) ↔ tendsto (λ n, u n - x) l (𝓝 0) :=
begin
  have A : tendsto (λ (n : α), x) l (𝓝 x) := tendsto_const_nhds,
  exact ⟨λ h, by simpa using h.sub A, λ h, by simpa using h.add A⟩
end

/-- If a monotone sequence `u` is such that `u n / n` tends to a limit `l` along subsequences with
exponential growth arbitrarily close to `1`, then `u n / n` tends to `l`. -/
lemma flouk (u : ℕ → ℝ) (l : ℝ) (hmono : monotone u)
  (hlim : ∀ (a : ℝ), 1 < a → ∃ c : ℕ → ℕ, (∀ᶠ n in at_top, (c (n+1) : ℝ) ≤ a * c n) ∧
    tendsto c at_top at_top ∧ tendsto (λ n, u (c n) / (c n)) at_top (𝓝 l)) :
  tendsto (λ n, u n / n) at_top (𝓝 l) :=
begin
  have lnonneg : 0 ≤ l,
  sorry { rcases hlim 2 one_lt_two with ⟨c, cgrowth, ctop, clim⟩,
    have : tendsto (λ n, u 0 / (c n)) at_top (𝓝 0) :=
      tendsto_const_nhds.div_at_top (tendsto_coe_nat_at_top_iff.2 ctop),
    apply le_of_tendsto_of_tendsto' this clim (λ n, _),
    simp_rw [div_eq_inv_mul],
    apply mul_le_mul_of_nonneg_left (hmono (zero_le _)) (inv_nonneg.2 (nat.cast_nonneg _)) },
  have A : ∀ (ε : ℝ), 0 < ε → ∀ᶠ n in at_top, u n - n * l ≤ (ε * (1 + ε + l)) * n,
  sorry { assume ε εpos,
    rcases hlim (1 + ε) ((lt_add_iff_pos_right _).2 εpos) with ⟨c, cgrowth, ctop, clim⟩,
    have L : ∀ᶠ n in at_top, u (c n) - c n * l ≤ ε * c n,
    { rw [tendsto_sub_nhds_zero_iff, ← asymptotics.is_o_one_iff ℝ, asymptotics.is_o_iff] at clim,
      filter_upwards [clim εpos, ctop (Ioi_mem_at_top 0)] with n hn cnpos',
      have cnpos : 0 < c n := cnpos',
      calc u (c n) - c n * l
      = (u (c n) / c n - l) * c n: by field_simp [cnpos.ne']
      ... ≤ ε * c n :
        begin
          apply mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _),
          simp only [mul_one, real.norm_eq_abs, abs_one] at hn,
          exact le_trans (le_abs_self _) hn,
        end },
    obtain ⟨a, ha⟩ : ∃ (a : ℕ), ∀ (b : ℕ), a ≤ b → (c (b + 1) : ℝ) ≤ (1 + ε) * c b
        ∧ u (c b) - c b * l ≤ ε * c b := eventually_at_top.1 (cgrowth.and L),
    let M := ((finset.range (a+1)).image (λ i, c i)).max' (by simp),
    filter_upwards [Ici_mem_at_top M] with n hn,
    have exN : ∃ N, n < c N,
    { rcases (tendsto_at_top.1 ctop (n+1)).exists with ⟨N, hN⟩,
      exact ⟨N, by linarith⟩ },
    let N := nat.find exN,
    have ncN : n < c N := nat.find_spec exN,
    have aN : a + 1 ≤ N,
    { by_contra' h,
      have cNM : c N ≤ M,
      { apply le_max',
        apply mem_image_of_mem,
        exact mem_range.2 h },
      exact lt_irrefl _ ((cNM.trans hn).trans_lt ncN) },
    have Npos : 0 < N := lt_of_lt_of_le (nat.succ_pos') aN,
    have cNn : c (N - 1) ≤ n,
    { have : N - 1 < N := nat.pred_lt Npos.ne',
      simpa only [not_lt] using nat.find_min exN this },
    have IcN : (c N : ℝ) ≤ (1 + ε) * (c (N - 1)),
    { have A : a ≤ N - 1, by linarith,
      have B : N - 1 + 1 = N := nat.succ_pred_eq_of_pos Npos,
      have := (ha _ A).1,
      rw B at this,
      linarith },
    calc u n - n * l ≤ u (c N) - c (N - 1) * l :
      begin
        apply sub_le_sub (hmono ncN.le),
        apply mul_le_mul_of_nonneg_right (nat.cast_le.2 cNn) lnonneg,
      end
    ... = (u (c N) - c N * l) + (c N - c (N - 1)) * l : by ring
    ... ≤ ε * c N + (ε * c (N - 1)) * l :
      begin
        apply add_le_add,
        { apply (ha _ _).2,
          exact le_trans (by simp only [le_add_iff_nonneg_right, zero_le']) aN },
        { apply mul_le_mul_of_nonneg_right _ lnonneg,
          linarith },
      end
    ... ≤ ε * ((1 + ε) * c (N-1)) + (ε * c (N - 1)) * l :
      add_le_add (mul_le_mul_of_nonneg_left IcN εpos.le) le_rfl
    ... = (ε * (1 + ε + l)) * c (N - 1) : by ring
    ... ≤ (ε * (1 + ε + l)) * n :
      begin
        refine mul_le_mul_of_nonneg_left (nat.cast_le.2 cNn) _,
        apply mul_nonneg εpos.le,
        linarith
      end },
  have B : ∀ (ε : ℝ), 0 < ε → ∀ᶠ (n : ℕ) in at_top, (n : ℝ) * l - u n ≤ (ε * (1 + l)) * n,
  sorry { assume ε εpos,
    rcases hlim (1 + ε) ((lt_add_iff_pos_right _).2 εpos) with ⟨c, cgrowth, ctop, clim⟩,
    have L : ∀ᶠ (n : ℕ) in at_top, (c n : ℝ) * l - u (c n) ≤ ε * c n,
    { rw [tendsto_sub_nhds_zero_iff, ← asymptotics.is_o_one_iff ℝ, asymptotics.is_o_iff] at clim,
      filter_upwards [clim εpos, ctop (Ioi_mem_at_top 0)] with n hn cnpos',
      have cnpos : 0 < c n := cnpos',
      calc (c n : ℝ) * l - u (c n)
      = -(u (c n) / c n - l) * c n: by field_simp [cnpos.ne']
      ... ≤ ε * c n :
        begin
          apply mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _),
          simp only [mul_one, real.norm_eq_abs, abs_one] at hn,
          exact le_trans (neg_le_abs_self _) hn,
        end },
    obtain ⟨a, ha⟩ : ∃ (a : ℕ), ∀ (b : ℕ), a ≤ b → (c (b + 1) : ℝ) ≤ (1 + ε) * c b
        ∧ (c b : ℝ) * l - u (c b) ≤ ε * c b := eventually_at_top.1 (cgrowth.and L),
    let M := ((finset.range (a+1)).image (λ i, c i)).max' (by simp),
    filter_upwards [Ici_mem_at_top M] with n hn,
    have exN : ∃ N, n < c N,
    { rcases (tendsto_at_top.1 ctop (n+1)).exists with ⟨N, hN⟩,
      exact ⟨N, by linarith⟩ },
    let N := nat.find exN,
    have ncN : n < c N := nat.find_spec exN,
    have aN : a + 1 ≤ N,
    { by_contra' h,
      have cNM : c N ≤ M,
      { apply le_max',
        apply mem_image_of_mem,
        exact mem_range.2 h },
      exact lt_irrefl _ ((cNM.trans hn).trans_lt ncN) },
    have Npos : 0 < N := lt_of_lt_of_le (nat.succ_pos') aN,
    have aN' : a ≤ N - 1 := by linarith,
    have cNn : c (N - 1) ≤ n,
    { have : N - 1 < N := nat.pred_lt Npos.ne',
      simpa only [not_lt] using nat.find_min exN this },
    calc (n : ℝ) * l - u n ≤ c N * l - u (c (N - 1)) :
      begin
        refine add_le_add (mul_le_mul_of_nonneg_right (nat.cast_le.2 ncN.le) lnonneg) _,
        exact neg_le_neg (hmono cNn),
      end
    ... ≤ ((1 + ε) * c (N - 1)) * l - u (c (N - 1)) :
      begin
        refine add_le_add (mul_le_mul_of_nonneg_right _ lnonneg) le_rfl,
        have B : N - 1 + 1 = N := nat.succ_pred_eq_of_pos Npos,
        have := (ha _ aN').1,
        rw B at this,
        linarith
      end
    ... = (c (N - 1) * l - u (c (N - 1))) + ε * c (N - 1) * l : by ring
    ... ≤ ε * c (N - 1) + ε * c (N - 1) * l :
      add_le_add (ha _ aN').2 le_rfl
    ... = (ε * (1 + l)) * c (N - 1) : by ring
    ... ≤ (ε * (1 + l)) * n :
      begin
        refine mul_le_mul_of_nonneg_left (nat.cast_le.2 cNn) _,
        exact mul_nonneg (εpos.le) (add_nonneg zero_le_one lnonneg),
      end },
  refine tendsto_order.2 ⟨λ d hd, _, λ d hd, _⟩,
  {

  },
  sorry { obtain ⟨ε, hε, εpos⟩ : ∃ (ε : ℝ), l + ε * (1 + ε + l) < d ∧ 0 < ε,
    { have L : tendsto (λ ε, l + (ε * (1 + ε + l))) (𝓝[>] 0) (𝓝 (l + 0 * (1 + 0 + l))),
      { apply tendsto.mono_left _ nhds_within_le_nhds,
        exact tendsto_const_nhds.add
          (tendsto_id.mul ((tendsto_const_nhds.add tendsto_id).add tendsto_const_nhds)) },
      simp only [zero_mul, add_zero] at L,
      exact (((tendsto_order.1 L).2 d hd).and (self_mem_nhds_within)).exists },
    filter_upwards [A ε εpos, Ioi_mem_at_top 0] with n hn npos,
    simp_rw [div_eq_inv_mul],
    calc (n : ℝ)⁻¹ * u n ≤ (n : ℝ)⁻¹ * (n * l + ε * (1 + ε + l) * n) :
      begin
        refine mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (nat.cast_nonneg _)),
        linarith,
      end
    ... = ((n : ℝ) ⁻¹ * n) * (l + ε * (1 + ε + l)) : by ring
    ... < d :
      begin
        rwa [inv_mul_cancel, one_mul],
        exact nat.cast_ne_zero.2 (ne_of_gt npos),
      end }
end


#exit

#check Ico_union_Ico_eq_Ico

-- a placer pres de ...
@[simp] lemma Ioc_union_Ioc_eq_Ioc {α : Type*} [linear_order α] [locally_finite_order α]
  {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) :
  Ioc a b ∪ Ioc b c = Ioc a c :=
by rw [←coe_inj, coe_union, coe_Ioc, coe_Ioc, coe_Ioc, set.Ioc_union_Ioc_eq_Ioc h₁ h₂]


#check prod_Ico_consecutive

@[to_additive]
lemma prod_Ioc_consecutive {β : Type*} [comm_monoid β]
  (f : ℕ → β) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
  (∏ i in Ioc m n, f i) * (∏ i in Ioc n k, f i) = (∏ i in Ioc m k, f i) :=
begin
  rw [← Ioc_union_Ioc_eq_Ioc hmn hnk, prod_union],
  apply disjoint_left.2 (λ x hx h'x, _),
  exact lt_irrefl _ ((mem_Ioc.1 h'x).1.trans_le (mem_Ioc.1 hx).2),
end

@[simp] lemma Ioc_self_succ (b : ℕ) : Ioc b b.succ = {b+1} :=
by rw [← nat.Icc_succ_left, Icc_self]

@[to_additive]
lemma prod_Ioc_succ_top {β : Type*} [comm_monoid β] {a b : ℕ} (hab : a ≤ b) (f : ℕ → β) :
  (∏ k in Ioc a (b + 1), f k) = (∏ k in Ioc a b, f k) * f (b + 1) :=
by rw [← prod_Ioc_consecutive _ hab (nat.le_succ b), Ioc_self_succ, prod_singleton]

lemma sum_Ioc_div_sq_le_sub {α : Type*} [linear_ordered_field α] {k n : ℕ} (hk : k ≠ 0) (h : k ≤ n) :
  ∑ i in Ioc k n, (1 : α) / i ^ 2 ≤ 1 / k - 1 / n :=
begin
  refine nat.le_induction _ _ n h,
  { simp only [Ioc_self, sum_empty, sub_self] },
  assume n hn IH,
  rw [sum_Ioc_succ_top hn],
  apply (add_le_add IH le_rfl).trans,
  simp only [sub_eq_add_neg, add_assoc, nat.cast_add, nat.cast_one, le_add_neg_iff_add_le,
    add_le_iff_nonpos_right, neg_add_le_iff_le_add, add_zero],
  have A : 0 < (n : α), by simpa using hk.bot_lt.trans_le hn,
  have B : 0 < (n : α) + 1, by linarith,
  field_simp [B.ne'],
  rw [div_le_div_iff _ A, ← sub_nonneg],
  { ring_nf, exact B.le },
  { nlinarith },
end

lemma sum_Ioo_div_sq_le {α : Type*} [linear_ordered_field α] (k n : ℕ) :
  ∑ i in Ioo k n, (1 : α) / i ^ 2 ≤ 2 / (k + 1) :=
calc
∑ i in Ioo k n, (1 : α) / i ^ 2 ≤ ∑ i in Ioc k (max (k+1) n), 1 / i ^ 2 :
begin
  apply sum_le_sum_of_subset_of_nonneg,
  { assume x hx,
    simp only [mem_Ioo] at hx,
    simp only [hx, hx.2.le, mem_Ioc, le_max_iff, or_true, and_self] },
  { assume i hi hident,
    exact div_nonneg zero_le_one (sq_nonneg _), }
end
... ≤ 1 / (k + 1) ^ 2 + ∑ i in Ioc k.succ (max (k + 1) n), 1 / i ^ 2 :
begin
  rw [← nat.Icc_succ_left, ← nat.Ico_succ_right, sum_eq_sum_Ico_succ_bot],
  swap, { exact nat.succ_lt_succ ((nat.lt_succ_self k).trans_le (le_max_left _ _)) },
  rw [nat.Ico_succ_right, nat.Icc_succ_left, nat.cast_succ],
end
... ≤ 1 / (k + 1) ^ 2 + 1 / (k + 1) :
begin
  refine add_le_add le_rfl ((sum_Ioc_div_sq_le_sub _ (le_max_left _ _)).trans _),
  { simp only [ne.def, nat.succ_ne_zero, not_false_iff] },
  { simp only [nat.cast_succ, one_div, sub_le_self_iff, inv_nonneg, nat.cast_nonneg] }
end
... ≤ 1 / (k + 1) + 1 / (k + 1) :
begin
  have A : (1 : α) ≤ k + 1, by simp only [le_add_iff_nonneg_left, nat.cast_nonneg],
  apply add_le_add_right,
  refine div_le_div zero_le_one le_rfl (zero_lt_one.trans_le A) _,
  simpa using pow_le_pow A one_le_two,
end
... = 2 / (k + 1) : by ring

namespace asymptotics

lemma is_o.sum_range {α : Type*} [normed_group α]
  {f : ℕ → α} {g : ℕ → ℝ} (h : is_o f g at_top)
  (hg : 0 ≤ g) (h'g : tendsto (λ n, ∑ i in range n, g i) at_top at_top) :
  is_o (λ n, ∑ i in range n, f i) (λ n, ∑ i in range n, g i) at_top :=
begin
  have A : ∀ i, ∥g i∥ = g i := λ i, real.norm_of_nonneg (hg i),
  have B : ∀ n, ∥∑ i in range n, g i∥ = ∑ i in range n, g i,
  { assume n,
    rw [real.norm_eq_abs, abs_sum_of_nonneg'],
    exact hg },
  apply is_o_iff.2 (λ ε εpos, _),
  obtain ⟨N, hN⟩ : ∃ (N : ℕ), ∀ (b : ℕ), N ≤ b → ∥f b∥ ≤ ε / 2 * g b,
    by simpa only [A, eventually_at_top] using is_o_iff.mp h (half_pos εpos),
  have : is_o (λ (n : ℕ), ∑ i in range N, f i) (λ (n : ℕ), ∑ i in range n, g i) at_top,
  { apply is_o_const_left.2,
    exact or.inr (h'g.congr (λ n, (B n).symm)) },
  filter_upwards [is_o_iff.1 this (half_pos εpos), Ici_mem_at_top N] with n hn Nn,
  calc ∥∑ i in range n, f i∥
  = ∥∑ i in range N, f i + ∑ i in Ico N n, f i∥ :
    by rw sum_range_add_sum_Ico _ Nn
  ... ≤ ∥∑ i in range N, f i∥ + ∥∑ i in Ico N n, f i∥ :
    norm_add_le _ _
  ... ≤ ∥∑ i in range N, f i∥ + ∑ i in Ico N n, (ε / 2) * g i :
    add_le_add le_rfl (norm_sum_le_of_le _ (λ i hi, hN _ (mem_Ico.1 hi).1))
  ... ≤ ∥∑ i in range N, f i∥ + ∑ i in range n, (ε / 2) * g i :
    begin
      refine add_le_add le_rfl _,
      apply sum_le_sum_of_subset_of_nonneg,
      { rw range_eq_Ico,
        exact Ico_subset_Ico (zero_le _) le_rfl },
      { assume i hi hident,
        exact mul_nonneg (half_pos εpos).le (hg i) }
    end
  ... ≤ (ε / 2) * ∥∑ i in range n, g i∥ + (ε / 2) * (∑ i in range n, g i) :
    begin
      rw ← mul_sum,
      exact add_le_add hn (mul_le_mul_of_nonneg_left le_rfl (half_pos εpos).le),
    end
  ... = ε * ∥(∑ i in range n, g i)∥ : by { simp [B], ring }
end

lemma is_o_sum_range_of_tendsto_zero {α : Type*} [normed_group α]
  {f : ℕ → α} (h : tendsto f at_top (𝓝 0)) :
  is_o (λ n, ∑ i in range n, f i) (λ n, (n : ℝ)) at_top :=
begin
  have := ((is_o_one_iff ℝ).2 h).sum_range (λ i, zero_le_one),
  simp only [sum_const, card_range, nat.smul_one_eq_coe] at this,
  exact this tendsto_coe_nat_at_top_at_top
end

end asymptotics

open asymptotics


/-- The Cesaro average of a converging sequence converges to the same limit. -/
lemma filter.tendsto.cesaro_smul {E : Type*} [normed_group E] [normed_space ℝ E]
  {u : ℕ → E} {l : E} (h : tendsto u at_top (𝓝 l)) :
  tendsto (λ (n : ℕ), (n ⁻¹ : ℝ) • (∑ i in range n, u i)) at_top (𝓝 l) :=
begin
  rw [tendsto_sub_nhds_zero_iff, ← is_o_one_iff ℝ],
  have := asymptotics.is_o_sum_range_of_tendsto_zero (tendsto_sub_nhds_zero_iff.1 h),
  apply ((is_O_refl (λ (n : ℕ), (n : ℝ) ⁻¹) at_top).smul_is_o this).congr' _ _,
  { filter_upwards [Ici_mem_at_top 1] with n npos,
    have nposℝ : (0 : ℝ) < n := nat.cast_pos.2 npos,
    simp only [smul_sub, sum_sub_distrib, sum_const, card_range, sub_right_inj],
    rw [nsmul_eq_smul_cast ℝ, smul_smul, inv_mul_cancel nposℝ.ne', one_smul] },
  { filter_upwards [Ici_mem_at_top 1] with n npos,
    have nposℝ : (0 : ℝ) < n := nat.cast_pos.2 npos,
    rw [algebra.id.smul_eq_mul, inv_mul_cancel nposℝ.ne'] }
end

lemma filter.tendsto.cesaro
  {u : ℕ → ℝ} {l : ℝ} (h : tendsto u at_top (𝓝 l)) :
  tendsto (λ (n : ℕ), (n ⁻¹ : ℝ) * (∑ i in range n, u i)) at_top (𝓝 l) :=
h.cesaro_smul


lemma neg_abs_le_neg (a : ℝ) : -|a| ≤ -a :=
by simp [le_abs_self]

open set (indicator)

namespace probability_theory

section truncation

variables {α : Type*}

/-- Truncating a function to the interval `(-A, A]`. -/
def truncation {α : Type*} (f : α → ℝ) (A : ℝ) :=
(indicator (set.Ioc (-A) A) id) ∘ f

variables {m : measurable_space α} {μ : measure α} {f : α → ℝ}

lemma _root_.measure_theory.ae_strongly_measurable.truncation
  (hf : ae_strongly_measurable f μ) {A : ℝ} :
  ae_strongly_measurable (truncation f A) μ :=
begin
  apply ae_strongly_measurable.comp_ae_measurable _ hf.ae_measurable,
  exact (strongly_measurable_id.indicator measurable_set_Ioc).ae_strongly_measurable,
end


lemma abs_truncation_le_bound (f : α → ℝ) (A : ℝ) (x : α) :
  abs (truncation f A x) ≤ |A| :=
begin
  simp only [truncation, set.indicator, set.mem_Icc, id.def, function.comp_app],
  split_ifs,
  { simp only [real.norm_eq_abs, abs_le],
    split,
    { linarith [neg_abs_le_neg A, h.1] },
    { linarith [le_abs_self A, h.2] } },
  { simp [abs_nonneg] }
end

@[simp] lemma truncation_zero (f : α → ℝ) :
  truncation f 0 = 0 :=
by simp [truncation]

lemma abs_truncation_le_abs_self (f : α → ℝ) (A : ℝ) (x : α) :
  |truncation f A x| ≤ |f x| :=
begin
  simp only [truncation, indicator, set.mem_Icc, id.def, function.comp_app],
  split_ifs,
  { exact le_rfl },
  { simp [abs_nonneg] },
end

lemma truncation_eq_self {f : α → ℝ} {A : ℝ} {x : α} (h : |f x| < A) :
  truncation f A x = f x :=
begin
  simp only [truncation, indicator, set.mem_Icc, id.def, function.comp_app, ite_eq_left_iff,
    not_le],
  assume H,
  apply H.elim,
  simp [(abs_lt.1 h).1, (abs_lt.1 h).2.le],
end

lemma truncation_eq_of_nonneg {f : α → ℝ} {A : ℝ}  (h : ∀ x, 0 ≤ f x) :
  truncation f A = (indicator (set.Ioc 0 A) id) ∘ f :=
begin
  ext x,
  rcases lt_trichotomy 0 (f x) with hx|hx|hx,
  { simp only [truncation, indicator, hx, set.mem_Ioc, id.def, function.comp_app, true_and],
    by_cases h'x : f x ≤ A,
    { have : - A < f x, by linarith [h x],
      simp only [this, true_and]},
    { simp only [h'x, and_false]} },
  { simp only [truncation, indicator, hx, id.def, function.comp_app, if_t_t]},
  { linarith [h x] },
end

lemma _root_.measure_theory.ae_strongly_measurable.mem_ℒp_truncation [is_finite_measure μ]
  (hf : ae_strongly_measurable f μ) {A : ℝ} {p : ℝ≥0∞} :
  mem_ℒp (truncation f A) p μ :=
begin
  refine mem_ℒp.mem_ℒp_of_exponent_le _ le_top,
  apply mem_ℒp_top_of_bound hf.truncation _
    (eventually_of_forall (λ x, abs_truncation_le_bound _ _ _)),
end

lemma _root_.measure_theory.ae_strongly_measurable.integrable_truncation [is_finite_measure μ]
  (hf : ae_strongly_measurable f μ) {A : ℝ} :
  integrable (truncation f A) μ :=
by { rw ← mem_ℒp_one_iff_integrable, exact hf.mem_ℒp_truncation }

lemma moment_truncation_eq_interval_integral (hf : ae_strongly_measurable f μ) {A : ℝ}
  (hA : 0 ≤ A) {n : ℕ} (hn : n ≠ 0) :
  ∫ x, (truncation f A x) ^ n ∂μ = ∫ y in (-A)..A, y ^ n ∂(measure.map f μ) :=
begin
  have M : measurable_set (set.Ioc (-A) A) := measurable_set_Ioc,
  change ∫ x, (λ z, (indicator (set.Ioc (-A) A) id z) ^ n) (f x) ∂μ = _,
  rw [← integral_map hf.ae_measurable, interval_integral.integral_of_le, ← integral_indicator M],
  { simp only [indicator, zero_pow' _ hn, id.def, ite_pow] },
  { linarith },
  { apply measurable.ae_strongly_measurable,
    convert (measurable_id.pow_const n).indicator M,
    simp only [indicator, zero_pow' _ hn, ite_pow] }
end

lemma moment_truncation_eq_interval_integral_of_nonneg (hf : ae_strongly_measurable f μ) {A : ℝ}
  {n : ℕ} (hn : n ≠ 0) (h'f : 0 ≤ f) :
  ∫ x, (truncation f A x) ^ n ∂μ = ∫ y in 0..A, y ^ n ∂(measure.map f μ) :=
begin
  have M : measurable_set (set.Ioc 0 A) := measurable_set_Ioc,
  have M' : measurable_set (set.Ioc A 0) := measurable_set_Ioc,
  rw truncation_eq_of_nonneg h'f,
  change ∫ x, (λ z, (indicator (set.Ioc 0 A) id z) ^ n) (f x) ∂μ = _,
  rcases le_or_lt 0 A with hA | hA,
  { rw [← integral_map hf.ae_measurable, interval_integral.integral_of_le hA,
        ← integral_indicator M],
    { simp only [indicator, zero_pow' _ hn, id.def, ite_pow] },
    { apply measurable.ae_strongly_measurable,
      convert (measurable_id.pow_const n).indicator M,
      simp only [indicator, zero_pow' _ hn, ite_pow] } },
  { rw [← integral_map hf.ae_measurable, interval_integral.integral_of_ge hA.le,
        ← integral_indicator M'],
    { simp only [set.Ioc_eq_empty (not_lt.2 hA.le), zero_pow' _ hn, set.indicator_empty,
        integral_const, algebra.id.smul_eq_mul, mul_zero, zero_eq_neg],
      apply integral_eq_zero_of_ae,
      have : ∀ᵐ x ∂(measure.map f μ), (0 : ℝ) ≤ x :=
        (ae_map_iff hf.ae_measurable measurable_set_Ici).2 (eventually_of_forall h'f),
      filter_upwards [this] with x hx,
      simp only [set.mem_Ioc, pi.zero_apply, ite_eq_right_iff, and_imp],
      assume h'x h''x,
      have : x = 0, by linarith,
      simp [this, zero_pow' _ hn] },
    { apply measurable.ae_strongly_measurable,
      convert (measurable_id.pow_const n).indicator M,
      simp only [indicator, zero_pow' _ hn, ite_pow] } }
end

lemma integral_truncation_eq_interval_integral (hf : ae_strongly_measurable f μ) {A : ℝ}
  (hA : 0 ≤ A) :
  ∫ x, truncation f A x ∂μ = ∫ y in (-A)..A, y ∂(measure.map f μ) :=
by simpa using moment_truncation_eq_interval_integral hf hA one_ne_zero

lemma integral_truncation_eq_interval_integral_of_nonneg (hf : ae_strongly_measurable f μ) {A : ℝ}
  (h'f : 0 ≤ f) :
  ∫ x, truncation f A x ∂μ = ∫ y in 0..A, y ∂(measure.map f μ) :=
by simpa using moment_truncation_eq_interval_integral_of_nonneg hf one_ne_zero h'f

lemma integral_truncation_le_integral_of_nonneg
  (hf : integrable f μ) (h'f : 0 ≤ f) {A : ℝ} :
  ∫ x, truncation f A x ∂μ ≤ ∫ x, f x ∂μ :=
begin
  apply integral_mono_of_nonneg (eventually_of_forall (λ x, _)) hf (eventually_of_forall (λ x, _)),
  { simp only [truncation, indicator, pi.zero_apply, set.mem_Ioc, id.def, function.comp_app],
    split_ifs,
    { exact h'f x },
    { exact le_rfl } },
  { simp only [truncation, indicator, set.mem_Ioc, id.def, function.comp_app],
    split_ifs,
    { exact le_rfl },
    { exact h'f x } }
end

/-- If a function is integrable, then the integral of its truncated versions converges to the
integral of the whole function. -/
lemma tendsto_integral_truncation {f : α → ℝ} (hf : integrable f μ) :
  tendsto (λ A, ∫ x, truncation f A x ∂μ) at_top (𝓝 (∫ x, f x ∂μ)) :=
begin
  refine tendsto_integral_filter_of_dominated_convergence (λ x, abs (f x)) _ _ _ _,
  { exact eventually_of_forall (λ A, hf.ae_strongly_measurable.truncation) },
  { apply eventually_of_forall (λ A, _),
    apply eventually_of_forall (λ x, _),
    rw real.norm_eq_abs,
    exact abs_truncation_le_abs_self _ _ _ },
  { apply hf.abs },
  { apply eventually_of_forall (λ x, _),
    apply tendsto_const_nhds.congr' _,
    filter_upwards [Ioi_mem_at_top (abs (f x))] with A hA,
    exact (truncation_eq_self hA).symm },
end

open probability_theory

lemma ident_distrib.truncation {β : Type*} [measurable_space β] {ν : measure β}
  {f : α → ℝ} {g : β → ℝ} (h : ident_distrib f g μ ν) {A : ℝ} :
  ident_distrib (truncation f A) (truncation g A) μ ν :=
h.comp (strongly_measurable_id.indicator measurable_set_Ioc).measurable

end truncation


lemma geom_sum_Ico_le_of_lt_one {a b : ℕ} {c : ℝ} (hc : 0 ≤ c) (h'c : c < 1) :
  ∑ i in Ico a b, c ^ i ≤ c ^ a / (1 - c) :=
begin
  rcases le_or_lt a b with hab | hab, swap,
  { rw [Ico_eq_empty, sum_empty],
    { apply div_nonneg (pow_nonneg hc _),
      simpa using h'c.le },
    { simpa using hab.le } },
  rw geom_sum_Ico' h'c.ne hab,
  apply div_le_div (pow_nonneg hc _) _ (sub_pos.2 h'c) le_rfl,
  simpa using pow_nonneg hc _
end


lemma aux_sum_horrible (N : ℕ) {j : ℝ} (hj : 0 < j) {c : ℝ} (hc : 1 < c) :
  ∑ i in (range N).filter (λ i, j < c ^ i), 1 / (c ^ i) ^ 2 ≤ (c^3 * (c - 1) ⁻¹) / j ^ 2 :=
begin
  have cpos : 0 < c := zero_lt_one.trans hc,
  have A : 0 < (c⁻¹) ^ 2 := sq_pos_of_pos (inv_pos.2 cpos),
  have B : c^2 * (1 - c⁻¹ ^ 2) ⁻¹ ≤ c^3 * (c - 1) ⁻¹,
  { rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff _ (sub_pos.2 hc)], swap,
    { exact sub_pos.2 (pow_lt_one (inv_nonneg.2 cpos.le) (inv_lt_one hc) two_ne_zero) },
    have : c ^ 3 = c^2 * c, by ring_exp,
    simp only [mul_sub, this, mul_one, inv_pow₀, sub_le_sub_iff_left],
    rw [mul_assoc, mul_comm c, ← mul_assoc, mul_inv_cancel (sq_pos_of_pos cpos).ne', one_mul],
    simpa using pow_le_pow hc.le one_le_two },
  calc
  ∑ i in (range N).filter (λ i, j < c ^ i), 1/ (c ^ i) ^ 2
    ≤ ∑ i in Ico (⌊real.log j / real.log c⌋₊) N, 1 / (c ^ i) ^ 2 :
  begin
    refine sum_le_sum_of_subset_of_nonneg _ (λ i hi hident, div_nonneg zero_le_one (sq_nonneg _)),
    assume i hi,
    simp only [mem_filter, mem_range] at hi,
    simp only [hi.1, mem_Ico, and_true],
    apply nat.floor_le_of_le,
    apply le_of_lt,
    rw [div_lt_iff (real.log_pos hc), ← real.log_pow],
    exact real.log_lt_log hj hi.2
  end
  ... = ∑ i in Ico (⌊real.log j / real.log c⌋₊) N, ((c⁻¹) ^ 2) ^ i :
  begin
    congr' 1 with i,
    simp [← pow_mul, mul_comm],
  end
  ... ≤ ((c⁻¹) ^ 2) ^ (⌊real.log j / real.log c⌋₊) / (1 - (c⁻¹) ^ 2) :
  begin
    apply geom_sum_Ico_le_of_lt_one (sq_nonneg _),
    rw sq_lt_one_iff (inv_nonneg.2 (zero_le_one.trans hc.le)),
    exact inv_lt_one hc
  end
  ... ≤ ((c⁻¹) ^ 2) ^ (real.log j / real.log c - 1) / (1 - (c⁻¹) ^ 2) :
  begin
    apply div_le_div _ _ _ le_rfl,
    { apply real.rpow_nonneg_of_nonneg (sq_nonneg _) },
    { rw ← real.rpow_nat_cast,
      apply real.rpow_le_rpow_of_exponent_ge A,
      { exact pow_le_one _ (inv_nonneg.2 (zero_le_one.trans hc.le)) (inv_le_one hc.le) },
      { exact (nat.sub_one_lt_floor _).le } },
    { simpa only [inv_pow₀, sub_pos] using inv_lt_one (one_lt_pow hc two_ne_zero) }
  end
  ... = (c^2 * (1 - c⁻¹ ^ 2) ⁻¹) / j ^ 2 :
  begin
    have I : (c ⁻¹ ^ 2) ^ (real.log j / real.log c) = 1 / j ^ 2,
    { apply real.log_inj_on_pos (real.rpow_pos_of_pos A _),
      { rw [one_div], exact inv_pos.2 (sq_pos_of_pos hj) },
      rw real.log_rpow A,
      simp only [one_div, real.log_inv, real.log_pow, nat.cast_bit0, nat.cast_one, mul_neg,
        neg_inj],
      field_simp [(real.log_pos hc).ne'],
      ring },
    rw [real.rpow_sub A, I],
    have : c^2 - 1 ≠ 0 := (sub_pos.2 (one_lt_pow hc two_ne_zero)).ne',
    field_simp [hj.ne', (zero_lt_one.trans hc).ne'],
    ring,
  end
  ... ≤ (c^3 * (c - 1) ⁻¹) / j ^ 2 :
  begin
    apply div_le_div _ B (sq_pos_of_pos hj) le_rfl,
    exact mul_nonneg (pow_nonneg cpos.le _) (inv_nonneg.2 (sub_pos.2 hc).le),
  end
end

lemma mul_pow_le_nat_floor_pow {c : ℝ} (hc : 1 < c) (i : ℕ) :
  (1 - c⁻¹) * c ^ i ≤ ⌊c ^ i⌋₊ :=
begin
  have cpos : 0 < c := zero_lt_one.trans hc,
  rcases nat.eq_zero_or_pos i with rfl|hi,
  { simp only [pow_zero, nat.floor_one, nat.cast_one, mul_one, sub_le_self_iff, inv_nonneg,
      cpos.le] },
  have hident : 1 ≤ i := hi,
  calc (1 - c⁻¹) * c ^ i
      = c ^ i - c ^ i * c ⁻¹ : by ring
  ... ≤ c ^ i - 1 :
    by simpa only [←div_eq_mul_inv, sub_le_sub_iff_left, one_le_div cpos, pow_one]
      using pow_le_pow hc.le hident
  ... ≤ ⌊c ^ i⌋₊ : (nat.sub_one_lt_floor _).le
end

lemma aux_sum_horrible2 (N : ℕ) {j : ℝ} (hj : 0 < j) {c : ℝ} (hc : 1 < c) :
  ∑ i in (range N).filter (λ i, j < ⌊c ^ i⌋₊), (1 : ℝ) / ⌊c ^ i⌋₊ ^ 2
    ≤ (c ^ 5 * (c - 1) ⁻¹ ^ 3) / j ^ 2 :=
begin
  have cpos : 0 < c := zero_lt_one.trans hc,
  have A : 0 < 1 - c⁻¹ := sub_pos.2 (inv_lt_one hc),
  calc
  ∑ i in (range N).filter (λ i, j < ⌊c ^ i⌋₊), (1 : ℝ) / ⌊c ^ i⌋₊ ^ 2
      ≤ ∑ i in (range N).filter (λ i, j < c ^ i), (1 : ℝ) / ⌊c ^ i⌋₊ ^ 2 :
  begin
    apply sum_le_sum_of_subset_of_nonneg,
    { assume i hi,
      simp only [mem_filter, mem_range] at hi,
      simpa only [hi.1, mem_filter, mem_range, true_and]
        using hi.2.trans_le (nat.floor_le (pow_nonneg cpos.le _)) },
    { assume i hi hident,
      exact div_nonneg zero_le_one (sq_nonneg _), }
  end
  ... ≤ ∑ i in (range N).filter (λ i, j < c ^ i), ((1 - c⁻¹) ⁻¹) ^ 2 * (1 / (c ^ i) ^ 2) :
  begin
    apply sum_le_sum (λ i hi, _),
    rw [mul_div_assoc', mul_one, div_le_div_iff], rotate,
    { apply sq_pos_of_pos,
      refine zero_lt_one.trans_le _,
      simp only [nat.le_floor, one_le_pow_of_one_le, hc.le, nat.one_le_cast, nat.cast_one] },
    { exact sq_pos_of_pos (pow_pos cpos _) },
    rw [one_mul, ← mul_pow],
    apply pow_le_pow_of_le_left (pow_nonneg cpos.le _),
    rw [← div_eq_inv_mul, le_div_iff A, mul_comm],
    exact mul_pow_le_nat_floor_pow hc i,
  end
  ... ≤ ((1 - c⁻¹) ⁻¹) ^ 2 * (c^3 * (c - 1) ⁻¹) / j ^ 2 :
  begin
    rw [← mul_sum, ← mul_div_assoc'],
    refine mul_le_mul_of_nonneg_left _ (sq_nonneg _),
    exact aux_sum_horrible N hj hc,
  end
  ... = (c ^ 5 * (c - 1) ⁻¹ ^ 3) / j ^ 2 :
  begin
    congr' 1,
    field_simp [cpos.ne', (sub_pos.2 hc).ne'],
    ring,
  end
end


lemma of_real_integral_on_one_of_measure_ne_top {α : Type*} {m : measurable_space α} (μ : measure α)
  {s : set α} (hs : μ s ≠ ∞) :
  ennreal.of_real (∫ x in s, (1 : ℝ) ∂μ) = μ s :=
calc
ennreal.of_real (∫ x in s, (1 : ℝ) ∂μ)
= ennreal.of_real (∫ x in s, ∥(1 : ℝ)∥ ∂μ) : by simp only [cstar_ring.norm_one]
... = ∫⁻ x in s, 1 ∂μ :
begin
  rw of_real_integral_norm_eq_lintegral_nnnorm,
  { simp only [nnnorm_one, ennreal.coe_one] },
  { rw integrable_const_iff,
    simp only [hs.lt_top, one_ne_zero, measure.restrict_apply, measurable_set.univ, set.univ_inter,
      false_or], }
end
... = μ s :
  by simp only [lintegral_one, measure.restrict_apply, measurable_set.univ, set.univ_inter]

lemma of_real_integral_on_one {α : Type*} {m : measurable_space α} (μ : measure α)
  [is_finite_measure μ] (s : set α) :
  ennreal.of_real (∫ x in s, (1 : ℝ) ∂μ) = μ s :=
of_real_integral_on_one_of_measure_ne_top μ (measure_ne_top μ s)

variables {Ω : Type*} [measure_space Ω] [is_probability_measure (ℙ : measure Ω)]

lemma sum_probability_mem_Ioc_le
  {X : Ω → ℝ} (hint : integrable X) (hnonneg : 0 ≤ X) {K : ℕ} {N : ℕ} (hKN : K ≤ N) :
  ∑ j in range K, ℙ {ω | X ω ∈ set.Ioc (j : ℝ) N} ≤ ennreal.of_real (𝔼[X] + 1) :=
begin
  let ρ : measure ℝ := measure.map X ℙ,
  haveI : is_probability_measure ρ := is_probability_measure_map hint.ae_measurable,
  have A : ∑ j in range K, ∫ x in j..N, (1 : ℝ) ∂ρ ≤ 𝔼[X] + 1, from calc
  ∑ j in range K, ∫ x in j..N, (1 : ℝ) ∂ρ
      = ∑ j in range K, ∑ i in Ico j N, ∫ x in i..(i+1 : ℕ), (1 : ℝ) ∂ρ :
    begin
      apply sum_congr rfl (λ j hj, _),
      rw interval_integral.sum_integral_adjacent_intervals_Ico ((mem_range.1 hj).le.trans hKN),
      assume k hk,
      exact continuous_const.interval_integrable _ _,
    end
  ... = ∑ i in range N, ∑ j in range (min (i+1) K), ∫ x in i..(i+1 : ℕ), (1 : ℝ) ∂ρ :
    begin
      simp_rw [sum_sigma'],
      refine sum_bij' (λ (p : (Σ (i : ℕ), ℕ)) hp, (⟨p.2, p.1⟩ : (Σ (i : ℕ), ℕ))) _ (λ a ha, rfl)
        (λ (p : (Σ (i : ℕ), ℕ)) hp, (⟨p.2, p.1⟩ : (Σ (i : ℕ), ℕ))) _ _ _,
      { rintros ⟨i, j⟩ hij,
        simp only [mem_sigma, mem_range, mem_Ico] at hij,
        simp only [hij, nat.lt_succ_iff.2 hij.2.1, mem_sigma, mem_range, lt_min_iff, and_self] },
      { rintros ⟨i, j⟩ hij,
        simp only [mem_sigma, mem_range, lt_min_iff] at hij,
        simp only [hij, nat.lt_succ_iff.1 hij.2.1, mem_sigma, mem_range, mem_Ico, and_self] },
      { rintros ⟨i, j⟩ hij, refl },
      { rintros ⟨i, j⟩ hij, refl },
    end
  ... ≤ ∑ i in range N, (i + 1) * ∫ x in i..(i+1 : ℕ), (1 : ℝ) ∂ρ :
    begin
      apply sum_le_sum (λ i hi, _),
      simp only [nat.cast_add, nat.cast_one, sum_const, card_range, nsmul_eq_mul, nat.cast_min],
      refine mul_le_mul_of_nonneg_right (min_le_left _ _) _,
      apply interval_integral.integral_nonneg,
      { simp only [le_add_iff_nonneg_right, zero_le_one] },
      { simp only [zero_le_one, implies_true_iff], }
    end
  ... ≤ ∑ i in range N, ∫ x in i..(i+1 : ℕ), (x + 1) ∂ρ :
    begin
      apply sum_le_sum (λ i hi, _),
      have I : (i : ℝ) ≤ (i + 1 : ℕ),
        by simp only [nat.cast_add, nat.cast_one, le_add_iff_nonneg_right, zero_le_one],
      simp_rw [interval_integral.integral_of_le I, ← integral_mul_left],
      apply set_integral_mono_on,
      { exact continuous_const.integrable_on_Ioc },
      { exact (continuous_id.add continuous_const).integrable_on_Ioc },
      { exact measurable_set_Ioc },
      { assume x hx,
        simp only [nat.cast_add, nat.cast_one, set.mem_Ioc] at hx,
        simp [hx.1.le] }
    end
  ... = ∫ x in 0..N, x + 1 ∂ρ :
    begin
      rw interval_integral.sum_integral_adjacent_intervals (λ k hk, _),
      { refl },
      { exact (continuous_id.add continuous_const).interval_integrable _ _ }
    end
  ... = ∫ x in 0..N, x ∂ρ + ∫ x in 0..N, 1 ∂ρ :
    begin
      rw interval_integral.integral_add,
      { exact continuous_id.interval_integrable _ _ },
      { exact continuous_const.interval_integrable _ _ },
    end
  ... = 𝔼[truncation X N] + ∫ x in 0..N, 1 ∂ρ :
    by rw integral_truncation_eq_interval_integral_of_nonneg hint.1 hnonneg
  ... ≤ 𝔼[X] + ∫ x in 0..N, 1 ∂ρ :
    add_le_add_right (integral_truncation_le_integral_of_nonneg hint hnonneg) _
  ... ≤ 𝔼[X] + 1 :
    begin
      refine add_le_add le_rfl _,
      rw interval_integral.integral_of_le (nat.cast_nonneg _),
      simp only [integral_const, measure.restrict_apply', measurable_set_Ioc, set.univ_inter,
        algebra.id.smul_eq_mul, mul_one],
      rw ← ennreal.one_to_real,
      exact ennreal.to_real_mono ennreal.one_ne_top prob_le_one,
    end,
  have B : ∀ a b, ℙ {ω | X ω ∈ set.Ioc a b} = ennreal.of_real (∫ x in set.Ioc a b, (1 : ℝ) ∂ρ),
  { assume a b,
    rw of_real_integral_on_one ρ _,
    rw measure.map_apply_of_ae_measurable hint.ae_measurable measurable_set_Ioc,
    refl },
  calc ∑ j in range K, ℙ {ω | X ω ∈ set.Ioc (j : ℝ) N}
      = ∑ j in range K, ennreal.of_real (∫ x in set.Ioc (j : ℝ) N, (1 : ℝ) ∂ρ) :
    by simp_rw B
  ... = ennreal.of_real (∑ j in range K, ∫ x in set.Ioc (j : ℝ) N, (1 : ℝ) ∂ρ) :
    begin
      rw ennreal.of_real_sum_of_nonneg,
      simp only [integral_const, algebra.id.smul_eq_mul, mul_one, ennreal.to_real_nonneg,
        implies_true_iff],
    end
  ... = ennreal.of_real (∑ j in range K, ∫ x in (j : ℝ)..N, (1 : ℝ) ∂ρ) :
    begin
      congr' 1,
      refine sum_congr rfl (λ j hj, _),
      rw interval_integral.integral_of_le (nat.cast_le.2 ((mem_range.1 hj).le.trans hKN)),

    end
  ... ≤ ennreal.of_real (𝔼[X] + 1) : ennreal.of_real_le_of_real A
end

lemma tsum_prob_mem_Ioi_lt_top
  {X : Ω → ℝ} (hint : integrable X) (hnonneg : 0 ≤ X) :
  ∑' (j : ℕ), ℙ {ω | X ω ∈ set.Ioi (j : ℝ)} < ∞ :=
begin
  suffices : ∀ (K : ℕ), ∑ j in range K, ℙ {ω | X ω ∈ set.Ioi (j : ℝ)} ≤ ennreal.of_real (𝔼[X] + 1),
  { apply (le_of_tendsto_of_tendsto (ennreal.tendsto_nat_tsum _) tendsto_const_nhds
      (eventually_of_forall this)).trans_lt ennreal.of_real_lt_top },
  assume K,
  have A : tendsto (λ (N : ℕ), ∑ j in range K, ℙ {ω | X ω ∈ set.Ioc (j : ℝ) N})
    at_top (𝓝 (∑ j in range K, ℙ {ω | X ω ∈ set.Ioi (j : ℝ)})),
  { refine tendsto_finset_sum _ (λ i hi, _),
    have : {ω | X ω ∈ set.Ioi (i : ℝ)} = ⋃ (N : ℕ), {ω | X ω ∈ set.Ioc (i : ℝ) N},
    { apply set.subset.antisymm _ _,
      { assume ω hω,
        obtain ⟨N, hN⟩ : ∃ (N : ℕ), X ω ≤ N := exists_nat_ge (X ω),
        exact set.mem_Union.2 ⟨N, hω, hN⟩ },
      { simp only [set.mem_Ioc, set.mem_Ioi, set.Union_subset_iff, set.set_of_subset_set_of,
          implies_true_iff] {contextual := tt} } },
    rw this,
    apply tendsto_measure_Union,
    assume m n hmn x hx,
    exact ⟨hx.1, hx.2.trans (nat.cast_le.2 hmn)⟩ },
  apply le_of_tendsto_of_tendsto A tendsto_const_nhds,
  filter_upwards [Ici_mem_at_top K] with N hN,
  exact sum_probability_mem_Ioc_le hint hnonneg hN
end

lemma sum_variance_truncation_le
  {X : Ω → ℝ} (hint : integrable X) (hnonneg : 0 ≤ X) (K : ℕ) :
  ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * 𝔼[(truncation X j) ^ 2] ≤ 2 * 𝔼[X] :=
begin
  set Y := λ (n : ℕ), truncation X n,
  let ρ : measure ℝ := measure.map X ℙ,
  have Y2 : ∀ n, 𝔼[Y n ^ 2] = ∫ x in 0..n, x ^ 2 ∂ρ,
  { assume n,
    change 𝔼[λ x, (Y n x)^2] = _,
    rw [moment_truncation_eq_interval_integral_of_nonneg hint.1 two_ne_zero hnonneg] },
  calc ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * 𝔼[Y j ^ 2]
      = ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * ∫ x in 0..j, x ^ 2 ∂ρ :
    by simp_rw [Y2]
  ... = ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * ∑ k in range j, ∫ x in k..(k+1 : ℕ), x ^ 2 ∂ρ :
    begin
      congr' 1 with j,
      congr' 1,
      rw interval_integral.sum_integral_adjacent_intervals,
      { refl },
      assume k hk,
      exact (continuous_id.pow _).interval_integrable _ _,
    end
  ... = ∑ k in range K, (∑ j in Ioo k K, ((j : ℝ) ^ 2) ⁻¹) * ∫ x in k..(k+1 : ℕ), x ^ 2 ∂ρ :
    begin
      simp_rw [mul_sum, sum_mul, sum_sigma'],
      refine sum_bij' (λ (p : (Σ (i : ℕ), ℕ)) hp, (⟨p.2, p.1⟩ : (Σ (i : ℕ), ℕ))) _ (λ a ha, rfl)
        (λ (p : (Σ (i : ℕ), ℕ)) hp, (⟨p.2, p.1⟩ : (Σ (i : ℕ), ℕ))) _ _ _,
      { rintros ⟨i, j⟩ hij,
        simp only [mem_sigma, mem_range, mem_filter] at hij,
        simp [hij, mem_sigma, mem_range, and_self, hij.2.trans hij.1], },
      { rintros ⟨i, j⟩ hij,
        simp only [mem_sigma, mem_range, mem_Ioo] at hij,
        simp only [hij, mem_sigma, mem_range, and_self], },
      { rintros ⟨i, j⟩ hij, refl },
      { rintros ⟨i, j⟩ hij, refl },
    end
  ... ≤ ∑ k in range K, (2/ (k+1)) * ∫ x in k..(k+1 : ℕ), x ^ 2 ∂ρ :
    begin
      apply sum_le_sum (λ k hk, _),
      simp_rw [← one_div],
      refine mul_le_mul_of_nonneg_right (sum_Ioo_div_sq_le _ _) _,
      refine interval_integral.integral_nonneg_of_forall _ (λ u, sq_nonneg _),
      simp only [nat.cast_add, nat.cast_one, le_add_iff_nonneg_right, zero_le_one],
    end
  ... ≤ ∑ k in range K, ∫ x in k..(k+1 : ℕ), 2 * x ∂ρ :
    begin
      apply sum_le_sum (λ k hk, _),
      have Ik : (k : ℝ) ≤ (k + 1 : ℕ), by simp,
      rw ← interval_integral.integral_const_mul,
      rw [interval_integral.integral_of_le Ik, interval_integral.integral_of_le Ik],
      apply set_integral_mono_on,
      { apply continuous.integrable_on_Ioc,
        exact continuous_const.mul (continuous_pow 2) },
      { apply continuous.integrable_on_Ioc,
        exact continuous_const.mul continuous_id' },
      { exact measurable_set_Ioc },
      { assume x hx,
        calc 2 / (↑k + 1) * x ^ 2 = (x / (k+1)) * (2 * x) : by ring_exp
        ... ≤ 1 * (2 * x) :
          begin
            apply mul_le_mul_of_nonneg_right _
              (mul_nonneg zero_le_two ((nat.cast_nonneg k).trans hx.1.le)),
            apply (div_le_one _).2 hx.2,
            simp only [nat.cast_add, nat.cast_one],
            linarith only [show (0 : ℝ) ≤ k, from  nat.cast_nonneg k],
          end
        ... = 2 * x : by rw one_mul }
    end
  ... = 2 * ∫ x in (0 : ℝ)..K, x ∂ρ :
    begin
      rw interval_integral.sum_integral_adjacent_intervals (λ k hk, _),
      swap, { exact (continuous_const.mul continuous_id').interval_integrable _ _ },
      rw interval_integral.integral_const_mul,
      refl
    end
  ... ≤ 2 * 𝔼[X] :
    begin
      apply mul_le_mul_of_nonneg_left _ zero_le_two,
      calc ∫ x in 0..↑K, x ∂ρ = ∫ a, truncation X K a :
        by rw integral_truncation_eq_interval_integral_of_nonneg hint.1 hnonneg
      ... ≤ ∫ (a : Ω), X a :
        begin
          apply integral_mono_of_nonneg (eventually_of_forall (λ x, _)) hint
            (eventually_of_forall (λ x, _)),
          { simp only [truncation, indicator, pi.zero_apply, set.mem_Ioc, id.def,
              function.comp_app],
            split_ifs,
            { exact hnonneg x },
            { exact le_rfl } },
          { simp only [truncation, indicator, set.mem_Ioc, id.def, function.comp_app],
            split_ifs,
            { exact le_rfl },
            { exact hnonneg x } }
        end
    end
end


variables (X : ℕ → Ω → ℝ) (hint : integrable (X 0))
  (hindep : pairwise (λ i j, indep_fun (X i) (X j)))
  (hident : ∀ i, ident_distrib (X i) (X 0))
  (hnonneg : ∀ i ω, 0 ≤ X i ω)

include X hint hindep hident hnonneg

lemma strong_law_aux1 {c : ℝ} (c_one : 1 < c) {ε : ℝ} (εpos : 0 < ε) :
  ∀ᵐ ω, ∀ᶠ (n : ℕ) in at_top,
    |∑ i in range ⌊c^n⌋₊, truncation (X i) i ω - 𝔼[∑ i in range ⌊c^n⌋₊, truncation (X i) i]|
      < ε * ⌊c^n⌋₊ :=
begin
  have c_pos : 0 < c := zero_lt_one.trans c_one,
  let ρ : measure ℝ := measure.map (X 0) ℙ,
  have hX : ∀ i, ae_strongly_measurable (X i) ℙ :=
    λ i, (hident i).symm.ae_strongly_measurable_snd hint.1,
  have A : ∀ i, strongly_measurable (indicator (set.Ioc (-i : ℝ) i) id) :=
    λ i, strongly_measurable_id.indicator measurable_set_Ioc,
  set Y := λ (n : ℕ), truncation (X n) n with hY,
  set S := λ n, ∑ i in range n, Y i with hS,
  let u : ℕ → ℕ := λ n, ⌊c ^ n⌋₊,
  have u_mono : monotone u :=
    λ i j hij, nat.floor_mono (pow_le_pow c_one.le hij),
  have I1 : ∀ K, ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * Var[Y j] ≤ 2 * 𝔼[X 0],
  { assume K,
    calc ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * Var[Y j] ≤
      ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * 𝔼[(truncation (X 0) j)^2] :
      begin
        apply sum_le_sum (λ j hj, _),
        refine mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (sq_nonneg _)),
        rw (hident j).truncation.variance_eq,
        exact variance_le_expectation_sq,
      end
      ... ≤ 2 * 𝔼[X 0] : sum_variance_truncation_le hint (hnonneg 0) K },
  let C := (c ^ 5 * (c - 1) ⁻¹ ^ 3) * (2 * 𝔼[X 0]),
  have I2 : ∀ N, ∑ i in range N, ((u i : ℝ) ^ 2) ⁻¹ * Var[S (u i)] ≤ C,
  { assume N,
    calc
    ∑ i in range N, ((u i : ℝ) ^ 2) ⁻¹ * Var[S (u i)]
        = ∑ i in range N, ((u i : ℝ) ^ 2) ⁻¹ * (∑ j in range (u i), Var[Y j]) :
      begin
        congr' 1 with i,
        congr' 1,
        rw [hS, indep_fun.Var_sum],
        { assume j hj,
          exact (hident j).ae_strongly_measurable.mem_ℒp_truncation },
        { assume k hk l hl hkl,
          exact (hindep k l hkl).comp (A k).measurable (A l).measurable }
      end
    ... = ∑ j in range (u (N - 1)),
            (∑ i in (range N).filter (λ i, j < u i), ((u i : ℝ) ^ 2) ⁻¹) * Var[Y j] :
      begin
        simp_rw [mul_sum, sum_mul, sum_sigma'],
        refine sum_bij' (λ (p : (Σ (i : ℕ), ℕ)) hp, (⟨p.2, p.1⟩ : (Σ (i : ℕ), ℕ))) _ (λ a ha, rfl)
          (λ (p : (Σ (i : ℕ), ℕ)) hp, (⟨p.2, p.1⟩ : (Σ (i : ℕ), ℕ))) _ _ _,
        { rintros ⟨i, j⟩ hij,
          simp only [mem_sigma, mem_range] at hij,
          simp only [hij.1, hij.2, mem_sigma, mem_range, mem_filter, and_true],
          exact hij.2.trans_le (u_mono (nat.le_pred_of_lt hij.1)) },
        { rintros ⟨i, j⟩ hij,
          simp only [mem_sigma, mem_range, mem_filter] at hij,
          simp only [hij.2.1, hij.2.2, mem_sigma, mem_range, and_self] },
        { rintros ⟨i, j⟩ hij, refl },
        { rintros ⟨i, j⟩ hij, refl },
      end
    ... ≤ ∑ j in range (u (N - 1)), (c ^ 5 * (c - 1) ⁻¹ ^ 3 / j ^ 2) * Var[Y j] :
      begin
        apply sum_le_sum (λ j hj, _),
        rcases @eq_zero_or_pos _ _ j with rfl|hj,
        { simp only [Y, nat.cast_zero, zero_pow', ne.def, bit0_eq_zero, nat.one_ne_zero,
            not_false_iff, div_zero, zero_mul],
          simp only [nat.cast_zero, truncation_zero, variance_zero, mul_zero] },
        apply mul_le_mul_of_nonneg_right _ (variance_nonneg _ _),
        convert aux_sum_horrible2 N (nat.cast_pos.2 hj) c_one,
        { simp only [nat.cast_lt] },
        { simp only [one_div] }
      end
    ... = (c ^ 5 * (c - 1) ⁻¹ ^ 3) * ∑ j in range (u (N - 1)), ((j : ℝ) ^ 2) ⁻¹ * Var[Y j] :
        by { simp_rw [mul_sum, div_eq_mul_inv], ring_nf }
    ... ≤ (c ^ 5 * (c - 1) ⁻¹ ^ 3) * (2 * 𝔼[X 0]) :
      begin
        apply mul_le_mul_of_nonneg_left (I1 _),
        apply mul_nonneg (pow_nonneg c_pos.le _),
        exact pow_nonneg (inv_nonneg.2 (sub_nonneg.2 c_one.le)) _
      end },
  have I3 : ∀ N, ∑ i in range N,
    ℙ {ω | (u i * ε : ℝ) ≤ |S (u i) ω - 𝔼[S (u i)]|} ≤ ennreal.of_real (ε ⁻¹ ^ 2 * C),
  { assume N,
    calc ∑ i in range N, ℙ {ω | (u i * ε : ℝ) ≤ |S (u i) ω - 𝔼[S (u i)]|}
        ≤ ∑ i in range N, ennreal.of_real (Var[S (u i)] / (u i * ε) ^ 2) :
      begin
        refine sum_le_sum (λ i hi, _),
        apply meas_ge_le_mul_variance,
        { exact mem_ℒp_finset_sum' _
            (λ j hj, (hident j).ae_strongly_measurable.mem_ℒp_truncation) },
        { apply mul_pos (nat.cast_pos.2 _) εpos,
          refine zero_lt_one.trans_le _,
          apply nat.le_floor,
          rw nat.cast_one,
          apply one_le_pow_of_one_le c_one.le }
      end
    ... = ennreal.of_real (∑ i in range N, Var[S (u i)] / (u i * ε) ^ 2) :
      begin
        rw ennreal.of_real_sum_of_nonneg (λ i hi, _),
        exact div_nonneg (variance_nonneg _ _) (sq_nonneg _),
      end
    ... ≤ ennreal.of_real (ε ⁻¹ ^ 2 * C) :
      begin
        apply ennreal.of_real_le_of_real,
        simp_rw [div_eq_inv_mul, ← inv_pow₀, mul_inv₀, mul_comm _ (ε⁻¹), mul_pow, mul_assoc,
          ← mul_sum],
        refine mul_le_mul_of_nonneg_left _ (sq_nonneg _),
        simp_rw [inv_pow₀],
        exact I2 N
      end },
  have I4 : ∑' i, ℙ {ω | (u i * ε : ℝ) ≤ |S (u i) ω - 𝔼[S (u i)]|} < ∞ :=
    (le_of_tendsto_of_tendsto' (ennreal.tendsto_nat_tsum _) tendsto_const_nhds I3).trans_lt
      ennreal.of_real_lt_top,
  filter_upwards [ae_eventually_not_mem I4.ne] with ω hω,
  simp_rw [not_le, mul_comm, S, sum_apply] at hω,
  exact hω,
end

lemma strong_law_aux2 {c : ℝ} (c_one : 1 < c) :
  ∀ᵐ ω, asymptotics.is_o
  (λ (n : ℕ), ∑ i in range ⌊c^n⌋₊, truncation (X i) i ω - 𝔼[∑ i in range ⌊c^n⌋₊, truncation (X i) i])
    (λ (n : ℕ), (⌊c^n⌋₊ : ℝ)) at_top :=
begin
  obtain ⟨v, -, v_pos, v_lim⟩ :
    ∃ (u : ℕ → ℝ), strict_anti u ∧ (∀ (n : ℕ), 0 < u n) ∧ tendsto u at_top (𝓝 0) :=
    exists_seq_strict_anti_tendsto (0 : ℝ),
  have := λ i, strong_law_aux1 X hint hindep hident hnonneg c_one (v_pos i),
  filter_upwards [ae_all_iff.2 this] with ω hω,
  apply asymptotics.is_o_iff.2 (λ ε εpos, _),
  obtain ⟨i, hi⟩ : ∃ i, v i < ε := ((tendsto_order.1 v_lim).2 ε εpos).exists,
  filter_upwards [hω i] with n hn,
  simp only [real.norm_eq_abs, lattice_ordered_comm_group.abs_abs, nat.abs_cast],
  exact hn.le.trans (mul_le_mul_of_nonneg_right hi.le (nat.cast_nonneg _)),
end

omit hindep hnonneg
lemma strong_law_aux3 :
  asymptotics.is_o (λ n, 𝔼[∑ i in range n, truncation (X i) i] - n * 𝔼[X 0])
    (λ (n : ℕ), (n : ℝ)) at_top :=
begin
  have A : ∀ i, strongly_measurable (indicator (set.Ioc (-i : ℝ) i) id) :=
    λ i, strongly_measurable_id.indicator measurable_set_Ioc,
  have A : tendsto (λ i, 𝔼[truncation (X i) i]) at_top (𝓝 (𝔼[X 0])),
  { convert (tendsto_integral_truncation hint).comp tendsto_coe_nat_at_top_at_top,
    ext i,
    exact (hident i).truncation.integral_eq },
  convert asymptotics.is_o_sum_range_of_tendsto_zero (tendsto_sub_nhds_zero_iff.1 A),
  ext1 n,
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, sum_apply, sub_left_inj],
  rw integral_finset_sum _ (λ i hi, _),
  exact ((hident i).symm.integrable_snd hint).1.integrable_truncation,
end
include hindep hnonneg

lemma strong_law_aux4 {c : ℝ} (c_one : 1 < c) :
  ∀ᵐ ω, asymptotics.is_o
  (λ (n : ℕ), ∑ i in range ⌊c^n⌋₊, truncation (X i) i ω - ⌊c^n⌋₊ * 𝔼[X 0])
    (λ (n : ℕ), (⌊c^n⌋₊ : ℝ)) at_top :=
begin
  filter_upwards [strong_law_aux2 X hint hindep hident hnonneg c_one] with ω hω,
  have A : tendsto (λ (n : ℕ), ⌊c ^ n⌋₊) at_top at_top :=
    tendsto_nat_floor_at_top.comp (tendsto_pow_at_top_at_top_of_one_lt c_one),
  convert hω.add ((strong_law_aux3 X hint hident).comp_tendsto A),
  ext1 n,
  simp,
end

lemma strong_law_aux5 :
  ∀ᵐ ω, asymptotics.is_o
  (λ (n : ℕ), ∑ i in range n, truncation (X i) i ω - ∑ i in range n, X i ω)
  (λ (n : ℕ), (n : ℝ)) at_top :=
begin
  have A : ∑' (j : ℕ), ℙ {ω | X j ω ∈ set.Ioi (j : ℝ)} < ∞,
  { convert tsum_prob_mem_Ioi_lt_top hint (hnonneg 0),
    ext1 j,
    exact (hident j).measure_mem_eq measurable_set_Ioi },
  have B : ∀ᵐ ω, tendsto (λ (n : ℕ), truncation (X n) n ω - X n ω) at_top (𝓝 0),
  { filter_upwards [ae_eventually_not_mem A.ne] with ω hω,
    apply tendsto_const_nhds.congr' _,
    filter_upwards [hω, Ioi_mem_at_top 0] with n hn npos,
    simp only [truncation, indicator, set.mem_Ioc, id.def, function.comp_app],
    split_ifs,
    { exact (sub_self _).symm },
    { have : - (n : ℝ) < X n ω,
      { apply lt_of_lt_of_le _ (hnonneg n ω),
        simpa only [right.neg_neg_iff, nat.cast_pos] using npos },
      simp only [this, true_and, not_le] at h,
      exact (hn h).elim } },
  filter_upwards [B] with ω hω,
  convert is_o_sum_range_of_tendsto_zero hω,
  ext n,
  rw sum_sub_distrib,
end

lemma strong_law_aux6 {c : ℝ} (c_one : 1 < c) :
  ∀ᵐ ω, asymptotics.is_o
  (λ (n : ℕ), ∑ i in range ⌊c^n⌋₊, X i ω - ⌊c^n⌋₊ * 𝔼[X 0])
    (λ (n : ℕ), (⌊c^n⌋₊ : ℝ)) at_top :=
begin
  filter_upwards [strong_law_aux4 X hint hindep hident hnonneg c_one,
    strong_law_aux5 X hint hindep hident hnonneg] with ω hω h'ω,
  have A : tendsto (λ (n : ℕ), ⌊c ^ n⌋₊) at_top at_top :=
    tendsto_nat_floor_at_top.comp (tendsto_pow_at_top_at_top_of_one_lt c_one),
  convert hω.sub (h'ω.comp_tendsto A),
  ext1 n,
  simp,
end

#exit


tsum_prob_mem_Ioi_lt_top
  {X : Ω → ℝ} (hint : integrable X) (hnonneg : 0 ≤ X) {K : ℕ} :
  ∑' (j : ℕ), ℙ {ω | X ω ∈ set.Ioi (j : ℝ)} < ∞

theorem
  strong_law1
  (X : ℕ → Ω → ℝ) (hint : ∀ i, integrable (X i))
  (hindep : pairwise (λ i j, indep_fun (X i) (X j)))
  (hident : ∀ i, identically_distributed (X i) (X 0))
  (hnonneg : ∀ i ω, 0 ≤ X i ω) :
  ∀ᵐ ω, tendsto (λ (n : ℕ), (n ⁻¹ : ℝ) * (∑ i in range n, X i ω)) at_top (𝓝 (𝔼[X 0])) :=
begin
  let ρ : measure ℝ := measure.map (X 0) ℙ,
  have A : ∀ i, strongly_measurable (indicator (set.Ioc (-i : ℝ) i) id) :=
    λ i, strongly_measurable_id.indicator measurable_set_Ioc,
  set Y := λ (n : ℕ), truncation (X n) n with hY,
  have I1 : ∀ K, ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * Var[Y j] ≤ 2 * 𝔼[X 0],
  sorry { assume K,
    calc ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * Var[Y j] ≤
      ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * 𝔼[(truncation (X 0) j)^2] :
      begin
        apply sum_le_sum (λ j hj, _),
        refine mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (sq_nonneg _)),
        refine variance_le_expectation_sq.trans _,
        apply le_of_eq,
        change ∫ a, (truncation (X j) j a) ^ 2 = ∫ a, (truncation (X 0) j a) ^ 2,
        rw [moment_truncation_eq_interval_integral_of_nonneg (hint j).1 two_ne_zero (hnonneg j),
          moment_truncation_eq_interval_integral_of_nonneg (hint 0).1 two_ne_zero (hnonneg 0),
          (hident j).distrib_eq],
      end
      ... ≤ 2 * 𝔼[X 0] : sum_variance_truncation_le (hint 0) (hnonneg 0) K },
  set S := λ n, ∑ i in range n, Y i with hS,
  have : tendsto (λ (n : ℕ), (n ⁻¹ : ℝ) * (∑ i in range n, 𝔼[Y i])) at_top (𝓝 (𝔼[X 0])),
  sorry { apply filter.tendsto.cesaro,
    convert (tendsto_integral_truncation (hint 0)).comp tendsto_coe_nat_at_top_at_top,
    ext i,
    calc 𝔼[Y i] = ∫ x, (indicator (set.Ioc (-i : ℝ) i) id) x ∂(measure.map (X i) ℙ) :
      by { rw integral_map (hint i).ae_measurable (A i).ae_strongly_measurable, refl }
    ... = ∫ x, (indicator (set.Ioc (-i : ℝ) i) id) x ∂(measure.map (X 0) ℙ) : by rw hident i
    ... = 𝔼[truncation (X 0) i] :
    by { rw integral_map (hint 0).ae_measurable (A i).ae_strongly_measurable, refl } },
  have c : ℝ := sorry,
  have c_one : 1 < c := sorry,
  have c_pos : 0 < c := sorry,
  let u : ℕ → ℕ := λ n, ⌊c ^ n⌋₊,
  have u_mono : monotone u := sorry,
  have ε : ℝ := sorry,
  have εpos : 0 < ε := sorry,
  let C := (c ^ 5 * (c - 1) ⁻¹ ^ 3) * (2 * 𝔼[X 0]),
  have I2 : ∀ N, ∑ i in range N, ((u i : ℝ) ^ 2) ⁻¹ * Var[S (u i)] ≤ C,
  sorry { assume N,
    calc
    ∑ i in range N, ((u i : ℝ) ^ 2) ⁻¹ * Var[S (u i)]
        = ∑ i in range N, ((u i : ℝ) ^ 2) ⁻¹ * (∑ j in range (u i), Var[Y j]) :
      begin
        congr' 1 with i,
        congr' 1,
        rw [hS, indep_fun.Var_sum],
        { assume j hj,
          exact (hint j).1.mem_ℒp_truncation },
        { assume k hk l hl hkl,
          exact (hindep k l hkl).comp (A k).measurable (A l).measurable }
      end
    ... = ∑ j in range (u (N - 1)),
            (∑ i in (range N).filter (λ i, j < u i), ((u i : ℝ) ^ 2) ⁻¹) * Var[Y j] :
      begin
        simp_rw [mul_sum, sum_mul, sum_sigma'],
        refine sum_bij' (λ (p : (Σ (i : ℕ), ℕ)) hp, (⟨p.2, p.1⟩ : (Σ (i : ℕ), ℕ))) _ (λ a ha, rfl)
          (λ (p : (Σ (i : ℕ), ℕ)) hp, (⟨p.2, p.1⟩ : (Σ (i : ℕ), ℕ))) _ _ _,
        { rintros ⟨i, j⟩ hij,
          simp only [mem_sigma, mem_range] at hij,
          simp only [hij.1, hij.2, mem_sigma, mem_range, mem_filter, and_true],
          exact hij.2.trans_le (u_mono (nat.le_pred_of_lt hij.1)) },
        { rintros ⟨i, j⟩ hij,
          simp only [mem_sigma, mem_range, mem_filter] at hij,
          simp only [hij.2.1, hij.2.2, mem_sigma, mem_range, and_self] },
        { rintros ⟨i, j⟩ hij, refl },
        { rintros ⟨i, j⟩ hij, refl },
      end
    ... ≤ ∑ j in range (u (N - 1)), (c ^ 5 * (c - 1) ⁻¹ ^ 3 / j ^ 2) * Var[Y j] :
      begin
        apply sum_le_sum (λ j hj, _),
        rcases @eq_zero_or_pos _ _ j with rfl|hj,
        { simp only [Y, nat.cast_zero, zero_pow', ne.def, bit0_eq_zero, nat.one_ne_zero,
            not_false_iff, div_zero, zero_mul],
          simp only [nat.cast_zero, truncation_zero, variance_zero, mul_zero] },
        apply mul_le_mul_of_nonneg_right _ (variance_nonneg _ _),
        convert aux_sum_horrible2 N (nat.cast_pos.2 hj) c_one,
        { simp only [nat.cast_lt] },
        { simp only [one_div] }
      end
    ... = (c ^ 5 * (c - 1) ⁻¹ ^ 3) * ∑ j in range (u (N - 1)), ((j : ℝ) ^ 2) ⁻¹ * Var[Y j] :
        by { simp_rw [mul_sum, div_eq_mul_inv], ring_nf }
    ... ≤ (c ^ 5 * (c - 1) ⁻¹ ^ 3) * (2 * 𝔼[X 0]) :
      begin
        apply mul_le_mul_of_nonneg_left (I1 _),
        apply mul_nonneg (pow_nonneg c_pos.le _),
        exact pow_nonneg (inv_nonneg.2 (sub_nonneg.2 c_one.le)) _
      end },
  have I3 : ∀ N, ∑ i in range N,
    ℙ {ω | (u i * ε : ℝ) ≤ |S (u i) ω - 𝔼[S (u i)]|} ≤ ennreal.of_real (ε ⁻¹ ^ 2 * C),
  sorry { assume N,
    calc ∑ i in range N, ℙ {ω | (u i * ε : ℝ) ≤ |S (u i) ω - 𝔼[S (u i)]|}
        ≤ ∑ i in range N, ennreal.of_real (Var[S (u i)] / (u i * ε) ^ 2) :
      begin
        refine sum_le_sum (λ i hi, _),
        apply meas_ge_le_mul_variance,
        { exact mem_ℒp_finset_sum' _ (λ j hj, (hint j).1.mem_ℒp_truncation) },
        { apply mul_pos (nat.cast_pos.2 _) εpos,
          refine zero_lt_one.trans_le _,
          apply nat.le_floor,
          rw nat.cast_one,
          apply one_le_pow_of_one_le c_one.le }
      end
    ... = ennreal.of_real (∑ i in range N, Var[S (u i)] / (u i * ε) ^ 2) :
      begin
        rw ennreal.of_real_sum_of_nonneg (λ i hi, _),
        exact div_nonneg (variance_nonneg _ _) (sq_nonneg _),
      end
    ... ≤ ennreal.of_real (ε ⁻¹ ^ 2 * C) :
      begin
        apply ennreal.of_real_le_of_real,
        simp_rw [div_eq_inv_mul, ← inv_pow₀, mul_inv₀, mul_comm _ (ε⁻¹), mul_pow, mul_assoc,
          ← mul_sum],
        refine mul_le_mul_of_nonneg_left _ (sq_nonneg _),
        simp_rw [inv_pow₀],
        exact I2 N
      end },
  have I4 : ∑' i, ℙ {ω | (u i * ε : ℝ) ≤ |S (u i) ω - 𝔼[S (u i)]|} < ∞ :=
    (le_of_tendsto_of_tendsto' (ennreal.tendsto_nat_tsum _) tendsto_const_nhds I3).trans_lt
      ennreal.of_real_lt_top,
  have I5 : ∀ᵐ ω, ∀ᶠ i in at_top, ¬((u i * ε : ℝ) ≤ |S (u i) ω - 𝔼[S (u i)]|) :=
    ae_eventually_not_mem I4.ne,

end

end probability_theory

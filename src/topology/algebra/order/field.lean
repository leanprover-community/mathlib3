/-
Copyright (c) 2022 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson, Devon Tuma, Eric Rodriguez, Oliver Nash
-/

import tactic.positivity
import tactic.linarith
import topology.algebra.order.group
import topology.algebra.field

/-!
# Topologies on linear ordered fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


open set filter topological_space
open function
open order_dual (to_dual of_dual)
open_locale topology classical filter

variables {α β : Type*}
variables [linear_ordered_field α] [topological_space α] [order_topology α]
variables {l : filter β} {f g : β → α}

section continuous_mul

lemma mul_tendsto_nhds_zero_right (x : α) :
  tendsto (uncurry ((*) : α → α → α)) (𝓝 0 ×ᶠ 𝓝 x) $ 𝓝 0 :=
begin
  have hx : 0 < 2 * (1 + |x|) := by positivity,
  rw ((nhds_basis_zero_abs_sub_lt α).prod $ nhds_basis_abs_sub_lt x).tendsto_iff
     (nhds_basis_zero_abs_sub_lt α),
  refine λ ε ε_pos, ⟨(ε/(2 * (1 + |x|)), 1), ⟨div_pos ε_pos hx, zero_lt_one⟩, _⟩,
  suffices : ∀ (a b : α), |a| < ε / (2 * (1 + |x|)) → |b - x| < 1 → |a| * |b| < ε,
  by simpa only [and_imp, prod.forall, mem_prod, ← abs_mul],
  intros a b h h',
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left _ (abs_nonneg a)) ((lt_div_iff hx).1 h),
  calc |b| = |(b - x) + x| : by rw sub_add_cancel b x
    ... ≤ |b - x| + |x| : abs_add (b - x) x
    ... ≤ 2 * (1 + |x|) : by linarith,
end

lemma mul_tendsto_nhds_zero_left (x : α) :
  tendsto (uncurry ((*) : α → α → α)) (𝓝 x ×ᶠ 𝓝 0) $ 𝓝 0 :=
begin
  intros s hs,
  have := mul_tendsto_nhds_zero_right x hs,
  rw [filter.mem_map, mem_prod_iff] at this ⊢,
  obtain ⟨U, hU, V, hV, h⟩ := this,
  exact ⟨V, hV, U, hU, λ y hy, ((mul_comm y.2 y.1) ▸
    h (⟨hy.2, hy.1⟩ : (prod.mk y.2 y.1) ∈ U ×ˢ V) : y.1 * y.2 ∈ s)⟩,
end

lemma nhds_eq_map_mul_left_nhds_one {x₀ : α} (hx₀ : x₀ ≠ 0) :
  𝓝 x₀ = map (λ x, x₀*x) (𝓝 1) :=
begin
  have hx₀' : 0 < |x₀| := abs_pos.2 hx₀,
  refine filter.ext (λ t, _),
  simp only [exists_prop, set_of_subset_set_of, (nhds_basis_abs_sub_lt x₀).mem_iff,
    (nhds_basis_abs_sub_lt (1 : α)).mem_iff, filter.mem_map'],
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨i, hi, hit⟩ := h,
    refine ⟨i / (|x₀|), div_pos hi (abs_pos.2 hx₀), λ x hx, hit _⟩,
    calc |x₀ * x - x₀| = |x₀ * (x - 1)| : congr_arg abs (by ring_nf)
      ... = |x₀| * |x - 1| : abs_mul x₀ (x - 1)
      ... < |x₀| * (i / |x₀|) : mul_lt_mul' le_rfl hx (by positivity) (abs_pos.2 hx₀)
      ... = |x₀| * i / |x₀| : by ring
      ... = i : mul_div_cancel_left i (λ h, hx₀ (abs_eq_zero.1 h)) },
  { obtain ⟨i, hi, hit⟩ := h,
    refine ⟨i * |x₀|, mul_pos hi (abs_pos.2 hx₀), λ x hx, _⟩,
    have : |x / x₀ - 1| < i,
    calc |x / x₀ - 1| = |x / x₀ - x₀ / x₀| : (by rw div_self hx₀)
    ... = |(x - x₀) / x₀| : congr_arg abs (sub_div x x₀ x₀).symm
    ... = |x - x₀| / |x₀| : abs_div (x - x₀) x₀
    ... < i * |x₀| / |x₀| : div_lt_div_of_lt (abs_pos.2 hx₀) hx
    ... = i : by rw [← mul_div_assoc', div_self (ne_of_lt $ abs_pos.2 hx₀).symm, mul_one],
    specialize hit (x / x₀) this,
    rwa [mul_div_assoc', mul_div_cancel_left x hx₀] at hit }
end

lemma nhds_eq_map_mul_right_nhds_one {x₀ : α} (hx₀ : x₀ ≠ 0) :
  𝓝 x₀ = map (λ x, x*x₀) (𝓝 1) :=
by simp_rw [mul_comm _ x₀, nhds_eq_map_mul_left_nhds_one hx₀]

lemma mul_tendsto_nhds_one_nhds_one :
  tendsto (uncurry ((*) : α → α → α)) (𝓝 1 ×ᶠ 𝓝 1) $ 𝓝 1 :=
begin
  rw ((nhds_basis_Ioo_pos (1 : α)).prod $ nhds_basis_Ioo_pos (1 : α)).tendsto_iff
     (nhds_basis_Ioo_pos_of_pos (zero_lt_one : (0 : α) < 1)),
  intros ε hε,
  have hε' : 0 ≤ 1 - ε / 4 := by linarith,
  have ε_pos : 0 < ε / 4 := by linarith,
  have ε_pos' : 0 < ε / 2 := by linarith,
  simp only [and_imp, prod.forall, mem_Ioo, function.uncurry_apply_pair, mem_prod, prod.exists],
  refine ⟨ε/4, ε/4, ⟨ε_pos, ε_pos⟩, λ a b ha ha' hb hb', _⟩,
  have ha0 : 0 ≤ a := le_trans hε' (le_of_lt ha),
  have hb0 : 0 ≤ b := le_trans hε' (le_of_lt hb),
  refine ⟨lt_of_le_of_lt _ (mul_lt_mul'' ha hb hε' hε'),
    lt_of_lt_of_le (mul_lt_mul'' ha' hb' ha0 hb0) _⟩,
  { calc 1 - ε = 1 - ε / 2 - ε/2 : by ring_nf
    ... ≤ 1 - ε/2 - ε/2 + (ε/2)*(ε/2) : le_add_of_nonneg_right (by positivity)
    ... = (1 - ε/2) * (1 - ε/2) : by ring_nf
    ... ≤ (1 - ε/4) * (1 - ε/4) : mul_le_mul (by linarith) (by linarith) (by linarith) hε' },
  { calc (1 + ε/4) * (1 + ε/4) = 1 + ε/2 + (ε/4)*(ε/4) : by ring_nf
    ... = 1 + ε/2 + (ε * ε) / 16 : by ring_nf
    ... ≤ 1 + ε/2 + ε/2 : add_le_add_left (div_le_div (le_of_lt hε.1) (le_trans
      ((mul_le_mul_left hε.1).2 hε.2) (le_of_eq $ mul_one ε)) zero_lt_two (by linarith)) (1 + ε/2)
    ... ≤ 1 + ε : by ring_nf }
end

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_field.has_continuous_mul : has_continuous_mul α :=
⟨begin
  rw continuous_iff_continuous_at,
  rintro ⟨x₀, y₀⟩,
  by_cases hx₀ : x₀ = 0,
  { rw [hx₀, continuous_at, zero_mul, nhds_prod_eq],
    exact mul_tendsto_nhds_zero_right y₀ },
  by_cases hy₀ : y₀ = 0,
  { rw [hy₀, continuous_at, mul_zero, nhds_prod_eq],
    exact mul_tendsto_nhds_zero_left x₀ },
  have hxy : x₀ * y₀ ≠ 0 := mul_ne_zero hx₀ hy₀,
  have key : (λ p : α × α, x₀ * p.1 * (p.2 * y₀)) = ((λ x, x₀*x) ∘ (λ x, x*y₀)) ∘ (uncurry (*)),
  { ext p, simp [uncurry, mul_assoc] },
  have key₂ : (λ x, x₀*x) ∘ (λ x, y₀*x) = λ x, (x₀ *y₀)*x,
  { ext x, simp },
  calc map (uncurry (*)) (𝓝 (x₀, y₀))
      = map (uncurry (*)) (𝓝 x₀ ×ᶠ 𝓝 y₀) : by rw nhds_prod_eq
  ... = map (λ (p : α × α), x₀ * p.1 * (p.2 * y₀)) ((𝓝 1) ×ᶠ (𝓝 1))
          : by rw [uncurry, nhds_eq_map_mul_left_nhds_one hx₀, nhds_eq_map_mul_right_nhds_one hy₀,
                    prod_map_map_eq, filter.map_map]
  ... = map ((λ x, x₀ * x) ∘ λ x, x * y₀) (map (uncurry (*)) (𝓝 1 ×ᶠ 𝓝 1))
          : by rw [key, ← filter.map_map]
  ... ≤ map ((λ (x : α), x₀ * x) ∘ λ x, x * y₀) (𝓝 1) : map_mono (mul_tendsto_nhds_one_nhds_one)
  ... = 𝓝 (x₀*y₀) : by rw [← filter.map_map, ← nhds_eq_map_mul_right_nhds_one hy₀,
    nhds_eq_map_mul_left_nhds_one hy₀, filter.map_map, key₂, ← nhds_eq_map_mul_left_nhds_one hxy],
end⟩

end continuous_mul

/-- In a linearly ordered field with the order topology, if `f` tends to `at_top` and `g` tends to
a positive constant `C` then `f * g` tends to `at_top`. -/
lemma filter.tendsto.at_top_mul {C : α} (hC : 0 < C) (hf : tendsto f l at_top)
  (hg : tendsto g l (𝓝 C)) :
  tendsto (λ x, (f x * g x)) l at_top :=
begin
  refine tendsto_at_top_mono' _ _ (hf.at_top_mul_const (half_pos hC)),
  filter_upwards [hg.eventually (lt_mem_nhds (half_lt_self hC)),
    hf.eventually (eventually_ge_at_top 0)] with x hg hf using mul_le_mul_of_nonneg_left hg.le hf,
end

/-- In a linearly ordered field with the order topology, if `f` tends to a positive constant `C` and
`g` tends to `at_top` then `f * g` tends to `at_top`. -/
lemma filter.tendsto.mul_at_top {C : α} (hC : 0 < C) (hf : tendsto f l (𝓝 C))
  (hg : tendsto g l at_top) :
  tendsto (λ x, (f x * g x)) l at_top :=
by simpa only [mul_comm] using hg.at_top_mul hC hf

/-- In a linearly ordered field with the order topology, if `f` tends to `at_top` and `g` tends to
a negative constant `C` then `f * g` tends to `at_bot`. -/
lemma filter.tendsto.at_top_mul_neg {C : α} (hC : C < 0) (hf : tendsto f l at_top)
  (hg : tendsto g l (𝓝 C)) :
  tendsto (λ x, (f x * g x)) l at_bot :=
by simpa only [(∘), neg_mul_eq_mul_neg, neg_neg]
  using tendsto_neg_at_top_at_bot.comp (hf.at_top_mul (neg_pos.2 hC) hg.neg)

/-- In a linearly ordered field with the order topology, if `f` tends to a negative constant `C` and
`g` tends to `at_top` then `f * g` tends to `at_bot`. -/
lemma filter.tendsto.neg_mul_at_top {C : α} (hC : C < 0) (hf : tendsto f l (𝓝 C))
  (hg : tendsto g l at_top) :
  tendsto (λ x, (f x * g x)) l at_bot :=
by simpa only [mul_comm] using hg.at_top_mul_neg hC hf

/-- In a linearly ordered field with the order topology, if `f` tends to `at_bot` and `g` tends to
a positive constant `C` then `f * g` tends to `at_bot`. -/
lemma filter.tendsto.at_bot_mul {C : α} (hC : 0 < C) (hf : tendsto f l at_bot)
  (hg : tendsto g l (𝓝 C)) :
  tendsto (λ x, (f x * g x)) l at_bot :=
by simpa [(∘)]
  using tendsto_neg_at_top_at_bot.comp ((tendsto_neg_at_bot_at_top.comp hf).at_top_mul hC hg)

/-- In a linearly ordered field with the order topology, if `f` tends to `at_bot` and `g` tends to
a negative constant `C` then `f * g` tends to `at_top`. -/
lemma filter.tendsto.at_bot_mul_neg {C : α} (hC : C < 0) (hf : tendsto f l at_bot)
  (hg : tendsto g l (𝓝 C)) :
  tendsto (λ x, (f x * g x)) l at_top :=
by simpa [(∘)]
  using tendsto_neg_at_bot_at_top.comp ((tendsto_neg_at_bot_at_top.comp hf).at_top_mul_neg hC hg)

/-- In a linearly ordered field with the order topology, if `f` tends to a positive constant `C` and
`g` tends to `at_bot` then `f * g` tends to `at_bot`. -/
lemma filter.tendsto.mul_at_bot {C : α} (hC : 0 < C) (hf : tendsto f l (𝓝 C))
  (hg : tendsto g l at_bot) :
  tendsto (λ x, (f x * g x)) l at_bot :=
by simpa only [mul_comm] using hg.at_bot_mul hC hf

/-- In a linearly ordered field with the order topology, if `f` tends to a negative constant `C` and
`g` tends to `at_bot` then `f * g` tends to `at_top`. -/
lemma filter.tendsto.neg_mul_at_bot {C : α} (hC : C < 0) (hf : tendsto f l (𝓝 C))
  (hg : tendsto g l at_bot) :
  tendsto (λ x, (f x * g x)) l at_top :=
by simpa only [mul_comm] using hg.at_bot_mul_neg hC hf

/-- The function `x ↦ x⁻¹` tends to `+∞` on the right of `0`. -/
lemma tendsto_inv_zero_at_top : tendsto (λx:α, x⁻¹) (𝓝[>] (0:α)) at_top :=
begin
  refine (at_top_basis' 1).tendsto_right_iff.2 (λ b hb, _),
  have hb' : 0 < b := by positivity,
  filter_upwards [Ioc_mem_nhds_within_Ioi ⟨le_rfl, inv_pos.2 hb'⟩]
    with x hx using (le_inv hx.1 hb').1 hx.2,
end

/-- The function `r ↦ r⁻¹` tends to `0` on the right as `r → +∞`. -/
lemma tendsto_inv_at_top_zero' : tendsto (λr:α, r⁻¹) at_top (𝓝[>] (0:α)) :=
begin
  refine (has_basis.tendsto_iff at_top_basis ⟨λ s, mem_nhds_within_Ioi_iff_exists_Ioc_subset⟩).2 _,
  refine λ b hb, ⟨b⁻¹, trivial, λ x hx, _⟩,
  have : 0 < x := lt_of_lt_of_le (inv_pos.2 hb) hx,
  exact ⟨inv_pos.2 this, (inv_le this hb).2 hx⟩
end

lemma tendsto_inv_at_top_zero : tendsto (λr:α, r⁻¹) at_top (𝓝 0) :=
tendsto_inv_at_top_zero'.mono_right inf_le_left

lemma filter.tendsto.div_at_top [has_continuous_mul α] {f g : β → α} {l : filter β} {a : α}
  (h : tendsto f l (𝓝 a)) (hg : tendsto g l at_top) : tendsto (λ x, f x / g x) l (𝓝 0) :=
by { simp only [div_eq_mul_inv], exact mul_zero a ▸ h.mul (tendsto_inv_at_top_zero.comp hg) }

lemma filter.tendsto.inv_tendsto_at_top (h : tendsto f l at_top) : tendsto (f⁻¹) l (𝓝 0) :=
tendsto_inv_at_top_zero.comp h

lemma filter.tendsto.inv_tendsto_zero (h : tendsto f l (𝓝[>] 0)) :
  tendsto (f⁻¹) l at_top :=
tendsto_inv_zero_at_top.comp h

/-- The function `x^(-n)` tends to `0` at `+∞` for any positive natural `n`.
A version for positive real powers exists as `tendsto_rpow_neg_at_top`. -/
lemma tendsto_pow_neg_at_top {n : ℕ} (hn : n ≠ 0) : tendsto (λ x : α, x ^ (-(n:ℤ))) at_top (𝓝 0) :=
by simpa only [zpow_neg, zpow_coe_nat] using (@tendsto_pow_at_top α _ _ hn).inv_tendsto_at_top

lemma tendsto_zpow_at_top_zero {n : ℤ} (hn : n < 0) :
  tendsto (λ x : α, x^n) at_top (𝓝 0) :=
begin
  lift -n to ℕ using le_of_lt (neg_pos.mpr hn) with N,
  rw [← neg_pos, ← h, nat.cast_pos] at hn,
  simpa only [h, neg_neg] using tendsto_pow_neg_at_top hn.ne'
end

lemma tendsto_const_mul_zpow_at_top_zero {n : ℤ} {c : α} (hn : n < 0) :
  tendsto (λ x, c * x ^ n) at_top (𝓝 0) :=
(mul_zero c) ▸ (filter.tendsto.const_mul c (tendsto_zpow_at_top_zero hn))

lemma tendsto_const_mul_pow_nhds_iff' {n : ℕ} {c d : α} :
  tendsto (λ x : α, c * x ^ n) at_top (𝓝 d) ↔ (c = 0 ∨ n = 0) ∧ c = d :=
begin
  rcases eq_or_ne n 0 with (rfl|hn),
  { simp [tendsto_const_nhds_iff] },
  rcases lt_trichotomy c 0 with hc|rfl|hc,
  { have := tendsto_const_mul_pow_at_bot_iff.2 ⟨hn, hc⟩,
    simp [not_tendsto_nhds_of_tendsto_at_bot this, hc.ne, hn] },
  { simp [tendsto_const_nhds_iff] },
  { have := tendsto_const_mul_pow_at_top_iff.2 ⟨hn, hc⟩,
    simp [not_tendsto_nhds_of_tendsto_at_top this, hc.ne', hn] }
end

lemma tendsto_const_mul_pow_nhds_iff {n : ℕ} {c d : α} (hc : c ≠ 0) :
  tendsto (λ x : α, c * x ^ n) at_top (𝓝 d) ↔ n = 0 ∧ c = d :=
by simp [tendsto_const_mul_pow_nhds_iff', hc]

lemma tendsto_const_mul_zpow_at_top_nhds_iff {n : ℤ} {c d : α} (hc : c ≠ 0) :
  tendsto (λ x : α, c * x ^ n) at_top (𝓝 d) ↔ (n = 0 ∧ c = d) ∨ (n < 0 ∧ d = 0) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { by_cases hn : 0 ≤ n,
    { lift n to ℕ using hn,
      simp only [zpow_coe_nat] at h,
      rw [tendsto_const_mul_pow_nhds_iff hc, ← int.coe_nat_eq_zero] at h,
      exact or.inl h },
    { rw not_le at hn,
      refine or.inr ⟨hn, tendsto_nhds_unique h (tendsto_const_mul_zpow_at_top_zero hn)⟩ } },
  { cases h,
    { simp only [h.left, h.right, zpow_zero, mul_one],
      exact tendsto_const_nhds },
    { exact h.2.symm ▸ tendsto_const_mul_zpow_at_top_zero h.1} }
end

-- TODO: With a different proof, this could be possibly generalised to only require a
-- `linear_ordered_semifield` instance, which would also remove the need for the
-- `nnreal` instance of `has_continuous_inv₀`.
@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_field.to_topological_division_ring : topological_division_ring α :=
{ continuous_at_inv₀ :=
  begin
    suffices : ∀ {x : α}, 0 < x → continuous_at has_inv.inv x,
    { intros x hx,
      cases hx.symm.lt_or_lt,
      { exact this h },
      convert (this $ neg_pos.mpr h).neg.comp continuous_neg.continuous_at,
      ext,
      simp [neg_inv] },
    intros t ht,
    rw [continuous_at,
        (nhds_basis_Ioo_pos t).tendsto_iff $ nhds_basis_Ioo_pos_of_pos $ inv_pos.2 ht],
    rintros ε ⟨hε : ε > 0, hεt : ε ≤ t⁻¹⟩,
    refine ⟨min (t ^ 2 * ε / 2) (t / 2), by positivity, λ x h, _⟩,
    have hx : t / 2 < x,
    { rw [set.mem_Ioo, sub_lt_comm, lt_min_iff] at h,
      nlinarith },
    have hx' : 0 < x := (half_pos ht).trans hx,
    have aux : 0 < 2 / t ^ 2 := by positivity,
    rw [set.mem_Ioo, ←sub_lt_iff_lt_add', sub_lt_comm, ←abs_sub_lt_iff] at h ⊢,
    rw [inv_sub_inv ht.ne' hx'.ne', abs_div, div_eq_mul_inv],
    suffices : |t * x|⁻¹ < 2 / t ^ 2,
    { rw [←abs_neg, neg_sub],
      refine (mul_lt_mul'' h this (by positivity) (by positivity)).trans_le _,
      rw [mul_comm, mul_min_of_nonneg _ _ aux.le],
      apply min_le_of_left_le,
      rw [←mul_div, ←mul_assoc, div_mul_cancel _ (sq_pos_of_pos ht).ne',
          mul_div_cancel' ε two_ne_zero] },
    refine inv_lt_of_inv_lt aux _,
    rw [inv_div, abs_of_pos $ mul_pos ht hx', sq, ←mul_div_assoc'],
    exact mul_lt_mul_of_pos_left hx ht
  end }

lemma nhds_within_pos_comap_mul_left {x : α} (hx : 0 < x) :
  comap (λ ε, x * ε) (𝓝[>] 0) = 𝓝[>] 0 :=
begin
  suffices : ∀ {x : α} (hx : 0 < x), 𝓝[>] 0 ≤ comap (λ ε, x * ε) (𝓝[>] 0),
  { refine le_antisymm _ (this hx),
    have hr : 𝓝[>] (0 : α) = ((𝓝[>] (0 : α)).comap (λ ε, x⁻¹ * ε)).comap (λ ε, x * ε),
    { simp [comap_comap, inv_mul_cancel hx.ne.symm, comap_id, one_mul_eq_id], },
    conv_rhs { rw hr, },
    rw comap_le_comap_iff (by convert univ_mem; exact (mul_left_surjective₀ hx.ne.symm).range_eq),
    exact this (inv_pos.mpr hx), },
  intros x hx,
  convert nhds_within_le_comap (continuous_mul_left x).continuous_within_at,
  { exact (mul_zero _).symm, },
  { rw image_const_mul_Ioi_zero hx, },
end

lemma eventually_nhds_within_pos_mul_left {x : α} (hx : 0 < x)
  {p : α → Prop} (h : ∀ᶠ ε in 𝓝[>] 0, p ε) : ∀ᶠ ε in 𝓝[>] 0, p (x * ε) :=
begin
  convert h.comap (λ ε, x * ε),
  exact (nhds_within_pos_comap_mul_left hx).symm,
end

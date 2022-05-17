/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import analysis.complex.basic
import data.complex.exponential

/-!
# Complex and real exponential

In this file we prove continuity of `complex.exp` and `real.exp`. We also prove a few facts about
limits of `real.exp` at infinity.

## Tags

exp
-/

noncomputable theory

open finset filter metric asymptotics set function
open_locale classical topological_space

namespace complex

variables {z y x : ℝ}

lemma exp_bound_sq (x z : ℂ) (hz : ∥z∥ ≤ 1) :
  ∥exp (x + z) - exp x - z • exp x∥ ≤ ∥exp x∥ * ∥z∥ ^ 2 :=
calc ∥exp (x + z) - exp x - z * exp x∥
    = ∥exp x * (exp z - 1 - z)∥ : by { congr, rw [exp_add], ring }
... = ∥exp x∥ * ∥exp z - 1 - z∥ : norm_mul _ _
... ≤ ∥exp x∥ * ∥z∥^2 : mul_le_mul_of_nonneg_left (abs_exp_sub_one_sub_id_le hz) (norm_nonneg _)

lemma locally_lipschitz_exp {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_le : r ≤ 1) (x y : ℂ)
  (hyx : ∥y - x∥ < r) :
  ∥exp y - exp x∥ ≤ (1 + r) * ∥exp x∥ * ∥y - x∥ :=
begin
  have hy_eq : y = x + (y - x), by abel,
  have hyx_sq_le : ∥y - x∥ ^ 2 ≤ r * ∥y - x∥,
  { rw pow_two,
    exact mul_le_mul hyx.le le_rfl (norm_nonneg _) hr_nonneg, },
  have h_sq : ∀ z, ∥z∥ ≤ 1 → ∥exp (x + z) - exp x∥ ≤ ∥z∥ * ∥exp x∥ + ∥exp x∥ * ∥z∥ ^ 2,
  { intros z hz,
    have : ∥exp (x + z) - exp x - z • exp x∥ ≤ ∥exp x∥ * ∥z∥ ^ 2, from exp_bound_sq x z hz,
    rw [← sub_le_iff_le_add',  ← norm_smul z],
    exact (norm_sub_norm_le _ _).trans this, },
  calc ∥exp y - exp x∥ = ∥exp (x + (y - x)) - exp x∥ : by nth_rewrite 0 hy_eq
  ... ≤ ∥y - x∥ * ∥exp x∥ + ∥exp x∥ * ∥y - x∥ ^ 2 : h_sq (y - x) (hyx.le.trans hr_le)
  ... ≤ ∥y - x∥ * ∥exp x∥ + ∥exp x∥ * (r * ∥y - x∥) :
    add_le_add_left (mul_le_mul le_rfl hyx_sq_le (sq_nonneg _) (norm_nonneg _)) _
  ... = (1 + r) * ∥exp x∥ * ∥y - x∥ : by ring,
end

@[continuity] lemma continuous_exp : continuous exp :=
continuous_iff_continuous_at.mpr $
  λ x, continuous_at_of_locally_lipschitz zero_lt_one (2 * ∥exp x∥)
    (locally_lipschitz_exp zero_le_one le_rfl x)

lemma continuous_on_exp {s : set ℂ} : continuous_on exp s :=
continuous_exp.continuous_on

end complex

section complex_continuous_exp_comp

variable {α : Type*}

open complex

lemma filter.tendsto.cexp {l : filter α} {f : α → ℂ} {z : ℂ} (hf : tendsto f l (𝓝 z)) :
  tendsto (λ x, exp (f x)) l (𝓝 (exp z)) :=
(continuous_exp.tendsto _).comp hf

variables [topological_space α] {f : α → ℂ} {s : set α} {x : α}

lemma continuous_within_at.cexp (h : continuous_within_at f s x) :
  continuous_within_at (λ y, exp (f y)) s x :=
h.cexp

lemma continuous_at.cexp (h : continuous_at f x) : continuous_at (λ y, exp (f y)) x :=
h.cexp

lemma continuous_on.cexp (h : continuous_on f s) : continuous_on (λ y, exp (f y)) s :=
λ x hx, (h x hx).cexp

lemma continuous.cexp (h : continuous f) : continuous (λ y, exp (f y)) :=
continuous_iff_continuous_at.2 $ λ x, h.continuous_at.cexp

end complex_continuous_exp_comp

namespace real

@[continuity] lemma continuous_exp : continuous exp :=
complex.continuous_re.comp complex.continuous_of_real.cexp

lemma continuous_on_exp {s : set ℝ} : continuous_on exp s :=
continuous_exp.continuous_on

end real

section real_continuous_exp_comp

variable {α : Type*}

open real

lemma filter.tendsto.exp {l : filter α} {f : α → ℝ} {z : ℝ} (hf : tendsto f l (𝓝 z)) :
  tendsto (λ x, exp (f x)) l (𝓝 (exp z)) :=
(continuous_exp.tendsto _).comp hf

variables [topological_space α] {f : α → ℝ} {s : set α} {x : α}

lemma continuous_within_at.exp (h : continuous_within_at f s x) :
  continuous_within_at (λ y, exp (f y)) s x :=
h.exp

lemma continuous_at.exp (h : continuous_at f x) : continuous_at (λ y, exp (f y)) x :=
h.exp

lemma continuous_on.exp (h : continuous_on f s) : continuous_on (λ y, exp (f y)) s :=
λ x hx, (h x hx).exp

lemma continuous.exp (h : continuous f) : continuous (λ y, exp (f y)) :=
continuous_iff_continuous_at.2 $ λ x, h.continuous_at.exp

end real_continuous_exp_comp

namespace real

variables {x y z : ℝ}

/-- The real exponential function tends to `+∞` at `+∞`. -/
lemma tendsto_exp_at_top : tendsto exp at_top at_top :=
begin
  have A : tendsto (λx:ℝ, x + 1) at_top at_top :=
    tendsto_at_top_add_const_right at_top 1 tendsto_id,
  have B : ∀ᶠ x in at_top, x + 1 ≤ exp x :=
    eventually_at_top.2 ⟨0, λx hx, add_one_le_exp x⟩,
  exact tendsto_at_top_mono' at_top B A
end

/-- The real exponential function tends to `0` at `-∞` or, equivalently, `exp(-x)` tends to `0`
at `+∞` -/
lemma tendsto_exp_neg_at_top_nhds_0 : tendsto (λx, exp (-x)) at_top (𝓝 0) :=
(tendsto_inv_at_top_zero.comp tendsto_exp_at_top).congr (λx, (exp_neg x).symm)

/-- The real exponential function tends to `1` at `0`. -/
lemma tendsto_exp_nhds_0_nhds_1 : tendsto exp (𝓝 0) (𝓝 1) :=
by { convert continuous_exp.tendsto 0, simp }

lemma tendsto_exp_at_bot : tendsto exp at_bot (𝓝 0) :=
(tendsto_exp_neg_at_top_nhds_0.comp tendsto_neg_at_bot_at_top).congr $
  λ x, congr_arg exp $ neg_neg x

lemma tendsto_exp_at_bot_nhds_within : tendsto exp at_bot (𝓝[>] 0) :=
tendsto_inf.2 ⟨tendsto_exp_at_bot, tendsto_principal.2 $ eventually_of_forall exp_pos⟩

/-- The function `exp(x)/x^n` tends to `+∞` at `+∞`, for any natural number `n` -/
lemma tendsto_exp_div_pow_at_top (n : ℕ) : tendsto (λx, exp x / x^n) at_top at_top :=
begin
  refine (at_top_basis_Ioi.tendsto_iff (at_top_basis' 1)).2 (λ C hC₁, _),
  have hC₀ : 0 < C, from zero_lt_one.trans_le hC₁,
  have : 0 < (exp 1 * C)⁻¹ := inv_pos.2 (mul_pos (exp_pos _) hC₀),
  obtain ⟨N, hN⟩ : ∃ N, ∀ k ≥ N, (↑k ^ n : ℝ) / exp 1 ^ k < (exp 1 * C)⁻¹ :=
    eventually_at_top.1 ((tendsto_pow_const_div_const_pow_of_one_lt n
      (one_lt_exp_iff.2 zero_lt_one)).eventually (gt_mem_nhds this)),
  simp only [← exp_nat_mul, mul_one, div_lt_iff, exp_pos, ← div_eq_inv_mul] at hN,
  refine ⟨N, trivial, λ x hx, _⟩, rw set.mem_Ioi at hx,
  have hx₀ : 0 < x, from N.cast_nonneg.trans_lt hx,
  rw [set.mem_Ici, le_div_iff (pow_pos hx₀ _), ← le_div_iff' hC₀],
  calc x ^ n ≤ ⌈x⌉₊ ^ n : pow_le_pow_of_le_left hx₀.le (nat.le_ceil _) _
  ... ≤ exp ⌈x⌉₊ / (exp 1 * C) : (hN _ (nat.lt_ceil.2 hx).le).le
  ... ≤ exp (x + 1) / (exp 1 * C) : div_le_div_of_le (mul_pos (exp_pos _) hC₀).le
    (exp_le_exp.2 $ (nat.ceil_lt_add_one hx₀.le).le)
  ... = exp x / C : by rw [add_comm, exp_add, mul_div_mul_left _ _ (exp_pos _).ne']
end

/-- The function `x^n * exp(-x)` tends to `0` at `+∞`, for any natural number `n`. -/
lemma tendsto_pow_mul_exp_neg_at_top_nhds_0 (n : ℕ) : tendsto (λx, x^n * exp (-x)) at_top (𝓝 0) :=
(tendsto_inv_at_top_zero.comp (tendsto_exp_div_pow_at_top n)).congr $ λx,
  by rw [comp_app, inv_eq_one_div, div_div_eq_mul_div, one_mul, div_eq_mul_inv, exp_neg]

/-- The function `(b * exp x + c) / (x ^ n)` tends to `+∞` at `+∞`, for any natural number
`n` and any real numbers `b` and `c` such that `b` is positive. -/
lemma tendsto_mul_exp_add_div_pow_at_top (b c : ℝ) (n : ℕ) (hb : 0 < b) :
  tendsto (λ x, (b * exp x + c) / x ^ n) at_top at_top :=
begin
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp only [pow_zero, div_one],
    exact (tendsto_exp_at_top.const_mul_at_top hb).at_top_add tendsto_const_nhds },
  refine tendsto.congr' (eventually_eq_of_mem (Ioi_mem_at_top 0) _)
    (((tendsto_exp_div_pow_at_top n).const_mul_at_top hb).at_top_add
      ((tendsto_pow_neg_at_top hn).mul (@tendsto_const_nhds _ _ _ c _))),
  intros x hx,
  simp only [zpow_neg x n],
  ring,
end

/-- The function `(x ^ n) / (b * exp x + c)` tends to `0` at `+∞`, for any natural number
`n` and any real numbers `b` and `c` such that `b` is nonzero. -/
lemma tendsto_div_pow_mul_exp_add_at_top (b c : ℝ) (n : ℕ) (hb : 0 ≠ b) :
  tendsto (λ x, x ^ n / (b * exp x + c)) at_top (𝓝 0) :=
begin
  have H : ∀ d e, 0 < d → tendsto (λ (x:ℝ), x^n / (d * (exp x) + e)) at_top (𝓝 0),
  { intros b' c' h,
    convert (tendsto_mul_exp_add_div_pow_at_top b' c' n h).inv_tendsto_at_top ,
    ext x,
    simpa only [pi.inv_apply] using (inv_div _ _).symm },
  cases lt_or_gt_of_ne hb,
  { exact H b c h },
  { convert (H (-b) (-c) (neg_pos.mpr h)).neg,
    { ext x,
      field_simp,
      rw [← neg_add (b * exp x) c, neg_div_neg_eq] },
    { exact neg_zero.symm } },
end

/-- `real.exp` as an order isomorphism between `ℝ` and `(0, +∞)`. -/
def exp_order_iso : ℝ ≃o Ioi (0 : ℝ) :=
strict_mono.order_iso_of_surjective _ (exp_strict_mono.cod_restrict exp_pos) $
  (continuous_subtype_mk _ continuous_exp).surjective
    (by simp only [tendsto_Ioi_at_top, subtype.coe_mk, tendsto_exp_at_top])
    (by simp [tendsto_exp_at_bot_nhds_within])

@[simp] lemma coe_exp_order_iso_apply (x : ℝ) : (exp_order_iso x : ℝ) = exp x := rfl

@[simp] lemma coe_comp_exp_order_iso : coe ∘ exp_order_iso = exp := rfl

@[simp] lemma range_exp : range exp = Ioi 0 :=
by rw [← coe_comp_exp_order_iso, range_comp, exp_order_iso.range_eq, image_univ, subtype.range_coe]

@[simp] lemma map_exp_at_top : map exp at_top = at_top :=
by rw [← coe_comp_exp_order_iso, ← filter.map_map, order_iso.map_at_top, map_coe_Ioi_at_top]

@[simp] lemma comap_exp_at_top : comap exp at_top = at_top :=
by rw [← map_exp_at_top, comap_map exp_injective, map_exp_at_top]

@[simp] lemma tendsto_exp_comp_at_top {α : Type*} {l : filter α} {f : α → ℝ} :
  tendsto (λ x, exp (f x)) l at_top ↔ tendsto f l at_top :=
by rw [← tendsto_comap_iff, comap_exp_at_top]

lemma tendsto_comp_exp_at_top {α : Type*} {l : filter α} {f : ℝ → α} :
  tendsto (λ x, f (exp x)) at_top l ↔ tendsto f at_top l :=
by rw [← tendsto_map'_iff, map_exp_at_top]

@[simp] lemma map_exp_at_bot : map exp at_bot = 𝓝[>] 0 :=
by rw [← coe_comp_exp_order_iso, ← filter.map_map, exp_order_iso.map_at_bot, ← map_coe_Ioi_at_bot]

lemma comap_exp_nhds_within_Ioi_zero : comap exp (𝓝[>] 0) = at_bot :=
by rw [← map_exp_at_bot, comap_map exp_injective]

lemma tendsto_comp_exp_at_bot {α : Type*} {l : filter α} {f : ℝ → α} :
  tendsto (λ x, f (exp x)) at_bot l ↔ tendsto f (𝓝[>] 0) l :=
by rw [← map_exp_at_bot, tendsto_map'_iff]

lemma is_o_pow_exp_at_top {n : ℕ} : is_o (λ x, x^n) real.exp at_top :=
by simpa [is_o_iff_tendsto (λ x hx, ((exp_pos x).ne' hx).elim)]
  using tendsto_div_pow_mul_exp_add_at_top 1 0 n zero_ne_one

end real

namespace complex

/-- `complex.abs (complex.exp z) → ∞` as `complex.re z → ∞`. TODO: use `bornology.cobounded`. -/
lemma tendsto_exp_comap_re_at_top : tendsto exp (comap re at_top) (comap abs at_top) :=
by simpa only [tendsto_comap_iff, (∘), abs_exp] using real.tendsto_exp_at_top.comp tendsto_comap

/-- `complex.exp z → 0` as `complex.re z → -∞`.-/
lemma tendsto_exp_comap_re_at_bot : tendsto exp (comap re at_bot) (𝓝 0) :=
tendsto_zero_iff_norm_tendsto_zero.2 $
  by simpa only [norm_eq_abs, abs_exp] using real.tendsto_exp_at_bot.comp tendsto_comap

lemma tendsto_exp_comap_re_at_bot_nhds_within : tendsto exp (comap re at_bot) (𝓝[≠] 0) :=
tendsto_inf.2 ⟨tendsto_exp_comap_re_at_bot,
  tendsto_principal.2 $ eventually_of_forall $ exp_ne_zero⟩

end complex

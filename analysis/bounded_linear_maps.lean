/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Continuous linear functions -- functions between normed vector spaces which are bounded and linear.
-/
import algebra.field
import tactic.norm_num
import analysis.normed_space

@[simp] lemma mul_inv_eq' {α} [discrete_field α] (a b : α) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
classical.by_cases (assume : a = 0, by simp [this]) $ assume ha,
classical.by_cases (assume : b = 0, by simp [this]) $ assume hb,
mul_inv_eq hb ha

noncomputable theory
local attribute [instance] classical.prop_decidable

local notation f ` →_{`:50 a `} `:0 b := filter.tendsto f (nhds a) (nhds b)

open filter (tendsto)

variables {k : Type*} [normed_field k]
variables {E : Type*} [normed_space k E]
variables {F : Type*} [normed_space k F]
variables {G : Type*} [normed_space k G]

structure is_bounded_linear_map {k : Type*}
  [normed_field k] {E : Type*} [normed_space k E] {F : Type*} [normed_space k F] (L : E → F)
  extends is_linear_map L : Prop :=
(bound : ∃ M, M > 0 ∧ ∀ x : E, ∥ L x ∥ ≤ M * ∥ x ∥)

include k

lemma is_linear_map.with_bound
  {L : E → F} (hf : is_linear_map L) (M : ℝ) (h : ∀ x : E, ∥ L x ∥ ≤ M * ∥ x ∥) :
  is_bounded_linear_map L :=
⟨ hf, classical.by_cases
  (assume : M ≤ 0, ⟨1, zero_lt_one, assume x,
    le_trans (h x) $ mul_le_mul_of_nonneg_right (le_trans this zero_le_one) (norm_nonneg x)⟩)
  (assume : ¬ M ≤ 0, ⟨M, lt_of_not_ge this, h⟩)⟩

namespace is_bounded_linear_map

lemma zero : is_bounded_linear_map (λ (x:E), (0:F)) :=
(0 : E →ₗ F).is_linear.with_bound 0 $ by simp [le_refl]

lemma id : is_bounded_linear_map (λ (x:E), x) :=
linear_map.id.is_linear.with_bound 1 $ by simp [le_refl]

lemma smul {f : E → F} (c : k) : is_bounded_linear_map f → is_bounded_linear_map (λ e, c • f e)
| ⟨hf, ⟨M, hM, h⟩⟩ := (c • hf.mk' f).is_linear.with_bound (∥c∥ * M) $ assume x,
  calc ∥c • f x∥ = ∥c∥ * ∥f x∥ : norm_smul c (f x)
    ... ≤ ∥c∥ * (M * ∥x∥) : mul_le_mul_of_nonneg_left (h x) (norm_nonneg c)
    ... = (∥c∥ * M) * ∥x∥ : (mul_assoc _ _ _).symm

lemma neg {f : E → F} (hf : is_bounded_linear_map f) : is_bounded_linear_map (λ e, -f e) :=
begin
  rw show (λ e, -f e) = (λ e, (-1) • f e), { funext, simp },
  exact smul (-1) hf
end

lemma add {f : E → F} {g : E → F} :
  is_bounded_linear_map f → is_bounded_linear_map g → is_bounded_linear_map (λ e, f e + g e)
| ⟨hlf, Mf, hMf, hf⟩  ⟨hlg, Mg, hMg, hg⟩ := (hlf.mk' _ + hlg.mk' _).is_linear.with_bound (Mf + Mg) $ assume x,
  calc ∥f x + g x∥ ≤ ∥f x∥ + ∥g x∥ : norm_triangle _ _
    ... ≤ Mf * ∥x∥ + Mg * ∥x∥ : add_le_add (hf x) (hg x)
    ... ≤ (Mf + Mg) * ∥x∥ : by rw add_mul

lemma sub {f : E → F} {g : E → F} (hf : is_bounded_linear_map f) (hg : is_bounded_linear_map g) :
  is_bounded_linear_map (λ e, f e - g e) := add hf (neg hg)

lemma comp {f : E → F} {g : F → G} :
  is_bounded_linear_map g → is_bounded_linear_map f → is_bounded_linear_map (g ∘ f)
| ⟨hlg, Mg, hMg, hg⟩ ⟨hlf, Mf, hMf, hf⟩ := ((hlg.mk' _).comp (hlf.mk' _)).is_linear.with_bound (Mg * Mf) $ assume x,
  calc ∥g (f x)∥ ≤ Mg * ∥f x∥ : hg _
    ... ≤ Mg * (Mf * ∥x∥) : mul_le_mul_of_nonneg_left (hf _) (le_of_lt hMg)
    ... = Mg * Mf * ∥x∥ : (mul_assoc _ _ _).symm

lemma tendsto {L : E → F} (x : E) : is_bounded_linear_map L → L →_{x} (L x)
| ⟨hL, M, hM, h_ineq⟩ := tendsto_iff_norm_tendsto_zero.2 $
  squeeze_zero (assume e, norm_nonneg _)
    (assume e, calc ∥L e - L x∥ = ∥hL.mk' L (e - x)∥ : by rw (hL.mk' _).map_sub e x; refl
      ... ≤ M*∥e-x∥ : h_ineq (e-x))
    (suffices (λ (e : E), M * ∥e - x∥) →_{x} (M * 0), by simpa,
      tendsto_mul tendsto_const_nhds (lim_norm _))

lemma continuous {L : E → F} (hL : is_bounded_linear_map L) : continuous L :=
continuous_iff_tendsto.2 $ assume x, hL.tendsto x

lemma lim_zero_bounded_linear_map {L : E → F} (H : is_bounded_linear_map L) : (L →_{0} 0) :=
(H.1.mk' _).map_zero ▸ continuous_iff_tendsto.1 H.continuous 0

end is_bounded_linear_map

-- Next lemma is stated for real normed space but it would work as soon as the base field is an extension of ℝ
lemma bounded_continuous_linear_map
  {E : Type*} [normed_space ℝ E] {F : Type*} [normed_space ℝ F] {L : E → F}
  (lin : is_linear_map L) (cont : continuous L) : is_bounded_linear_map L :=
let ⟨δ, δ_pos, hδ⟩ := exists_delta_of_continuous cont zero_lt_one 0 in
have HL0 : L 0 = 0, from (lin.mk' _).map_zero,
have H : ∀{a}, ∥a∥ ≤ δ → ∥L a∥ < 1, by simpa only [HL0, dist_zero_right] using hδ,
lin.with_bound (δ⁻¹) $ assume x,
classical.by_cases (assume : x = 0, by simp only [this, HL0, norm_zero, mul_zero]) $
assume h : x ≠ 0,
let p := ∥x∥ * δ⁻¹, q := p⁻¹ in
have p_inv : p⁻¹ = δ*∥x∥⁻¹, by simp,

have norm_x_pos : ∥x∥ > 0 := (norm_pos_iff x).2 h,
have norm_x : ∥x∥ ≠ 0 := mt (norm_eq_zero x).1 h,

have p_pos : p > 0 := mul_pos norm_x_pos (inv_pos δ_pos),
have p0 : _ := ne_of_gt p_pos,
have q_pos : q > 0 := inv_pos p_pos,
have q0 : _ := ne_of_gt q_pos,

have ∥p⁻¹ • x∥ = δ := calc
  ∥p⁻¹ • x∥ = abs p⁻¹ * ∥x∥ : by rw norm_smul; refl
  ... = p⁻¹ * ∥x∥ : by rw [abs_of_nonneg $ le_of_lt q_pos]
  ... = δ : by simp [mul_assoc, inv_mul_cancel norm_x],

calc ∥L x∥ = (p * q) * ∥L x∥ : begin dsimp [q], rw [mul_inv_cancel p0, one_mul] end
  ... = p * ∥L (q • x)∥ : by simp [lin.smul, norm_smul, real.norm_eq_abs, abs_of_pos q_pos, mul_assoc]
  ... ≤ p * 1 : mul_le_mul_of_nonneg_left (le_of_lt $ H $ le_of_eq $ this) (le_of_lt p_pos)
  ... = δ⁻¹ * ∥x∥ : by rw [mul_one, mul_comm]

/-
Copyright (c) 2022 Cuma Kökmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cuma Kökmen, Yury Kudryashov
-/
import measure_theory.integral.circle_integral

/-!
# Integral over a torus in `ℂⁿ`

In this file we define the integral of a function `f : ℂⁿ → E` over a torus
`{z : ℂⁿ | ∀ i, z i ∈ metric.sphere (c i) (R i)}`. In order to do this, we define
`torus_map (c : ℂⁿ) (R θ : ℝⁿ)` to be the point in `ℂⁿ` given by $z_k=c_k+R_ke^{θ_ki}$,
where $i$ is the imaginary unit, then define `torus_integral f c R` as the integral over
the cube $[0, (λ _, 2π)] = \{θ\|∀ k, 0 ≤ θ_k ≤ 2π\}$ of the Jacobian of the
`torus_map` multiplied by `f (torus_map c R θ)`.

We also define a predicate saying that `f ∘ torus_map c R` is integrable on the cube
`[0, (λ _, 2\pi)]`.

## Main definitions

* `torus_map c R`: the generalized multidimensional exponential map from `ℝⁿ` to `ℂⁿ` that sends
  $θ=(θ_0,…,θ_{n-1})$ to $z=(z_0,…,z_{n-1})$, where $z_k= c_k + R_ke^{θ_k i}$;

* `torus_integrable f c R`: a function `f : ℂⁿ → E` is integrable over the generalized torus
  with center `c : ℂⁿ` and radius `R : ℝⁿ` if `f ∘ torus_map c R` is integrable on the
  closed cube `Icc (0 : ℝⁿ) (λ _, 2 * π)`;

* `torus_integral f c R`: the integral of a function `f : ℂⁿ → E` over a torus with
  center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ` defined as
  $\iiint_{[0, 2 * π]} (∏_{k = 1}^{n} i R_k e^{θ_k * i}) • f (c + Re^{θ_k i})\,dθ_0…dθ_{k-1}$.

## Main statements

* `torus_integral_dim0`, `torus_integral_dim1`, `torus_integral_succ`: formulas for `torus_integral`
  in cases of dimension `0`, `1`, and `n + 1`.

## Notations

- `ℝ⁰`, `ℝ¹`, `ℝⁿ`, `ℝⁿ⁺¹`: local notation for `fin 0 → ℝ`, `fin 1 → ℝ`, `fin n → ℝ`, and
  `fin (n + 1) → ℝ`, respectively;
- `ℂ⁰`, `ℂ¹`, `ℂⁿ`, `ℂⁿ⁺¹`: local notation for `fin 0 → ℂ`, `fin 1 → ℂ`, `fin n → ℂ`, and
  `fin (n + 1) → ℂ`, respectively;
- `∯ z in T(c, R), f z`: notation for `torus_integral f c R`;
- `∮ z in C(c, R), f z`: notation for `circle_integral f c R`, defined elsewhere;
- `∏ k, f k`: notation for `finset.prod`, defined elsewhere;
- `π`: notation for `real.pi`, defined elsewhere.

## Tags

integral, torus
-/

variable {n : ℕ}
variables {E : Type*} [normed_add_comm_group E]

noncomputable theory

open complex set measure_theory function filter topological_space
open_locale real big_operators

local notation `ℝ⁰` := fin 0 → ℝ
local notation `ℂ⁰` := fin 0 → ℂ
local notation `ℝ¹` := fin 1 → ℝ
local notation `ℂ¹` := fin 1 → ℂ
local notation `ℝⁿ` := fin n → ℝ
local notation `ℂⁿ` := fin n → ℂ
local notation `ℝⁿ⁺¹` := fin (n + 1) → ℝ
local notation `ℂⁿ⁺¹` := fin (n + 1) → ℂ

/-!
### `torus_map`, a generalization of a torus
-/

/-- The n dimensional exponential map $θ_i ↦ c + R e^{θ_i*I}, θ ∈ ℝⁿ$ representing
a torus in `ℂⁿ` with center `c ∈ ℂⁿ` and generalized radius `R ∈ ℝⁿ`, so we can adjust
it to every n axis. -/
def torus_map (c : ℂⁿ) (R : ℝⁿ) : ℝⁿ → ℂⁿ :=
λ θ i, c i + R i * exp(θ i * I)

lemma torus_map_sub_center (c : ℂⁿ) (R : ℝⁿ) (θ : ℝⁿ) :
  torus_map c R θ - c = torus_map 0 R θ :=
by { ext1 i, simp [torus_map] }

lemma torus_map_eq_center_iff {c : ℂⁿ} {R : ℝⁿ} {θ : ℝⁿ} :
  torus_map c R θ = c ↔ R = 0 :=
by simp [funext_iff, torus_map, exp_ne_zero]

@[simp] lemma torus_map_zero_radius (c : ℂⁿ) : torus_map c 0 = const ℝⁿ c :=
by { ext1, rw torus_map_eq_center_iff.2 rfl }

/-!
### Integrability of a function on a generalized torus
-/

/-- A function `f : ℂⁿ → E` is integrable on the generalized torus if the function
`f ∘ torus_map c R θ` is integrable on `Icc (0 : ℝⁿ) (λ _, 2 * π)`-/
def torus_integrable (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) : Prop :=
  integrable_on (λ (θ : ℝⁿ), f (torus_map c R θ)) (Icc (0 : ℝⁿ) (λ _, 2 * π)) volume

namespace torus_integrable

variables {f g : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ}

/-- Constant functions are torus integrable -/
lemma torus_integrable_const (a : E) (c : ℂⁿ) (R : ℝⁿ) :
  torus_integrable (λ _, a) c R :=
by simp [torus_integrable, measure_Icc_lt_top]

/-- If `f` is torus integrable then `-f` is torus integrable. -/
protected lemma neg (hf : torus_integrable f c R) : torus_integrable (-f) c R := hf.neg

/-- If `f` and `g` are two torus integrable functions, then so is `f + g`. -/
protected lemma add (hf : torus_integrable f c R) (hg : torus_integrable g c R) :
  torus_integrable (f + g) c R :=
hf.add hg

/-- If `f` and `g` are two torus integrable functions, then so is `f - g`. -/
protected lemma sub (hf : torus_integrable f c R) (hg : torus_integrable g c R) :
  torus_integrable (f - g) c R :=
hf.sub hg

lemma torus_integrable_zero_radius {f : ℂⁿ → E} {c : ℂⁿ} :
  torus_integrable f c 0 :=
begin
  rw [torus_integrable, torus_map_zero_radius],
  apply torus_integrable_const (f c) c 0,
end

/--The function given in the definition of `torus_integral` is integrable. -/
lemma function_integrable [normed_space ℂ E] (hf : torus_integrable f c R) :
  integrable_on (λ (θ : ℝⁿ), (∏ i, R i * exp(θ i * I) * I : ℂ) • f (torus_map c R θ))
                (Icc (0 : ℝⁿ) (λ _, 2 * π)) volume :=
begin
  refine (hf.norm.const_mul (∏ i, |R i|)).mono' _ _,
  { refine (continuous.ae_strongly_measurable _).smul hf.1,
    exact continuous_finset_prod finset.univ (λ i hi, (continuous_const.mul
      (((continuous_of_real.comp (continuous_apply i)).mul continuous_const).cexp)).mul
      continuous_const) },
  simp [norm_smul, map_prod],
end

end torus_integrable

variables [normed_space ℂ E] [complete_space E] {f g : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ}

/--The definition of the integral over a generalized torus with center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ`
as the `•`-product of the derivative of `torus_map` and `f (torus_map c R θ)`-/
def torus_integral (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) :=
∫ (θ : ℝⁿ) in Icc (0 : ℝⁿ) (λ _, 2 * π), (∏ i, R i * exp(θ i * I) * I : ℂ) • f (torus_map c R θ)

notation `∯` binders ` in ` `T(` c `, ` R `)` `, ` r:(scoped:60 f, torus_integral f c R) := r

lemma torus_integral_radius_zero (hn : n ≠ 0) (f : ℂⁿ → E) (c : ℂⁿ): ∯ x in T(c, 0), f x = 0 :=
by simp only [torus_integral, pi.zero_apply, of_real_zero, mul_zero, zero_mul, fin.prod_const,
  zero_pow' n hn, zero_smul, integral_zero]

lemma torus_integral_neg (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) :
  ∯ x in T(c, R), -f x = -∯ x in T(c, R), f x :=
by simp [torus_integral, integral_neg]

lemma torus_integral_add (hf : torus_integrable f c R) (hg : torus_integrable g c R) :
  ∯ x in T(c, R), f x + g x = (∯ x in T(c, R), f x) + ∯ x in T(c, R), g x :=
by simpa only [torus_integral, smul_add, pi.add_apply]
  using integral_add hf.function_integrable hg.function_integrable

lemma torus_integral_sub (hf : torus_integrable f c R) (hg : torus_integrable g c R) :
  ∯ x in T(c, R), f x - g x = (∯ x in T(c, R), f x) - ∯ x in T(c, R), g x :=
by simpa only [sub_eq_add_neg, ← torus_integral_neg] using torus_integral_add hf hg.neg

lemma torus_integral_smul {𝕜 : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E] [smul_comm_class 𝕜 ℂ E]
  (a : 𝕜) (f : ℂⁿ → E) (c : ℂⁿ) (R : ℝⁿ) :
  ∯ x in T(c, R), a • f x = a • ∯ x in T(c, R), f x :=
by simp only [torus_integral, integral_smul, ← smul_comm a]

lemma torus_integral_const_mul (a : ℂ) (f : ℂⁿ → ℂ) (c : ℂⁿ) (R : ℝⁿ) :
  ∯ x in T(c, R), a * f x = a * ∯ x in T(c, R), f x :=
torus_integral_smul a f c R

/--If for all `θ : ℝⁿ`, `‖f (torus_map c R θ)‖` is less than or equal to a constant `C : ℝ`, then
`‖∯ x in T(c, R), f x‖` is less than or equal to `(2 * π)^n * (∏ i, |R i|) * C`-/
lemma norm_torus_integral_le_of_norm_le_const {C : ℝ} (hf : ∀ θ, ‖f (torus_map c R θ)‖ ≤ C) :
  ‖∯ x in T(c, R), f x‖ ≤ (2 * π)^(n: ℕ) * (∏ i, |R i|) * C :=
calc ‖∯ x in T(c, R), f x‖ ≤ (∏ i, |R i|) * C * (volume (Icc (0 : ℝⁿ) (λ _, 2 * π))).to_real :
  norm_set_integral_le_of_norm_le_const' measure_Icc_lt_top measurable_set_Icc $ λ θ hθ,
    ( calc ‖(∏ i : fin n, R i * exp (θ i * I) * I : ℂ) • f (torus_map c R θ)‖
          = (∏ i : fin n, |R i|) * ‖f (torus_map c R θ)‖ : by simp [norm_smul]
      ... ≤ (∏ i : fin n, |R i|) * C :
        mul_le_mul_of_nonneg_left (hf _) (finset.prod_nonneg $ λ _ _, abs_nonneg _) )
... = (2 * π)^(n: ℕ) * (∏ i, |R i|) * C :
  by simp only [pi.zero_def, real.volume_Icc_pi_to_real (λ _, real.two_pi_pos.le), sub_zero,
      fin.prod_const, mul_assoc, mul_comm ((2 * π) ^ (n : ℕ))]

@[simp] lemma torus_integral_dim0 (f : ℂ⁰ → E) (c : ℂ⁰) (R : ℝ⁰) : ∯ x in T(c, R), f x = f c :=
by simp only [torus_integral, fin.prod_univ_zero, one_smul,
  subsingleton.elim (λ i : fin 0, 2 * π) 0, Icc_self, measure.restrict_singleton, volume_pi,
  integral_smul_measure, integral_dirac, measure.pi_of_empty _ 0,
  measure.dirac_apply_of_mem (mem_singleton _), subsingleton.elim (torus_map c R 0) c]

/-- In dimension one, `torus_integral` is the same as `circle_integral`
(up to the natural equivalence between `ℂ` and `fin 1 → ℂ`). -/
lemma torus_integral_dim1 (f : ℂ¹ → E) (c : ℂ¹) (R : ℝ¹) :
  ∯ x in T(c, R), f x = ∮ z in C(c 0, R 0), f (λ _, z) :=
begin
  have : (λ (x : ℝ) (b : fin 1), x) ⁻¹' Icc 0 (λ _, 2 * π) = Icc 0 (2 * π),
    from (order_iso.fun_unique (fin 1) ℝ).symm.preimage_Icc _ _,
  simp only [torus_integral, circle_integral, interval_integral.integral_of_le real.two_pi_pos.le,
    measure.restrict_congr_set Ioc_ae_eq_Icc, deriv_circle_map, fin.prod_univ_one,
    ← ((volume_preserving_fun_unique (fin 1) ℝ).symm _).set_integral_preimage_emb
      (measurable_equiv.measurable_embedding _), this, measurable_equiv.fun_unique_symm_apply],
  simp only [torus_map, circle_map, zero_add],
  rcongr
end

/-- Recurrent formula for `torus_integral`, see also `torus_integral_succ`. -/
lemma torus_integral_succ_above {f : ℂⁿ⁺¹ → E} {c : ℂⁿ⁺¹} {R : ℝⁿ⁺¹} (hf : torus_integrable f c R)
  (i : fin (n + 1)) :
  ∯ x in T(c, R), f x =
    ∮ x in C(c i, R i), ∯ y in T(c ∘ i.succ_above, R ∘ i.succ_above), f (i.insert_nth x y) :=
begin
  set e : ℝ × ℝⁿ ≃ᵐ ℝⁿ⁺¹ := (measurable_equiv.pi_fin_succ_above_equiv (λ _, ℝ) i).symm,
  have hem : measure_preserving e,
    from (volume_preserving_pi_fin_succ_above_equiv (λ j : fin (n + 1), ℝ) i).symm _,
  have heπ : e ⁻¹' (Icc 0 (λ _, 2 * π)) = Icc 0 (2 * π) ×ˢ Icc (0 : ℝⁿ) (λ _, 2 * π),
    from ((order_iso.pi_fin_succ_above_iso (λ _, ℝ) i).symm.preimage_Icc _ _).trans
      (Icc_prod_eq _ _),
  rw [torus_integral, ← hem.map_eq, set_integral_map_equiv, heπ, measure.volume_eq_prod,
    set_integral_prod, circle_integral_def_Icc],
  { refine set_integral_congr measurable_set_Icc (λ θ hθ, _),
    simp only [torus_integral, ← integral_smul, deriv_circle_map, i.prod_univ_succ_above _,
      smul_smul, torus_map, circle_map_zero],
    refine set_integral_congr measurable_set_Icc (λ Θ hΘ, _),
    simp only [measurable_equiv.pi_fin_succ_above_equiv_symm_apply, i.insert_nth_apply_same,
      i.insert_nth_apply_succ_above, (∘)],
    congr' 2,
    simp only [funext_iff, i.forall_iff_succ_above, circle_map, fin.insert_nth_apply_same,
      eq_self_iff_true, fin.insert_nth_apply_succ_above, implies_true_iff, and_self] },
  { have := hf.function_integrable,
    rwa [← hem.integrable_on_comp_preimage e.measurable_embedding, heπ] at this }
end

/-- Recurrent formula for `torus_integral`, see also `torus_integral_succ_above`. -/
lemma torus_integral_succ {f : ℂⁿ⁺¹ → E} {c : ℂⁿ⁺¹} {R : ℝⁿ⁺¹} (hf : torus_integrable f c R) :
  ∯ x in T(c, R), f x =
    ∮ x in C(c 0, R 0), ∯ y in T(c ∘ fin.succ, R ∘ fin.succ), f (fin.cons x y) :=
by simpa using torus_integral_succ_above hf 0

/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser
-/
import analysis.normed_space.exponential
import analysis.calculus.fderiv_analytic
import topology.metric_space.cau_seq_filter

/-!
# Calculus results on exponential in a Banach algebra

In this file, we prove basic properties about the derivative of the exponential map `exp 𝕂`
in a Banach algebra `𝔸` over a field `𝕂`. We keep them separate from the main file
`analysis/normed_space/exponential` in order to minimize dependencies.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `has_strict_fderiv_at_exp_zero_of_radius_pos` : `exp 𝕂` has strict Fréchet-derivative
  `1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero
  (see also `has_strict_deriv_at_exp_zero_of_radius_pos` for the case `𝔸 = 𝕂`)
- `has_strict_fderiv_at_exp_of_lt_radius` : if `𝕂` has characteristic zero and `𝔸` is commutative,
  then given a point `x` in the disk of convergence, `exp 𝕂` has strict Fréchet-derivative
  `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at x (see also `has_strict_deriv_at_exp_of_lt_radius` for the case
  `𝔸 = 𝕂`)
- `has_strict_fderiv_at_exp_smul_const_of_mem_ball`: `u ↦ exp 𝕂 (u • x)`, where `x` belongs to a
  ring that may not be commutative, has strict Fréchet-derivative
  `exp 𝕂 (t • x) • (1 : 𝔸 →L[𝕂] 𝔸).smul_right x` at `t` if `t • x` is in the radius of convergence.

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `has_strict_fderiv_at_exp_zero` : `exp 𝕂` has strict Fréchet-derivative `1 : 𝔸 →L[𝕂] 𝔸` at zero
  (see also `has_strict_deriv_at_exp_zero` for the case `𝔸 = 𝕂`)
- `has_strict_fderiv_at_exp` : if `𝔸` is commutative, then given any point `x`, `exp 𝕂` has strict
  Fréchet-derivative `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at x (see also `has_strict_deriv_at_exp` for the
  case `𝔸 = 𝕂`)
- `has_strict_fderiv_at_exp_smul_const`: `u ↦ exp 𝕂 (u • x)`, where `x` belongs to a
  ring that may not be commutative, has strict Fréchet-derivative
  `exp 𝕂 (t • x) • (1 : 𝔸 →L[𝕂] 𝔸).smul_right x` at `t`.

### Compatibilty with `real.exp` and `complex.exp`

- `complex.exp_eq_exp_ℂ` : `complex.exp = exp ℂ ℂ`
- `real.exp_eq_exp_ℝ` : `real.exp = exp ℝ ℝ`

-/

open filter is_R_or_C continuous_multilinear_map normed_field asymptotics
open_locale nat topology big_operators ennreal

section any_field_any_algebra

variables {𝕂 𝔸 : Type*} [nontrivially_normed_field 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸]
  [complete_space 𝔸]

/-- The exponential in a Banach-algebra `𝔸` over a normed field `𝕂` has strict Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero. -/
lemma has_strict_fderiv_at_exp_zero_of_radius_pos (h : 0 < (exp_series 𝕂 𝔸).radius) :
  has_strict_fderiv_at (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
begin
  convert (has_fpower_series_at_exp_zero_of_radius_pos h).has_strict_fderiv_at,
  ext x,
  change x = exp_series 𝕂 𝔸 1 (λ _, x),
  simp [exp_series_apply_eq]
end

/-- The exponential in a Banach-algebra `𝔸` over a normed field `𝕂` has Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero. -/
lemma has_fderiv_at_exp_zero_of_radius_pos (h : 0 < (exp_series 𝕂 𝔸).radius) :
  has_fderiv_at (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
(has_strict_fderiv_at_exp_zero_of_radius_pos h).has_fderiv_at

end any_field_any_algebra

section any_field_comm_algebra

variables {𝕂 𝔸 : Type*} [nontrivially_normed_field 𝕂] [normed_comm_ring 𝔸] [normed_algebra 𝕂 𝔸]
  [complete_space 𝔸]

/-- The exponential map in a commutative Banach-algebra `𝔸` over a normed field `𝕂` of
characteristic zero has Fréchet-derivative `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x` in the
disk of convergence. -/
lemma has_fderiv_at_exp_of_mem_ball [char_zero 𝕂] {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  has_fderiv_at (exp 𝕂) (exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
begin
  have hpos : 0 < (exp_series 𝕂 𝔸).radius := (zero_le _).trans_lt hx,
  rw has_fderiv_at_iff_is_o_nhds_zero,
  suffices : (λ h, exp 𝕂 x * (exp 𝕂 (0 + h) - exp 𝕂 0 - continuous_linear_map.id 𝕂 𝔸 h))
    =ᶠ[𝓝 0] (λ h, exp 𝕂 (x + h) - exp 𝕂 x - exp 𝕂 x • continuous_linear_map.id 𝕂 𝔸 h),
  { refine (is_o.const_mul_left _ _).congr' this (eventually_eq.refl _ _),
    rw ← has_fderiv_at_iff_is_o_nhds_zero,
    exact has_fderiv_at_exp_zero_of_radius_pos hpos },
  have : ∀ᶠ h in 𝓝 (0 : 𝔸), h ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius :=
    emetric.ball_mem_nhds _ hpos,
  filter_upwards [this] with _ hh,
  rw [exp_add_of_mem_ball hx hh, exp_zero, zero_add, continuous_linear_map.id_apply, smul_eq_mul],
  ring
end

/-- The exponential map in a commutative Banach-algebra `𝔸` over a normed field `𝕂` of
characteristic zero has strict Fréchet-derivative `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x` in
the disk of convergence. -/
lemma has_strict_fderiv_at_exp_of_mem_ball [char_zero 𝕂] {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  has_strict_fderiv_at (exp 𝕂) (exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
let ⟨p, hp⟩ := analytic_at_exp_of_mem_ball x hx in
hp.has_fderiv_at.unique (has_fderiv_at_exp_of_mem_ball hx) ▸ hp.has_strict_fderiv_at

end any_field_comm_algebra

section deriv

variables {𝕂 : Type*} [nontrivially_normed_field 𝕂] [complete_space 𝕂]

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has strict derivative
`exp 𝕂 x` at any point `x` in the disk of convergence. -/
lemma has_strict_deriv_at_exp_of_mem_ball [char_zero 𝕂] {x : 𝕂}
  (hx : x ∈ emetric.ball (0 : 𝕂) (exp_series 𝕂 𝕂).radius) :
  has_strict_deriv_at (exp 𝕂) (exp 𝕂 x) x :=
by simpa using (has_strict_fderiv_at_exp_of_mem_ball hx).has_strict_deriv_at

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has derivative
`exp 𝕂 x` at any point `x` in the disk of convergence. -/
lemma has_deriv_at_exp_of_mem_ball [char_zero 𝕂] {x : 𝕂}
  (hx : x ∈ emetric.ball (0 : 𝕂) (exp_series 𝕂 𝕂).radius) :
  has_deriv_at (exp 𝕂) (exp 𝕂 x) x :=
(has_strict_deriv_at_exp_of_mem_ball hx).has_deriv_at

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has strict derivative
`1` at zero, as long as it converges on a neighborhood of zero. -/
lemma has_strict_deriv_at_exp_zero_of_radius_pos (h : 0 < (exp_series 𝕂 𝕂).radius) :
  has_strict_deriv_at (exp 𝕂) (1 : 𝕂) 0 :=
(has_strict_fderiv_at_exp_zero_of_radius_pos h).has_strict_deriv_at

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has derivative
`1` at zero, as long as it converges on a neighborhood of zero. -/
lemma has_deriv_at_exp_zero_of_radius_pos (h : 0 < (exp_series 𝕂 𝕂).radius) :
  has_deriv_at (exp 𝕂) (1 : 𝕂) 0 :=
(has_strict_deriv_at_exp_zero_of_radius_pos h).has_deriv_at

end deriv

section is_R_or_C_any_algebra

variables {𝕂 𝔸 : Type*} [is_R_or_C 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸]
  [complete_space 𝔸]

/-- The exponential in a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has strict Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero. -/
lemma has_strict_fderiv_at_exp_zero :
  has_strict_fderiv_at (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
has_strict_fderiv_at_exp_zero_of_radius_pos (exp_series_radius_pos 𝕂 𝔸)

/-- The exponential in a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero. -/
lemma has_fderiv_at_exp_zero :
  has_fderiv_at (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
has_strict_fderiv_at_exp_zero.has_fderiv_at

end is_R_or_C_any_algebra

section is_R_or_C_comm_algebra

variables {𝕂 𝔸 : Type*} [is_R_or_C 𝕂] [normed_comm_ring 𝔸] [normed_algebra 𝕂 𝔸]
  [complete_space 𝔸]

/-- The exponential map in a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has strict
Fréchet-derivative `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x`. -/
lemma has_strict_fderiv_at_exp {x : 𝔸} :
  has_strict_fderiv_at (exp 𝕂) (exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
has_strict_fderiv_at_exp_of_mem_ball ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/-- The exponential map in a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has
Fréchet-derivative `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x`. -/
lemma has_fderiv_at_exp {x : 𝔸} :
  has_fderiv_at (exp 𝕂) (exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
has_strict_fderiv_at_exp.has_fderiv_at

end is_R_or_C_comm_algebra

section deriv_R_or_C

variables {𝕂 : Type*} [is_R_or_C 𝕂]

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has strict derivative `exp 𝕂 x` at any point
`x`. -/
lemma has_strict_deriv_at_exp {x : 𝕂} : has_strict_deriv_at (exp 𝕂) (exp 𝕂 x) x :=
has_strict_deriv_at_exp_of_mem_ball ((exp_series_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has derivative `exp 𝕂 x` at any point `x`. -/
lemma has_deriv_at_exp {x : 𝕂} : has_deriv_at (exp 𝕂) (exp 𝕂 x) x :=
has_strict_deriv_at_exp.has_deriv_at

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has strict derivative `1` at zero. -/
lemma has_strict_deriv_at_exp_zero : has_strict_deriv_at (exp 𝕂) (1 : 𝕂) 0 :=
has_strict_deriv_at_exp_zero_of_radius_pos (exp_series_radius_pos 𝕂 𝕂)

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has derivative `1` at zero. -/
lemma has_deriv_at_exp_zero :
  has_deriv_at (exp 𝕂) (1 : 𝕂) 0 :=
has_strict_deriv_at_exp_zero.has_deriv_at

end deriv_R_or_C

lemma complex.exp_eq_exp_ℂ : complex.exp = exp ℂ :=
begin
  refine funext (λ x, _),
  rw [complex.exp, exp_eq_tsum_div],
  exact tendsto_nhds_unique x.exp'.tendsto_limit
    (exp_series_div_summable ℝ x).has_sum.tendsto_sum_nat
end

lemma real.exp_eq_exp_ℝ : real.exp = exp ℝ :=
by { ext x, exact_mod_cast congr_fun complex.exp_eq_exp_ℂ x }

/-! ### Derivative of $\exp (ux)$ by $u$

Note that since for `x : 𝔹` we have `normed_ring 𝔹` not `normed_comm_ring 𝔹`, we cannot deduce
these results from `has_fderiv_at_exp_of_mem_ball`.

We could deduce them from the more general non-commutive case,
$$\frac{d}{dt}e^{x(t)} = \int_0^1 e^{sx(t)} \left(\frac{d}{dt}e^{x(t)}\right) e^{(1-s)x(t)} ds$$
but this is harder to prove, and typically is shown by going via these results first.

TODO: prove this result too!
-/

section exp_smul
variables {𝕂 𝔸 𝔹 : Type*}
variables (𝕂)

open_locale topology
open asymptotics filter

section mem_ball
variables [nontrivially_normed_field 𝕂] [char_zero 𝕂]
variables [normed_comm_ring 𝔸] [normed_ring 𝔹]
variables [normed_algebra 𝕂 𝔸] [normed_algebra 𝕂 𝔹] [algebra 𝔸 𝔹] [has_continuous_smul 𝔸 𝔹]
variables [is_scalar_tower 𝕂 𝔸 𝔹]
variables [complete_space 𝔹]

lemma has_fderiv_at_exp_smul_const_of_mem_ball
  (x : 𝔹) (t : 𝔸) (htx : t • x ∈ emetric.ball (0 : 𝔹) (exp_series 𝕂 𝔹).radius) :
  has_fderiv_at (λ u : 𝔸, exp 𝕂 (u • x))
    (exp 𝕂 (t • x) • (1 : 𝔸 →L[𝕂] 𝔸).smul_right x) t :=
begin
  -- TODO: prove this via `has_fderiv_at_exp_of_mem_ball` using the commutative ring
  -- `algebra.elemental_algebra 𝔸 x`. See leanprover-community/mathlib#19062 for discussion.
  have hpos : 0 < (exp_series 𝕂 𝔹).radius := (zero_le _).trans_lt htx,
  rw has_fderiv_at_iff_is_o_nhds_zero,
  suffices :
    (λ h, exp 𝕂 (t • x) * (exp 𝕂 ((0 + h) • x) - exp 𝕂 ((0 : 𝔸) • x)
      - ((1 : 𝔸 →L[𝕂] 𝔸).smul_right x) h))
    =ᶠ[𝓝 0] (λ h, exp 𝕂 ((t + h) • x) - exp 𝕂 (t • x)
      - (exp 𝕂 (t • x) • (1 : 𝔸 →L[𝕂] 𝔸).smul_right x) h),
  { refine (is_o.const_mul_left _ _).congr' this (eventually_eq.refl _ _),
    rw ← @has_fderiv_at_iff_is_o_nhds_zero _ _ _ _ _ _ _ _
      (λ u, exp 𝕂 (u • x)) ((1 : 𝔸 →L[𝕂] 𝔸).smul_right x) 0,
    have : has_fderiv_at (exp 𝕂) (1 : 𝔹 →L[𝕂] 𝔹) ((1 : 𝔸 →L[𝕂] 𝔸).smul_right x 0),
    { rw [continuous_linear_map.smul_right_apply, continuous_linear_map.one_apply, zero_smul],
      exact has_fderiv_at_exp_zero_of_radius_pos hpos },
    exact this.comp 0 ((1 : 𝔸 →L[𝕂] 𝔸).smul_right x).has_fderiv_at },
  have : tendsto (λ h : 𝔸, h • x) (𝓝 0) (𝓝 0),
  { rw ← zero_smul 𝔸 x,
    exact tendsto_id.smul_const x },
  have : ∀ᶠ h in 𝓝 (0 : 𝔸), h • x ∈ emetric.ball (0 : 𝔹) (exp_series 𝕂 𝔹).radius :=
    this.eventually (emetric.ball_mem_nhds _ hpos),
  filter_upwards [this],
  intros h hh,
  have : commute (t • x) (h • x) := ((commute.refl x).smul_left t).smul_right h,
  rw [add_smul t h, exp_add_of_commute_of_mem_ball this htx hh, zero_add, zero_smul, exp_zero,
      continuous_linear_map.smul_right_apply, continuous_linear_map.one_apply,
      continuous_linear_map.smul_apply, continuous_linear_map.smul_right_apply,
      continuous_linear_map.one_apply, smul_eq_mul, mul_sub_left_distrib, mul_sub_left_distrib,
      mul_one],
end

lemma has_fderiv_at_exp_smul_const_of_mem_ball'
  (x : 𝔹) (t : 𝔸) (htx : t • x ∈ emetric.ball (0 : 𝔹) (exp_series 𝕂 𝔹).radius) :
  has_fderiv_at (λ u : 𝔸, exp 𝕂 (u • x))
    (((1 : 𝔸 →L[𝕂] 𝔸).smul_right x).smul_right (exp 𝕂 (t • x))) t :=
begin
  convert has_fderiv_at_exp_smul_const_of_mem_ball 𝕂 _ _ htx using 1,
  ext t',
  show commute (t' • x) (exp 𝕂 (t • x)),
  exact (((commute.refl x).smul_left t').smul_right t).exp_right 𝕂,
end

lemma has_strict_fderiv_at_exp_smul_const_of_mem_ball (t : 𝔸) (x : 𝔹)
  (htx : t • x ∈ emetric.ball (0 : 𝔹) (exp_series 𝕂 𝔹).radius) :
  has_strict_fderiv_at (λ u : 𝔸, exp 𝕂 (u • x))
    (exp 𝕂 (t • x) • (1 : 𝔸 →L[𝕂] 𝔸).smul_right x) t :=
let ⟨p, hp⟩ := analytic_at_exp_of_mem_ball (t • x) htx in
have deriv₁ : has_strict_fderiv_at (λ u : 𝔸, exp 𝕂 (u • x)) _ t,
  from hp.has_strict_fderiv_at.comp t
    ((continuous_linear_map.id 𝕂 𝔸).smul_right x).has_strict_fderiv_at,
have deriv₂ : has_fderiv_at (λ u : 𝔸, exp 𝕂 (u • x)) _ t,
  from has_fderiv_at_exp_smul_const_of_mem_ball 𝕂 x t htx,
(deriv₁.has_fderiv_at.unique deriv₂) ▸ deriv₁

lemma has_strict_fderiv_at_exp_smul_const_of_mem_ball' (t : 𝔸) (x : 𝔹)
  (htx : t • x ∈ emetric.ball (0 : 𝔹) (exp_series 𝕂 𝔹).radius) :
  has_strict_fderiv_at (λ u : 𝔸, exp 𝕂 (u • x))
    (((1 : 𝔸 →L[𝕂] 𝔸).smul_right x).smul_right (exp 𝕂 (t • x))) t :=
let ⟨p, hp⟩ := analytic_at_exp_of_mem_ball (t • x) htx in
begin
  convert has_strict_fderiv_at_exp_smul_const_of_mem_ball 𝕂 _ _ htx using 1,
  ext t',
  show commute (t' • x) (exp 𝕂 (t • x)),
  exact (((commute.refl x).smul_left t').smul_right t).exp_right 𝕂,
end

variables {𝕂}

lemma has_strict_deriv_at_exp_smul_const_of_mem_ball (t : 𝕂) (x : 𝔹)
  (htx : t • x ∈ emetric.ball (0 : 𝔹) (exp_series 𝕂 𝔹).radius) :
  has_strict_deriv_at (λ u : 𝕂, exp 𝕂 (u • x)) (exp 𝕂 (t • x) * x) t :=
by simpa using (has_strict_fderiv_at_exp_smul_const_of_mem_ball 𝕂 t x htx).has_strict_deriv_at


lemma has_strict_deriv_at_exp_smul_const_of_mem_ball' (t : 𝕂) (x : 𝔹)
  (htx : t • x ∈ emetric.ball (0 : 𝔹) (exp_series 𝕂 𝔹).radius) :
  has_strict_deriv_at (λ u : 𝕂, exp 𝕂 (u • x)) (x * exp 𝕂 (t • x)) t :=
by simpa using (has_strict_fderiv_at_exp_smul_const_of_mem_ball' 𝕂 t x htx).has_strict_deriv_at

lemma has_deriv_at_exp_smul_const_of_mem_ball (t : 𝕂) (x : 𝔹)
  (htx : t • x ∈ emetric.ball (0 : 𝔹) (exp_series 𝕂 𝔹).radius) :
  has_deriv_at (λ u : 𝕂, exp 𝕂 (u • x)) (exp 𝕂 (t • x) * x) t :=
(has_strict_deriv_at_exp_smul_const_of_mem_ball t x htx).has_deriv_at

lemma has_deriv_at_exp_smul_const_of_mem_ball' (t : 𝕂) (x : 𝔹)
  (htx : t • x ∈ emetric.ball (0 : 𝔹) (exp_series 𝕂 𝔹).radius) :
  has_deriv_at (λ u : 𝕂, exp 𝕂 (u • x)) (x * exp 𝕂 (t • x)) t :=
(has_strict_deriv_at_exp_smul_const_of_mem_ball' t x htx).has_deriv_at

end mem_ball

section is_R_or_C
variables [is_R_or_C 𝕂]
variables [normed_comm_ring 𝔸] [normed_ring 𝔹]
variables [normed_algebra 𝕂 𝔸] [normed_algebra 𝕂 𝔹] [algebra 𝔸 𝔹] [has_continuous_smul 𝔸 𝔹]
variables [is_scalar_tower 𝕂 𝔸 𝔹]
variables [complete_space 𝔹]

variables (𝕂)

lemma has_fderiv_at_exp_smul_const (x : 𝔹) (t : 𝔸) :
  has_fderiv_at (λ u : 𝔸, exp 𝕂 (u • x))
    (exp 𝕂 (t • x) • (1 : 𝔸 →L[𝕂] 𝔸).smul_right x) t :=
has_fderiv_at_exp_smul_const_of_mem_ball 𝕂 _ _ $
  (exp_series_radius_eq_top 𝕂 𝔹).symm ▸ edist_lt_top _ _

lemma has_fderiv_at_exp_smul_const' (x : 𝔹) (t : 𝔸) :
  has_fderiv_at (λ u : 𝔸, exp 𝕂 (u • x))
    (((1 : 𝔸 →L[𝕂] 𝔸).smul_right x).smul_right (exp 𝕂 (t • x))) t :=
has_fderiv_at_exp_smul_const_of_mem_ball' 𝕂 _ _ $
  (exp_series_radius_eq_top 𝕂 𝔹).symm ▸ edist_lt_top _ _

lemma has_strict_fderiv_at_exp_smul_const (t : 𝔸) (x : 𝔹) :
  has_strict_fderiv_at (λ u : 𝔸, exp 𝕂 (u • x))
    (exp 𝕂 (t • x) • (1 : 𝔸 →L[𝕂] 𝔸).smul_right x) t :=
has_strict_fderiv_at_exp_smul_const_of_mem_ball 𝕂 _ _ $
  (exp_series_radius_eq_top 𝕂 𝔹).symm ▸ edist_lt_top _ _

lemma has_strict_fderiv_at_exp_smul_const' (t : 𝔸) (x : 𝔹) :
  has_strict_fderiv_at (λ u : 𝔸, exp 𝕂 (u • x))
    (((1 : 𝔸 →L[𝕂] 𝔸).smul_right x).smul_right (exp 𝕂 (t • x))) t :=
has_strict_fderiv_at_exp_smul_const_of_mem_ball' 𝕂 _ _ $
  (exp_series_radius_eq_top 𝕂 𝔹).symm ▸ edist_lt_top _ _

variables {𝕂}

lemma has_strict_deriv_at_exp_smul_const (t : 𝕂) (x : 𝔹) :
  has_strict_deriv_at (λ u : 𝕂, exp 𝕂 (u • x)) (exp 𝕂 (t • x) * x) t :=
has_strict_deriv_at_exp_smul_const_of_mem_ball _ _ $
  (exp_series_radius_eq_top 𝕂 𝔹).symm ▸ edist_lt_top _ _

lemma has_strict_deriv_at_exp_smul_const' (t : 𝕂) (x : 𝔹) :
  has_strict_deriv_at (λ u : 𝕂, exp 𝕂 (u • x)) (x * exp 𝕂 (t • x)) t :=
has_strict_deriv_at_exp_smul_const_of_mem_ball' _ _ $
  (exp_series_radius_eq_top 𝕂 𝔹).symm ▸ edist_lt_top _ _

lemma has_deriv_at_exp_smul_const (t : 𝕂) (x : 𝔹) :
  has_deriv_at (λ u : 𝕂, exp 𝕂 (u • x)) (exp 𝕂 (t • x) * x) t :=
has_deriv_at_exp_smul_const_of_mem_ball _ _ $
  (exp_series_radius_eq_top 𝕂 𝔹).symm ▸ edist_lt_top _ _

lemma has_deriv_at_exp_smul_const' (t : 𝕂) (x : 𝔹) :
  has_deriv_at (λ u : 𝕂, exp 𝕂 (u • x)) (x * exp 𝕂 (t • x)) t :=
has_deriv_at_exp_smul_const_of_mem_ball' _ _ $
  (exp_series_radius_eq_top 𝕂 𝔹).symm ▸ edist_lt_top _ _

end is_R_or_C

end exp_smul

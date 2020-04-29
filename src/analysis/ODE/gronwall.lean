/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.calculus.mean_value
import analysis.special_functions.exp_log

/-!
# Grönwall's inequality

The main technical result of this file is the Grönwall-like inequality
`norm_le_gronwall_bound_of_norm_deriv_right_le`. It states that if `f : ℝ → E` satisfies `∥f a∥ ≤ δ`
and `∀ x ∈ [a, b), ∥f' x∥ ≤ K * ∥f x∥ + ε`, then for all `x ∈ [a, b]` we have `∥f x∥ ≤ δ * exp (K *
x) + (ε / K) * (exp (K * x) - 1)`.

Then we use this inequality to prove some estimates on the possible rate of growth of the distance
between two approximate or exact solutions of an ordinary differential equation.

The proofs are based on [Hubbard and West, *Differential Equations: A Dynamical Systems Approach*,
Sec. 4.5][HubbardWest-ode], where `norm_le_gronwall_bound_of_norm_deriv_right_le` is called
“Fundamental Inequality”.

## TODO

- Once we have FTC, prove an inequality for a function satisfying `∥f' x∥ ≤ K x * ∥f x∥ + ε`,
  or more generally `liminf_{y→x+0} (f y - f x)/(y - x) ≤ K x * f x + ε` with any sign
  of `K x` and `f x`.
-/

variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F]

open metric set asymptotics filter real
open_locale classical

/-! ### Technical lemmas about `gronwall_bound` -/

/-- Upper bound used in several Grönwall-like inequalities. -/
noncomputable def gronwall_bound (δ K ε x : ℝ) : ℝ :=
if K = 0 then δ + ε * x else δ * exp (K * x) + (ε / K) * (exp (K * x) - 1)

lemma gronwall_bound_K0 (δ ε : ℝ) : gronwall_bound δ 0 ε = λ x, δ + ε * x :=
funext $ λ x, if_pos rfl

lemma gronwall_bound_of_K_ne_0 {δ K ε : ℝ} (hK : K ≠ 0) :
  gronwall_bound δ K ε = λ x, δ * exp (K * x) + (ε / K) * (exp (K * x) - 1) :=
funext $ λ x, if_neg hK

lemma has_deriv_at_gronwall_bound (δ K ε x : ℝ) :
  has_deriv_at (gronwall_bound δ K ε) (K * (gronwall_bound δ K ε x) + ε) x :=
begin
  by_cases hK : K = 0,
  { subst K,
    simp only [gronwall_bound_K0, zero_mul, zero_add],
    convert ((has_deriv_at_id x).const_mul ε).const_add δ,
    rw [mul_one] },
  { simp only [gronwall_bound_of_K_ne_0 hK],
    convert (((has_deriv_at_id x).const_mul K).exp.const_mul δ).add
      ((((has_deriv_at_id x).const_mul K).exp.sub_const 1).const_mul (ε / K)) using 1,
    simp only [id, mul_add, (mul_assoc _ _ _).symm, mul_comm _ K, mul_div_cancel' _ hK],
    ring }
end

lemma has_deriv_at_gronwall_bound_shift (δ K ε x a : ℝ) :
  has_deriv_at (λ y, gronwall_bound δ K ε (y - a)) (K * (gronwall_bound δ K ε (x - a)) + ε) x :=
begin
  convert (has_deriv_at_gronwall_bound δ K ε _).comp x ((has_deriv_at_id x).sub_const a),
  rw [id, mul_one]
end

lemma gronwall_bound_x0 (δ K ε : ℝ) : gronwall_bound δ K ε 0 = δ :=
begin
  by_cases hK : K = 0,
  { simp only [gronwall_bound, if_pos hK, mul_zero, add_zero] },
  { simp only [gronwall_bound, if_neg hK, mul_zero, exp_zero, sub_self, mul_one, add_zero] }
end

lemma gronwall_bound_ε0 (δ K x : ℝ) : gronwall_bound δ K 0 x = δ * exp (K * x) :=
begin
  by_cases hK : K = 0,
  { simp only [gronwall_bound_K0, hK, zero_mul, exp_zero, add_zero, mul_one] },
  { simp only [gronwall_bound_of_K_ne_0 hK, zero_div, zero_mul, add_zero] }
end

lemma gronwall_bound_ε0_δ0 (K x : ℝ) : gronwall_bound 0 K 0 x = 0 :=
by simp only [gronwall_bound_ε0, zero_mul]

lemma gronwall_bound_continuous_ε (δ K x : ℝ) : continuous (λ ε, gronwall_bound δ K ε x) :=
begin
  by_cases hK : K = 0,
  { simp only [gronwall_bound_K0, hK],
    exact continuous_const.add (continuous_id.mul continuous_const) },
  { simp only [gronwall_bound_of_K_ne_0 hK],
    exact continuous_const.add ((continuous_id.mul continuous_const).mul continuous_const) }
end

/-! ### Inequality and corollaries -/

/-- A Grönwall-like inequality: if `f : ℝ → ℝ` is continuous on `[a, b]` and satisfies
the inequalities `f a ≤ δ` and
`∀ x ∈ [a, b), liminf_{z→x+0} (f z - f x)/(z - x) ≤ K * (f x) + ε`, then `f x`
is bounded by `gronwall_bound δ K ε (x - a)` on `[a, b]`.

See also `norm_le_gronwall_bound_of_norm_deriv_right_le` for a version bounding `∥f x∥`,
`f : ℝ → E`. -/
theorem le_gronwall_bound_of_liminf_deriv_right_le {f f' : ℝ → ℝ} {δ K ε : ℝ} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r →
    ∃ᶠ z in nhds_within x (Ioi x), (z - x)⁻¹ * (f z - f x) < r)
  (ha : f a ≤ δ) (bound : ∀ x ∈ Ico a b, f' x ≤ K * f x + ε) :
  ∀ x ∈ Icc a b, f x ≤ gronwall_bound δ K ε (x - a) :=
begin
  have H : ∀ x ∈ Icc a b, ∀ ε' ∈ Ioi ε, f x ≤ gronwall_bound δ K ε' (x - a),
  { assume x hx ε' hε',
    apply image_le_of_liminf_slope_right_lt_deriv_boundary hf hf',
    { rwa [sub_self, gronwall_bound_x0] },
    { exact λ x, has_deriv_at_gronwall_bound_shift δ K ε' x a },
    { assume x hx hfB,
      rw [← hfB],
      apply lt_of_le_of_lt (bound x hx),
      exact add_lt_add_left hε' _ },
    { exact hx } },
  assume x hx,
  change f x ≤ (λ ε', gronwall_bound δ K ε' (x - a)) ε,
  convert continuous_within_at_const.closure_le _ _ (H x hx),
  { simp only [closure_Ioi, left_mem_Ici] },
  exact (gronwall_bound_continuous_ε δ K (x - a)).continuous_within_at
end

/-- A Grönwall-like inequality: if `f : ℝ → E` is continuous on `[a, b]`, has right derivative
`f' x` at every point `x ∈ [a, b)`, and satisfies the inequalities `∥f a∥ ≤ δ`,
`∀ x ∈ [a, b), ∥f' x∥ ≤ K * ∥f x∥ + ε`, then `∥f x∥` is bounded by `gronwall_bound δ K ε (x - a)`
on `[a, b]`. -/
theorem norm_le_gronwall_bound_of_norm_deriv_right_le {f f' : ℝ → E} {δ K ε : ℝ} {a b : ℝ}
  (hf : continuous_on f (Icc a b)) (hf' : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ioi x) x)
  (ha : ∥f a∥ ≤ δ) (bound : ∀ x ∈ Ico a b, ∥f' x∥ ≤ K * ∥f x∥ + ε) :
  ∀ x ∈ Icc a b, ∥f x∥ ≤ gronwall_bound δ K ε (x - a) :=
le_gronwall_bound_of_liminf_deriv_right_le (continuous_norm.comp_continuous_on hf)
  (λ x hx r hr, (hf' x hx).liminf_right_slope_norm_le hr) ha bound

/-- If `f` and `g` are two approximate solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t`,
and assumes that the solutions never leave this set. -/
theorem dist_le_of_approx_trajectories_ODE_of_mem_set {v : ℝ → E → E} {s : ℝ → set E}
  {K : ℝ} (hv : ∀ t, ∀ x y ∈ s t, dist (v t x) (v t y) ≤ K * dist x y)
  {f g f' g' : ℝ → E} {a b : ℝ} {εf εg δ : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ t ∈ Ico a b, has_deriv_within_at f (f' t) (Ioi t) t)
  (f_bound : ∀ t ∈ Ico a b, dist (f' t) (v t (f t)) ≤ εf)
  (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
  (hg : continuous_on g (Icc a b))
  (hg' : ∀ t ∈ Ico a b, has_deriv_within_at g (g' t) (Ioi t) t)
  (g_bound : ∀ t ∈ Ico a b, dist (g' t) (v t (g t)) ≤ εg)
  (hgs : ∀ t ∈ Ico a b, g t ∈ s t)
  (ha : dist (f a) (g a) ≤ δ) :
  ∀ t ∈ Icc a b, dist (f t) (g t) ≤ gronwall_bound δ K (εf + εg) (t - a) :=
begin
  simp only [dist_eq_norm] at ha ⊢,
  have h_deriv : ∀ t ∈ Ico a b, has_deriv_within_at (λ t, f t - g t) (f' t - g' t) (Ioi t) t,
    from λ t ht, (hf' t ht).sub (hg' t ht),
  apply norm_le_gronwall_bound_of_norm_deriv_right_le (hf.sub hg) h_deriv ha,
  assume t ht,
  have := dist_triangle4_right (f' t) (g' t) (v t (f t)) (v t (g t)),
  rw [dist_eq_norm] at this,
  apply le_trans this,
  apply le_trans (add_le_add (add_le_add (f_bound t ht) (g_bound t ht))
    (hv t (f t) (g t) (hfs t ht) (hgs t ht))),
  rw [dist_eq_norm, add_comm]
end

/-- If `f` and `g` are two approximate solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in the whole space. -/
theorem dist_le_of_approx_trajectories_ODE {v : ℝ → E → E}
  {K : nnreal} (hv : ∀ t, lipschitz_with K (v t))
  {f g f' g' : ℝ → E} {a b : ℝ} {εf εg δ : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ t ∈ Ico a b, has_deriv_within_at f (f' t) (Ioi t) t)
  (f_bound : ∀ t ∈ Ico a b, dist (f' t) (v t (f t)) ≤ εf)
  (hg : continuous_on g (Icc a b))
  (hg' : ∀ t ∈ Ico a b, has_deriv_within_at g (g' t) (Ioi t) t)
  (g_bound : ∀ t ∈ Ico a b, dist (g' t) (v t (g t)) ≤ εg)
  (ha : dist (f a) (g a) ≤ δ) :
  ∀ t ∈ Icc a b, dist (f t) (g t) ≤ gronwall_bound δ K (εf + εg) (t - a) :=
have hfs : ∀ t ∈ Ico a b, f t ∈ (@univ E), from λ t ht, trivial,
dist_le_of_approx_trajectories_ODE_of_mem_set (λ t x y hx hy, (hv t).dist_le_mul x y)
  hf hf' f_bound hfs hg hg' g_bound (λ t ht, trivial) ha

/-- If `f` and `g` are two exact solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t`,
and assumes that the solutions never leave this set. -/
theorem dist_le_of_trajectories_ODE_of_mem_set {v : ℝ → E → E} {s : ℝ → set E}
  {K : ℝ} (hv : ∀ t, ∀ x y ∈ s t, dist (v t x) (v t y) ≤ K * dist x y)
  {f g : ℝ → E} {a b : ℝ} {δ : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ t ∈ Ico a b, has_deriv_within_at f (v t (f t)) (Ioi t) t)
  (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
  (hg : continuous_on g (Icc a b))
  (hg' : ∀ t ∈ Ico a b, has_deriv_within_at g (v t (g t)) (Ioi t) t)
  (hgs : ∀ t ∈ Ico a b, g t ∈ s t)
  (ha : dist (f a) (g a) ≤ δ) :
  ∀ t ∈ Icc a b, dist (f t) (g t) ≤ δ * exp (K * (t - a)) :=
begin
  have f_bound : ∀ t ∈ Ico a b, dist (v t (f t)) (v t (f t)) ≤ 0,
    by { intros, rw [dist_self] },
  have g_bound : ∀ t ∈ Ico a b, dist (v t (g t)) (v t (g t)) ≤ 0,
    by { intros, rw [dist_self] },
  assume t ht,
  have := dist_le_of_approx_trajectories_ODE_of_mem_set hv hf hf' f_bound hfs hg hg' g_bound
    hgs ha t ht,
  rwa [zero_add, gronwall_bound_ε0] at this,
end

/-- If `f` and `g` are two exact solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in the whole space. -/
theorem dist_le_of_trajectories_ODE {v : ℝ → E → E}
  {K : nnreal} (hv : ∀ t, lipschitz_with K (v t))
  {f g : ℝ → E} {a b : ℝ} {δ : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ t ∈ Ico a b, has_deriv_within_at f (v t (f t)) (Ioi t) t)
  (hg : continuous_on g (Icc a b))
  (hg' : ∀ t ∈ Ico a b, has_deriv_within_at g (v t (g t)) (Ioi t) t)
  (ha : dist (f a) (g a) ≤ δ) :
  ∀ t ∈ Icc a b, dist (f t) (g t) ≤ δ * exp (K * (t - a)) :=
have hfs : ∀ t ∈ Ico a b, f t ∈ (@univ E), from λ t ht, trivial,
dist_le_of_trajectories_ODE_of_mem_set (λ t x y hx hy, (hv t).dist_le_mul x y)
  hf hf' hfs hg hg' (λ t ht, trivial) ha

/-- There exists only one solution of an ODE \(\dot x=v(t, x)\) in a set `s ⊆ ℝ × E` with
a given initial value provided that RHS is Lipschitz continuous in `x` within `s`,
and we consider only solutions included in `s`. -/
theorem ODE_solution_unique_of_mem_set {v : ℝ → E → E} {s : ℝ → set E}
  {K : ℝ} (hv : ∀ t, ∀ x y ∈ s t, dist (v t x) (v t y) ≤ K * dist x y)
  {f g : ℝ → E} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ t ∈ Ico a b, has_deriv_within_at f (v t (f t)) (Ioi t) t)
  (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
  (hg : continuous_on g (Icc a b))
  (hg' : ∀ t ∈ Ico a b, has_deriv_within_at g (v t (g t)) (Ioi t) t)
  (hgs : ∀ t ∈ Ico a b, g t ∈ s t)
  (ha : f a = g a) :
  ∀ t ∈ Icc a b, f t = g t :=
begin
  assume t ht,
  have := dist_le_of_trajectories_ODE_of_mem_set hv hf hf' hfs hg hg' hgs
    (dist_le_zero.2 ha) t ht,
  rwa [zero_mul, dist_le_zero] at this
end

/-- There exists only one solution of an ODE \(\dot x=v(t, x)\) with
a given initial value provided that RHS is Lipschitz continuous in `x`. -/
theorem ODE_solution_unique {v : ℝ → E → E}
  {K : nnreal} (hv : ∀ t, lipschitz_with K (v t))
  {f g : ℝ → E} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ t ∈ Ico a b, has_deriv_within_at f (v t (f t)) (Ioi t) t)
  (hg : continuous_on g (Icc a b))
  (hg' : ∀ t ∈ Ico a b, has_deriv_within_at g (v t (g t)) (Ioi t) t)
  (ha : f a = g a) :
  ∀ t ∈ Icc a b, f t = g t :=
have hfs : ∀ t ∈ Ico a b, f t ∈ (@univ E), from λ t ht, trivial,
ODE_solution_unique_of_mem_set (λ t x y hx hy, (hv t).dist_le_mul x y)
  hf hf' hfs hg hg' (λ t ht, trivial) ha

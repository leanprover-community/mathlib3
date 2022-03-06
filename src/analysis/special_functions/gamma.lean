import analysis.special_functions.exponential
import measure_theory.integral.integral_eq_improper
import measure_theory.integral.limit_comparison
import analysis.special_functions.integrals


noncomputable theory
open finset filter metric interval_integral set function
open_locale classical topological_space ennreal filter

namespace real


/- The integrand in the integration-by-parts argument -/

def F (s x : ℝ) : ℝ := exp(-x) * x^s

lemma cont_F (s : ℝ) (h1: 0 ≤ s) :
  continuous_on s.F (Ici 0) :=
begin
  apply continuous_on.mul,
  { apply continuous_on.exp,
    apply continuous_on.neg,
    apply continuous_on_id },
  { apply continuous_on.rpow_const,
    apply continuous_on_id,
    tauto }
end

lemma deriv_F (s x: ℝ) (h1: 1 ≤ s) (h2: 0 ≤ x) : has_deriv_at s.F
(- (exp (-x) * x ^ s) + exp (-x) * (s * x ^ (s - 1))) x :=
begin
  have d1 : has_deriv_at (λ (y: ℝ), exp(-y)) (-exp(-x)) x,
  { simpa using has_deriv_at.exp (has_deriv_at_neg x) },
  have d2 : has_deriv_at (λ (y: ℝ), y^s) (s*x^(s-1)) x,
  { apply has_deriv_at_rpow_const,
    right,
    exact h1 },
  simpa using has_deriv_at.mul d1 d2
end


/- A long and fiddly argument to show that F decays exponentially at +∞ -/

/- This lemma should really go in specific_limits.lean or something -/
lemma tendsto_exp_div_rpow_at_top (s : ℝ) : tendsto (λ x : ℝ, exp x / x ^ s ) at_top at_top :=
begin
  have := archimedean_iff_nat_lt.1 (real.archimedean) s,
  cases this with n hn,
  have t := tendsto_exp_div_pow_at_top n,
  have : 0 < (n:ℝ) - s := by linarith,
  replace t := tendsto.at_top_mul_at_top t (tendsto_rpow_at_top this),

  let f1 := (λ x:ℝ, (exp x / x ^ n) * (x ^ (↑n - s))),
  let f2 := (λ x:ℝ, exp x / x ^ s),
  have ff1: f1 = (λ x:ℝ, (exp x / x ^ n) * (x ^ (↑n - s))) := by refl,
  have ff2: f2 = (λ x:ℝ, exp x / x ^ s) := by refl,

  have : ∀ x : ℝ, (0 < x) → f1 x = f2 x,
  --have : ∀ x : ℝ, (0 < x) → ( (exp x / x ^ n) * (x ^ (↑n - s)) = exp x / x ^ s),
  --have : ∀ x : ℝ, (0 < x) → (λ x:ℝ, (exp x / x ^ n) * (x ^ (↑n - s))) x = (λ x:ℝ, exp x / x ^ s) x,
  {
    intros x h,
    rw [ff1,ff2],
    ring_nf,
    --rw div_eq_mul_inv (exp x) (x^n),
    rw mul_eq_mul_right_iff,
    left,
    rw [sub_eq_neg_add,rpow_add_nat, mul_assoc],
    have : x^n * (x^n)⁻¹ = 1,
    apply mul_inv_cancel,
    apply pow_ne_zero,
    exact h.ne',
    rw [this, mul_one],
    apply rpow_neg,
    exact le_of_lt(h),
    exact h.ne',
  },

  have Icieq: eq_on f1 f2 (Ici 1),
  {
    intros x hx,
    rw [set.Ici, mem_set_of_eq] at hx,
    have b: 0 < x := by linarith,
    exact (this x b),
  },

  have eveq : eventually_eq at_top f1 f2,
  {
    rw eventually_eq_iff_exists_mem,
    use (Ici 1),
    split,
    apply mem_at_top,
    exact Icieq,
  },
  apply tendsto.congr' eveq,
  exact t,
end

/- More general version allowing exp(-bx) for any b > 0 -/
lemma tendsto_exp_mul_div_rpow_at_top (s : ℝ) (b : ℝ) (hb : 0 < b):
  tendsto (λ x : ℝ, exp (b * x) / x ^ s ) at_top at_top :=
begin
  have t1 := tendsto_exp_div_rpow_at_top (s/b),
  have t2 := tendsto_rpow_at_top hb,
  have t := tendsto.comp t2 t1,

  let f1 := (λ (x : ℝ), (exp x / x ^ (s / b)) ^ b),
  let f2 := (λ x : ℝ, exp (b * x) / x ^ s ),
  have ff1 : ∀ x:ℝ, f1 x = (exp x / x ^ (s / b)) ^ b,
  {
    by simp only [eq_self_iff_true, forall_const],
  },
  have ff2 : ∀ x:ℝ, f2 x = exp (b * x) / x ^ s,
  {
    by simp only [eq_self_iff_true, forall_const],
  },

  have Ioieq: eq_on f1 f2 (Ioi 0),
  {
    intros x hx,
    rw [set.Ioi, mem_set_of_eq] at hx,
    rw [ff1, ff2],
    rw div_rpow,
    -- clean up the subgoals introduced by div_rpow
    show 0 ≤ exp x,
    { apply le_of_lt(exp_pos x) },
    show 0 ≤ x ^ (s / b),
    { apply le_of_lt,
      apply rpow_pos_of_pos hx },

    have : exp x ^ b = exp (b * x),
    { calc exp x ^ b = exp(log (exp x ^ b ) ) : by { rw exp_log, apply rpow_pos_of_pos (exp_pos x) }
      ...            = exp( b * log (exp x) ) : by rw log_rpow (exp_pos x)
      ...            = exp( b * x )           : by rw log_exp },
    rw this,
    rw div_eq_div_iff,
    show x^s ≠ 0,
    { symmetry, apply ne_of_lt,
      apply rpow_pos_of_pos,
      linarith },
    show (x ^ (s / b)) ^ b ≠ 0,
    { symmetry, apply ne_of_lt,
      apply rpow_pos_of_pos,
      apply rpow_pos_of_pos,
      linarith },
    rw mul_eq_mul_left_iff,
    left,
    rw ←rpow_mul,
    show 0 ≤ x, linarith,
    rw div_mul_cancel, exact hb.ne'
  },
  have : Ici (1:ℝ) ⊆ Ioi (0:ℝ),
  {
    rw [set.Ioi, set.Ici],
    intro x,
    rw mem_set_of_eq,rw mem_set_of_eq,
    intro hx,linarith,
  },
  have Ioi_at_top: Ioi (0:ℝ) ∈ at_top := Ioi_mem_at_top (0:ℝ),
  have ev_eq: eventually_eq at_top f1 f2 := eventually_eq_of_mem Ioi_at_top Ioieq,

  exact tendsto.congr' ev_eq t
end

lemma tendsto_exp_mul_div_rpow_at_top' (s : ℝ) (b : ℝ) (hb : 0 < b):
  tendsto (λ x : ℝ, x^s * exp (-b * x)) at_top (𝓝 $ (0:ℝ)) :=
begin
  have l := tendsto_exp_mul_div_rpow_at_top s b hb,
  have:  (λ x : ℝ, x^s * exp (-b * x)) =  (λ x : ℝ, exp (b * x) / x^s)⁻¹,
  {
    ext,
    simp only [neg_mul, pi.inv_apply],
    rw [inv_div,div_eq_mul_inv],
    rw mul_eq_mul_left_iff,
    left,
    apply exp_neg,
  },
  rw this,
  exact tendsto.inv_tendsto_at_top l
end

/- Now we have the bits we need -/
lemma asymp_F (s : ℝ) :
  asymptotics.is_O s.F (λ x : ℝ, exp(-(1/2) * x)) filter.at_top :=
begin
  apply asymptotics.is_o.is_O,
  apply asymptotics.is_o_of_tendsto,
  { intros x hx,
    exfalso,
    apply ( exp_pos(-(1/2) * x)).ne',
    exact hx },

  simp only [F],

  have : ∀ (x: ℝ), (x > 0) → (exp (-x) * x ^ s / exp (-(1 / 2) * x) = exp (-(1/2) * x) * x ^ s),
  {
    intros x h,
    rw mul_comm,
    rw mul_comm (exp (-(1/2) * x)) (x ^ s),
    rw div_eq_of_eq_mul,
    exact (exp_pos (-(1/2) * x)).ne',
    have: exp(-x) = exp(-(1/2)*x) * exp (-(1 / 2) * x),
    {
      rw ←real.exp_add,
      simp only [exp_eq_exp],
      ring,
    },
    rw this,
    ring
  },
  replace : eventually_eq at_top
    (λ x:ℝ,(exp (-x) * x ^ s / exp (-(1 / 2) * x))) (λ x:ℝ,  exp (-(1/2) * x) * x ^ s),
  {
    apply eventually_eq_of_mem (Ioi_mem_at_top(0:ℝ)),
    intros x hx,
    rw [set.Ioi, mem_set_of_eq] at hx,
    exact (this x hx)
  },
  rw (tendsto_congr' this),
  have : (λ (x : ℝ), exp (-(1 / 2) * x) * x ^ s) = (λ (x : ℝ), exp ((1 / 2) * x) / x ^ s)⁻¹,
  {
    ext1,
    simp only [neg_mul, pi.inv_apply],
    rw inv_div,
    rw exp_neg,
    ring,
  },
  rw this,
  apply tendsto.inv_tendsto_at_top,
  exact (tendsto_exp_mul_div_rpow_at_top s (1/2))(one_half_pos) -- hooray!
end





def real_incomplete_gamma (s X : ℝ) : ℝ := ∫ x in 0..X, exp(-x) * x^(s-1)

lemma gamma_FE_incomp (s X : ℝ) (h: 1 ≤ s) (h2: 0 ≤ X):
  real_incomplete_gamma (s+1) X = s * real_incomplete_gamma s X - X^s * exp(-X) :=
begin
  rw real_incomplete_gamma,
  rw real_incomplete_gamma,

  have F_der_I: (∀ (x:ℝ), (x ∈ interval 0 X) →
    has_deriv_at s.F (- (exp (-x) * x ^ s) + exp (-x) * (s * x ^ (s - 1))) x),
  {
    intros x hx,
    cases hx,
    rw min_def at hx_left,
    split_ifs at hx_left,
    exact deriv_F s x h hx_left,
    tauto,
  },

  have c : continuous_on (λ (x : ℝ), exp (-x)) (interval 0 X),
  { apply continuous_on.exp,
    apply continuous_on.neg,
    apply continuous_on_id },

  have dF_int_I: interval_integrable (λ (x : ℝ),
    -(exp (-x) * x ^ s) + exp (-x) * (s * x ^ (s - 1)))
    measure_theory.measure_space.volume 0 X,
  {
    -- This is an awful mess,
    -- proving continuity of a function
    -- built up as a sum of many terms.
    apply continuous_on.interval_integrable,
    apply continuous_on.add,
    apply continuous_on.neg,
    apply continuous_on.mul,
    exact c,
    apply continuous_on.rpow_const,
    apply continuous_at.continuous_on,
    intros x hxX,
    apply continuous_at_id,
    intros x hxX,
    right,
    exact le_trans(zero_le_one)(h),

    -- halfway...
    apply continuous_on.mul,
    exact c,
    apply continuous_on.mul,
    apply continuous.continuous_on,
    apply continuous_const,
    apply continuous_on.rpow_const,
    apply continuous_at.continuous_on,
    intros x hxX,
    apply continuous_at_id,
    intros x hxX,
    right,
    rw le_sub,
    simp,exact h
  },
  have int_eval := integral_eq_sub_of_has_deriv_at F_der_I dF_int_I,
  clear F_der_I dF_int_I c,
  have : (F s 0) = 0,
  { rw F, rw zero_rpow, ring, apply ne_of_gt,
    apply lt_of_lt_of_le zero_lt_one h },
  rw [this, F] at int_eval,
  simp only [sub_zero] at int_eval,
  rw integral_add at int_eval,
  simp only [add_tsub_cancel_right],
  have : (∫ (x : ℝ) in 0..X, exp (-x) * x ^ s)
   = (∫ (x : ℝ) in 0..X, exp (-x) * (s * x ^ (s - 1))) - exp (-X) * X ^ s,
  rw sub_eq_neg_add,
  apply eq_add_of_add_neg_eq,
  rw ← int_eval, simp,ring,
  rw this,
  have : (exp (-X) * X ^ s) = (X^s * exp(-X)) := by ring,
  rw this, simp,
  clear this, clear this,clear this,clear int_eval,
  have : (λ (x : ℝ), exp (-x) * (s * x ^ (s - 1)))
    = (λ (x : ℝ), s * (exp (-x) * x ^ (s - 1))),
  ext1, ring,
  rw this,
  apply integral_const_mul,
  clear this, clear int_eval,

  -- now two more integrability statements, yawn
  apply continuous_on.interval_integrable,
  apply continuous_on.neg,
  apply continuous_on.mul,
  apply continuous_on.exp,
  apply continuous_on.neg,
  apply continuous_on_id,
  apply continuous_on.rpow_const,
  apply continuous_on_id,
  intros x hx,
  right,
  exact le_trans(zero_le_one)(h),

  -- and the last one
  apply continuous_on.interval_integrable,
  apply continuous_on.mul,
  apply continuous_on.exp,
  apply continuous_on.neg,
  apply continuous_on_id,
  apply continuous_on.mul,
  apply continuous_on_const,
  apply continuous_on.rpow_const,
  apply continuous_on_id,
  intros x hx,
  right,
  rw le_sub,
  simp only [sub_zero],
  exact h
end


lemma integrable_F (s: ℝ) (h: 1 ≤ s): measure_theory.integrable_on
  (λ (x:ℝ), exp(-x) * x^(s-1)) (Ioi 0) :=
begin
  apply limit_comparison.integrable_bigoh_exp (s-1).F 0 (1/2) one_half_pos,
  apply cont_F,
  { linarith },
  exact asymp_F (s-1)
end

def real_gamma (s: ℝ) : ℝ :=  ∫ x in (Ioi 0), exp(-x) * x^(s-1)

lemma tendsto_incomplete_gamma (s : ℝ) (h: 1 ≤ s):
  tendsto (s.real_incomplete_gamma) (filter.at_top)  (𝓝 $ real_gamma s) :=
begin
  apply measure_theory.interval_integral_tendsto_integral_Ioi,
  swap, apply tendsto_id,
  exact integrable_F s h
end

lemma FE_gamma (s : ℝ) (h: 1 ≤ s) :
  real_gamma (s+1) = s * real_gamma s :=
begin
  have t1: tendsto (s+1).real_incomplete_gamma at_top (𝓝 (s+1).real_gamma),
  { apply tendsto_incomplete_gamma, linarith },
  suffices t2: tendsto (s+1).real_incomplete_gamma at_top (𝓝 $ s * real_gamma s),
  { apply tendsto_nhds_unique t1 t2 },

  have a: eventually_eq at_top ((s+1).real_incomplete_gamma)
    (λ X:ℝ, s * real_incomplete_gamma s X - X^s * exp(-X)),
  {
    apply eventually_eq_of_mem (Ici_mem_at_top (0:ℝ)),
    intros X hX,
    rw [set.Ici, mem_set_of_eq] at hX,
    exact gamma_FE_incomp s X h hX
  },
  replace a := eventually_eq.symm a,

  suffices b: tendsto (λ X:ℝ, s * real_incomplete_gamma s X - X^s * exp(-X)) at_top
    (𝓝 $ s * real_gamma s),
  { exact tendsto.congr' a b, },

  have l1: tendsto (λ X:ℝ, s * real_incomplete_gamma s X) at_top (𝓝 $ s * real_gamma s),
  {
    apply tendsto.const_mul,
    exact tendsto_incomplete_gamma s h
  },
  suffices l2: tendsto (λ X:ℝ, -X^s * exp(-X)) at_top (𝓝 $ (0:ℝ)),
  {
    have := tendsto.add l1 l2,
    simpa using this
  },
  have l3: tendsto (λ X:ℝ, X^s * exp(-X)) at_top (𝓝 $ (0:ℝ)),
  {
    have := tendsto_exp_mul_div_rpow_at_top' s (1:ℝ) zero_lt_one,
    simpa using this
  },
  have: (λ X:ℝ, -X^s * exp(-X)) = (λ X:ℝ, (-1) * (X^s * exp(-X))) := by { simp only [neg_mul, one_mul], },
  rw this,
  have : (0:ℝ) = (-1) * (0:ℝ) := by {ring, },
  rw this,
  apply tendsto.const_mul,
  exact l3
end

lemma incomp_gamma_at_one (X : ℝ) (hX: 0 < X): real_incomplete_gamma 1 X = 1-exp(-X) :=
begin
  rw real_incomplete_gamma,
  simp
end

lemma gamma_at_one: real_gamma 1 = 1 :=
begin
  have t1: tendsto (1:ℝ).real_incomplete_gamma at_top (𝓝 (1:ℝ).real_gamma),
  {
    apply tendsto_incomplete_gamma,
    refl
  },
  have t2: tendsto (1:ℝ).real_incomplete_gamma at_top (𝓝 (1:ℝ)),
  {
    have t2a: eventually_eq at_top (λ X:ℝ, 1-exp(-X)) (1:ℝ).real_incomplete_gamma,
    {
      apply eventually_eq_of_mem (Ioi_mem_at_top (0:ℝ)),
      intros X hX,
      symmetry,
      apply incomp_gamma_at_one,
      rw [←Ioi_def, mem_set_of_eq] at hX, exact hX
    },
    apply tendsto.congr' t2a,

    have t2b: tendsto (λ X, exp(-X)) at_top (𝓝 (0:ℝ)),
    {
      have := tendsto_exp_mul_div_rpow_at_top' 0 1,
      simpa using this
    },
    have := tendsto.const_sub (1:ℝ) t2b,
    simpa using this
  },
  apply tendsto_nhds_unique t1 t2
end

lemma gamma_integer: ∀ n:ℕ, real_gamma (n+1) = nat.factorial n :=
begin
  intro n,
  induction n with n hn,

  simp only [nat.cast_zero, zero_add, nat.factorial_zero, nat.cast_one],
  exact gamma_at_one,

  rw FE_gamma,
  simp only [nat.cast_succ, nat.factorial_succ, nat.cast_mul, mul_eq_mul_left_iff],
  left, exact hn,

  simp only [nat.cast_succ, le_add_iff_nonneg_left, nat.cast_nonneg]
end

end real

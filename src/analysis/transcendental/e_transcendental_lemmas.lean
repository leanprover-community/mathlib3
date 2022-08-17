import measure_theory.integral.interval_integral
import measure_theory.measure.haar_lebesgue
import analysis.special_functions.exp
import analysis.transcendental.small_lemmas
import data.polynomial.derivative

noncomputable theory
open_locale big_operators
open_locale classical
open_locale polynomial
open small_lemmas

/-Definition
For any integer polynomial $f$ and $n\in\mathbb N$ we define `deriv_n f n` to be the $n$-th derivative of polynomial $f$. $h^{[n]}$ means $h\circ h\circ h\cdots\circ h$ $n$-times.

TODO: Remove this entirely.
-/
def deriv_n (f : ℤ[X]) (n : ℕ) : ℤ[X] := polynomial.derivative ^[n] f

namespace e_transcendental_lemmas

/-- # Assumption-/
/-Theorem
fundamental theorem of calculus and integration by part is assumed. I am waiting for them to arrive in `mathlib` and I will update this part and prove relatvent additional assumptions.
-/

theorem integrate_by_part (f g : ℝ -> ℝ)
  {hf : differentiable ℝ f} {hf4 : continuous (deriv f)}
  {hg : differentiable ℝ g} {hg4 : continuous (deriv g)}
  (a b : ℝ) :
  (∫ x in a..b, (f x)*(deriv g x)) = (f b) * (g b) - (f a) * (g a) - (∫ x in a..b, (deriv f x) * (g x)) :=

begin
  have := @interval_integral.integral_mul_deriv_eq_deriv_mul a b f g (deriv f) (deriv g) _ _ _ _,
  { convert this, ext, rw mul_comm },
  { intros x hx, simp only [has_deriv_at_deriv_iff], exact hf.differentiable_at },
  { intros x hx, simp only [has_deriv_at_deriv_iff], exact hg.differentiable_at },
  { exact continuous_on.interval_integrable hf4.continuous_on },
  { exact continuous_on.interval_integrable hg4.continuous_on },
end

/-Theorem
If forall $x\in(a,b), 0 \le f(x)\le c$ then
$$
\int_a^b f\le (b-a)c
$$
-/
theorem integral_le_max_times_length (f : ℝ -> ℝ) {h1 : measurable f} (a b : ℝ) (h : a ≤ b) (c : ℝ)
    (f_nonneg : ∀ x ∈ set.Icc a b, 0 ≤ f x) (c_max : ∀ x ∈ set.Icc a b, f x ≤ c) :
    (∫ x in a..b, f x) ≤ (b - a) * c :=
begin
    rw [mul_comm, ←abs_of_nonneg (sub_nonneg_of_le h)],
    have triv1 : (∫ x in a..b, f x) = ∥(∫ x in a..b, f x)∥,
    {
        rw real.norm_eq_abs,
        rw abs_of_nonneg,
        rw interval_integral.integral_of_le h,
        apply measure_theory.integral_nonneg_of_ae,
        apply (@measure_theory.ae_restrict_iff ℝ _ _ (set.Ioc a b) _ _).2,
        { apply measure_theory.ae_of_all,
          intros x hx,
          simp only [and_imp, set.mem_Ioc, pi.zero_apply, ge_iff_le, set.mem_Icc] at *,
          refine f_nonneg x hx.1.le hx.2 },
        { simp only [pi.zero_apply],
          refine measurable_set_le measurable_zero h1 },
    },
    rw triv1,
    apply interval_integral.norm_integral_le_of_norm_le_const _,
    rw set.interval_oc_of_le h,
    intros x hx,
    rw real.norm_eq_abs,
    rw abs_of_nonneg,
    { exact c_max _ (set.Ioc_subset_Icc_self hx) },
    refine f_nonneg x _,
    exact set.Ioc_subset_Icc_self hx,
end

/-Theorem
$$
\frac{\mathrm{d}\exp(t-x)}{\mathrm{d}x}=-\exp(t-x)
$$
-/
theorem deriv_exp_t_x (t : ℝ) : deriv (λ x, real.exp (t-x)) = -(λ x, real.exp (t-x)) :=
begin
    have triv : (λ x, real.exp (t-x)) = real.exp ∘ (λ x, t - x) := by simp only [],
    ext,
    rw triv,
    rw deriv.scomp, simp only [neg_mul, deriv_exp, differentiable_at_const, mul_one, algebra.id.smul_eq_mul, one_mul, zero_sub, deriv_sub, differentiable_at_id', pi.neg_apply, deriv_id'', deriv_const'],

    simp only [differentiable_at_id', differentiable_at.exp],
    apply differentiable_at.const_sub,
    exact differentiable_at_id,
end

/-Theorem
$$
\frac{\mathrm{d}-\exp(t-x)}{\mathrm{d}x}=\exp(t-x)
$$
-/
theorem deriv_exp_t_x' (t : ℝ) : (deriv (λ x, - (real.exp (t-x)))) = (λ x, real.exp (t-x)) :=
begin
    simp only [deriv_exp, differentiable_at_const, mul_one, zero_sub, deriv_sub, differentiable_at_id', deriv_id'', deriv.neg', deriv_const', mul_neg, differentiable_at.sub, neg_neg],
end

/--
# about I
-/

/-Definition
Suppose $f$ is an integer polynomial with degree $n$ and $t\ge0$ then define
    \[I(f,t):=\int_0^t \exp(t-x)f(z)\mathrm{d}x\]
We use integration by parts to prove
    \[I(f,t)=\exp(t)\left(\sum_{i=0}^n f^{(i)}(0)\right)-\sum_{i=0}^n f^{(i)}(t)\]

The two different ways of representing $I(f,t)$ we give us upper bound and lower bound when we are using this on transcendence of $e$.
-/
def I (f : ℤ[X]) (t : ℝ) : ℝ :=
    t.exp * (∑ i in finset.range f.nat_degree.succ, (f_eval_on_ℝ (polynomial.derivative^[i] f) 0)) -
    (∑ i in finset.range f.nat_degree.succ, (f_eval_on_ℝ (polynomial.derivative^[i] f) t))

/--
I equivalent definition
\[I(f,t):=\int_0^t \exp(t-x)f(z)\mathrm{d}x\]
-/
def II (f : ℤ[X]) (t : ℝ) : ℝ := ∫ x in 0..t, real.exp(t - x) * (f_eval_on_ℝ f x)

/-Theorem
$I(0,t)$ is 0.
-/
theorem II_0 (t : ℝ) : II 0 t = 0 :=
begin
    -- We are integrating $\exp(t-x)\times 0$
    rw II, unfold f_eval_on_ℝ,
    simp only [mul_zero, polynomial.aeval_zero, polynomial.map_zero,
        interval_integral.integral_const, smul_zero],
end

lemma differentiable_aeval (f : ℤ[X]) :
    differentiable ℝ (λ (x : ℝ), (polynomial.aeval x) (f)) :=
begin
      simp only [polynomial.aeval_def, polynomial.eval₂_eq_eval_map],
      apply polynomial.differentiable,

end


/-Theorem
By integration by part we have:
\[I(f, t) = e^tf(0)-f(t)+I(f',t)\]
-/
lemma II_integrate_by_part (f : ℤ[X]) (t : ℝ) :
    (II f t) = (real.exp t) * (f_eval_on_ℝ f 0) - (f_eval_on_ℝ f t) + (II f.derivative t) :=
begin
  rw II,
  convert integrate_by_part (f_eval_on_ℝ f) (λ (x : ℝ), -(t - x).exp) 0 t using 1,
  { simp only [deriv_exp_t_x', mul_comm] },
  { simp only [sub_eq_add_neg],
    apply congr_arg2,
    { simp only [add_zero, neg_zero', mul_one, real.exp_zero, add_right_neg, neg_neg], ring },
    { simp_rw [II, f_eval_on_ℝ_deriv, ←interval_integral.integral_neg, neg_mul_eq_mul_neg, neg_neg,
        ←sub_eq_add_neg, mul_comm] } },
  { apply differentiable_aeval f },
  { rw f_eval_on_ℝ_deriv,
    exact (differentiable_aeval f.derivative).continuous },
  { exact (real.differentiable_exp.comp (differentiable_id'.const_sub t)).neg, },
  { rw deriv_exp_t_x',
    exact (real.differentiable_exp.comp (differentiable_id'.const_sub t)).continuous },
end

/-Theorem
Combine the theorem above with induction we get for all $m\in\mathbb N$
\[
I(f,t)=e^t\sum_{i=0}^m f^{(i)}(0)-\sum_{i=0}^m f^{(i)}(t)
\]
-/
lemma II_integrate_by_part_m (f : ℤ[X]) (t : ℝ) (m : ℕ) :
  II f t = t.exp * (∑ i in finset.range (m+1), (f_eval_on_ℝ (polynomial.derivative^[i] f) 0)) -
  (∑ i in finset.range (m+1), f_eval_on_ℝ (polynomial.derivative^[i] f) t) +
  (II (polynomial.derivative^[m + 1] f) t) :=
begin
    induction m with m ih,
    {   rw [II_integrate_by_part],
        simp only [function.iterate_one, finset.sum_singleton, finset.range_one,
            function.iterate_zero_apply] },

    rw [ih, II_integrate_by_part, finset.sum_range_succ _ (m + 1),
        finset.sum_range_succ _ (m + 1), ←function.iterate_succ_apply' polynomial.derivative],
    ring,
end

/-Theorem
So the using if $f$ has degree $n$, then $f^{(n+1)}$ is zero we have the two definition of $I(f,t)$ agrees.
-/
theorem II_eq_I (f : ℤ[X]) (t : ℝ) : II f t = I f t :=
begin
  have II_integrate_by_part_m := II_integrate_by_part_m f t f.nat_degree,
  rwa [polynomial.iterate_derivative_eq_zero (nat.lt_succ_self _), II_0, add_zero] at
    II_integrate_by_part_m,
end

/-- # $\bar{f}$
- Say $f(T)=a_0+a_1T+a_2T^2+\cdots+a_nT^n$. Then $\bar{f}=|a_0|+|a_1|T+|a_2|T^2+\cdots+|a_n|T^n$
- We proved some theorems about $\bar{f}$
-/

def f_bar (f : ℤ[X]) : ℤ[X] :=
⟨{ support := f.support,
  to_fun  := λ n, abs (f.coeff n),
  mem_support_to_fun := λ n, by rw [ne.def, abs_eq_zero, polynomial.mem_support_iff]}⟩

/-Theorem
By our construction the $n$-th coefficient of $\bar{f}$ is the absolute value of $n$-th coefficient of $f$
-/
theorem bar_coeff (f : ℤ[X]) (n : ℕ) : (f_bar f).coeff n = abs (f.coeff n) :=
begin
    -- true by definition
    dsimp [f_bar], refl,
end

/-Theorem
By our construction, $\bar{f}$ and $f$ has the same support
-/
theorem bar_supp (f : ℤ[X]) : (f_bar f).support = f.support :=
begin
    -- true by definition
    dsimp [f_bar], refl,
end

/-Theorem
Since $\bar{f}$ and $f$ has the same support, they have the same degree.
-/
theorem bar_same_deg (f : ℤ[X]) : (f_bar f).nat_degree = f.nat_degree :=
begin
    apply polynomial.nat_degree_eq_of_degree_eq,
    -- degree is defined to be $\sup$ of support. Since support of $\bar{f}$ and $f$ are the same, their degree is the same.
    rw polynomial.degree, rw polynomial.degree, rw bar_supp,
end

/-Theorem
$\bar{0}=0$
-/
theorem f_bar_0 : f_bar 0 = 0 :=
begin
    ext, rw bar_coeff, simp only [abs_zero, polynomial.coeff_zero],
end

/-Theorem
for any $f\in\mathbb Z$, if $\bar{f}=0$ then $f=0$
-/
theorem f_bar_eq_0 (f : ℤ[X]) : f_bar f = 0 -> f = 0 :=
begin
    intro h, rw polynomial.ext_iff at h, ext,
    have hn := h n, simp only [polynomial.coeff_zero] at hn, rw bar_coeff at hn, simp only [abs_eq_zero, polynomial.coeff_zero] at hn ⊢, assumption,
end

theorem coeff_f_bar_mul (f g : ℤ[X]) (n : ℕ) : (f_bar (f*g)).coeff n = abs(∑ p in finset.nat.antidiagonal n, (f.coeff p.1)*(g.coeff p.2)) :=
begin
    rw bar_coeff (f*g) n, rw polynomial.coeff_mul,
end

theorem f_bar_eq (f : ℤ[X]) : f_bar f = ∑ i in finset.range f.nat_degree.succ, polynomial.C (abs (f.coeff i)) * polynomial.X^i :=
begin
    ext, rw bar_coeff, rw polynomial.finset_sum_coeff, simp_rw [polynomial.coeff_C_mul_X_pow],
    simp only [finset.mem_range, finset.sum_ite_eq], split_ifs, refl, simp only [not_lt] at h,
    rw polynomial.coeff_eq_zero_of_nat_degree_lt h, exact rfl,
end

lemma polynomial.aeval_eq_sum_support {R A : Type*} [comm_semiring R] [comm_semiring A] [algebra R A]
    (x : A) (f : R[X]) :
    polynomial.aeval x f = ∑ i in f.support, (f.coeff i) • x ^ i:=
begin
  simp_rw [polynomial.aeval_def, polynomial.eval₂_eq_sum, polynomial.sum, algebra.smul_def],
end

/-Theorem
For any $x\in(0,t)$
$|f(x)|\le \bar{f}(t)$
-/
lemma f_bar_ineq (f : ℤ[X]) (t : ℝ) : ∀ x ∈ set.Icc 0 t, abs (f_eval_on_ℝ f x) ≤ f_eval_on_ℝ (f_bar f) t :=
begin
  intros x hx,
  rw set.mem_Icc at hx,
  calc |f_eval_on_ℝ f x| = |∑ i in f.support, (f.coeff i : ℝ) * x ^ i| : _
  ... ≤ ∑ i in f.support, |(f.coeff i:ℝ) * x ^ i| : finset.abs_sum_le_sum_abs _ _
  ... = ∑ i in f.support, |(f.coeff i:ℝ)| * x ^ i : finset.sum_congr rfl (λ i hi, _)
  ... ≤ ∑ i in (f_bar f).support, abs (f.coeff i:ℝ) * t ^ i : _
  ... = _ : _,
  { rw [f_eval_on_ℝ, polynomial.aeval_eq_sum_support x f], simp only [zsmul_eq_mul] },
  { have := pow_nonneg hx.1 i,
    rw [abs_mul, abs_of_nonneg this], },
  { rw bar_supp,
    refine finset.sum_le_sum (λ n hn, mul_le_mul_of_nonneg_left _ (abs_nonneg _)),
    exact pow_le_pow_of_le_left hx.1 hx.2 _ },
  { rw [f_eval_on_ℝ, polynomial.aeval_eq_sum_support],
    simp only [e_transcendental_lemmas.bar_coeff, finset.sum_congr, zsmul_eq_mul, int.cast_abs] }
end

/-Theorem
$$|I(f,t)|\le te^t\bar{f}(t)$$
-/
theorem abs_II_le2 (f : ℤ[X]) (t : ℝ) (ht : 0 ≤ t) : abs (II f t) ≤ t * t.exp * (f_eval_on_ℝ (f_bar f) t) :=
begin
  refine (interval_integral.abs_integral_le_integral_abs ht).trans _,
  convert integral_le_max_times_length ((λ x, abs ((t - x).exp * f_eval_on_ℝ f x))) 0 t ht
    (t.exp * f_eval_on_ℝ (f_bar f) t) (λ x _, abs_nonneg _) _ using 1,
  { rw [sub_zero, mul_assoc], },
  { refine continuous.measurable _,
    refine continuous_abs.comp _,
    exact continuous.mul (real.continuous_exp.comp (continuous_sub_left _))
      (differentiable_aeval _).continuous},
  { intros x hx,
    rw [abs_mul, real.abs_exp],
    refine mul_le_mul _ (f_bar_ineq f t x hx) (abs_nonneg _) (real.exp_pos t).le,
    rw set.mem_Icc at hx,
    rw [real.exp_le_exp, sub_le, sub_self], exact hx.1 },
end

end e_transcendental_lemmas

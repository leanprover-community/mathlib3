/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import ring_theory.polynomial.bernstein
import topology.continuous_function.polynomial

/-!
# Bernstein approximations and Weierstrass' theorem

We prove that the Bernstein approximations
```
∑ k : fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)
```
for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.

Our proof follows [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D.
The original proof, due to [Bernstein](bernstein1912) in 1912, is probabilistic,
and relies on Bernoulli's theorem,
which gives bounds for how quickly the observed frequencies in a
Bernoulli trial approach the underlying probability.

The proof here does not directly rely on Bernoulli's theorem,
but can also be given a probabilistic account.
* Consider a weighted coin which with probability `x` produces heads,
  and with probability `1-x` produces tails.
* The value of `bernstein n k x` is the probability that
  such a coin gives exactly `k` heads in a sequence of `n` tosses.
* If such an appearance of `k` heads results in a payoff of `f(k / n)`,
  the `n`-th Bernstein approximation for `f` evaluated at `x` is the expected payoff.
* The main estimate in the proof bounds the probability that
  the observed frequency of heads differs from `x` by more than some `δ`,
  obtaining a bound of `(4 * n * δ^2)⁻¹`, irrespective of `x`.
* This ensures that for `n` large, the Bernstein approximation is (uniformly) close to the
  payoff function `f`.

(You don't need to think in these terms to follow the proof below: it's a giant `calc` block!)

This result proves Weierstrass' theorem that polynomials are dense in `C([0,1], ℝ)`,
although we defer an abstract statement of this until later.
-/

noncomputable theory

open_locale classical
open_locale big_operators
open_locale bounded_continuous_function
open_locale unit_interval

/--
The Bernstein polynomials, as continuous functions on `[0,1]`.
-/
def bernstein (n ν : ℕ) : C(I, ℝ) :=
(bernstein_polynomial ℝ n ν).to_continuous_map_on I

@[simp] lemma bernstein_apply (n ν : ℕ) (x : I) :
  bernstein n ν x = n.choose ν * x^ν * (1-x)^(n-ν) :=
begin
  dsimp [bernstein, polynomial.to_continuous_map_on, polynomial.to_continuous_map,
    bernstein_polynomial],
  simp,
end

lemma bernstein_nonneg {n ν : ℕ} {x : I} :
  0 ≤ bernstein n ν x :=
begin
  simp only [bernstein_apply],
  exact mul_nonneg
    (mul_nonneg (nat.cast_nonneg _) (pow_nonneg (by unit_interval) _))
    (pow_nonneg (by unit_interval) _),
end

/-!
We now give a slight reformulation of `bernstein_polynomial.variance`.
-/

namespace bernstein

/--
Send `k : fin (n+1)` to the equally spaced points `k/n` in the unit interval.
-/
def z {n : ℕ} (k : fin (n+1)) : I :=
⟨(k : ℝ) / n,
  begin
    cases n,
    { norm_num },
    { have h₁ : 0 < (n.succ : ℝ) := by exact_mod_cast (nat.succ_pos _),
      have h₂ : ↑k ≤ n.succ := by exact_mod_cast (fin.le_last k),
      rw [set.mem_Icc, le_div_iff h₁, div_le_iff h₁],
      norm_cast,
      simp [h₂], },
  end⟩

local postfix `/ₙ`:90 := z

lemma probability (n : ℕ) (x : I) :
  ∑ k : fin (n+1), bernstein n k x = 1 :=
begin
  have := bernstein_polynomial.sum ℝ n,
  apply_fun (λ p, polynomial.aeval (x : ℝ) p) at this,
  simp [alg_hom.map_sum, finset.sum_range] at this,
  exact this,
end

lemma variance {n : ℕ} (h : 0 < (n : ℝ)) (x : I) :
  ∑ k : fin (n+1), (x - k/ₙ : ℝ)^2 * bernstein n k x = x * (1-x) / n :=
begin
  have h' : (n : ℝ) ≠ 0 := ne_of_gt h,
  apply_fun (λ x : ℝ, x * n) using group_with_zero.mul_right_injective h',
  apply_fun (λ x : ℝ, x * n) using group_with_zero.mul_right_injective h',
  dsimp,
  conv_lhs { simp only [finset.sum_mul, z], },
  conv_rhs { rw div_mul_cancel _ h', },
  have := bernstein_polynomial.variance ℝ n,
  apply_fun (λ p, polynomial.aeval (x : ℝ) p) at this,
  simp [alg_hom.map_sum, finset.sum_range, ←polynomial.nat_cast_mul] at this,
  convert this using 1,
  { congr' 1, funext k,
    rw [mul_comm _ (n : ℝ), mul_comm _ (n : ℝ), ←mul_assoc, ←mul_assoc],
    congr' 1,
    field_simp [h],
    ring, },
  { ring, },
end

end bernstein

open bernstein

local postfix `/ₙ`:2000 := z
local notation `|`x`|` := abs x

/--
The `n`-th approximation of a continuous function on `[0,1]` by Bernstein polynomials,
given by `∑ k, f (k/n) * bernstein n k x`.
-/
def bernstein_approximation (n : ℕ) (f : C(I, ℝ)) : C(I, ℝ) :=
∑ k : fin (n+1), f k/ₙ • bernstein n k

/-!
We now set up some of the basic machinery of the proof that the Bernstein approximations
converge uniformly.

A key player is the set `S f ε h n x`,
for some function `f : C(I, ℝ)`, `h : 0 < ε`, `n : ℕ` and `x : I`.

This is the set of points `k` in `fin (n+1)` such that
`k/n` is within `δ` of `x`, where `δ` is the modulus of uniform continuity for `f`,
chosen so `|f x - f y| < ε/2` when `|x - y| < δ`.

We show that if `k ∉ S`, then `1 ≤ δ^-2 * (x - k/n)^2`.
-/

namespace bernstein_approximation

@[simp] lemma apply (n : ℕ) (f : C(I, ℝ)) (x : I) :
  bernstein_approximation n f x = ∑ k : fin (n+1), f k/ₙ * bernstein n k x :=
by simp [bernstein_approximation]

/--
The modulus of (uniform) continuity for `f`, chosen so `|f x - f y| < ε/2` when `|x - y| < δ`.
-/
def δ (f : C(I, ℝ)) (ε : ℝ) (h : 0 < ε) : ℝ := f.modulus (ε/2) (half_pos h)

/--
The set of points `k` so `k/n` is within `δ` of `x`.
-/
def S (f : C(I, ℝ)) (ε : ℝ) (h : 0 < ε) (n : ℕ) (x : I) : finset (fin (n+1)) :=
{ k : fin (n+1) | dist k/ₙ x < δ f ε h }.to_finset

/--
If `k ∈ S`, then `f(k/n)` is close to `f x`.
-/
lemma lt_of_mem_S
  {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : fin (n+1)} (m : k ∈ S f ε h n x) :
  |f k/ₙ - f x| < ε/2 :=
begin
  apply f.dist_lt_of_dist_lt_modulus (ε/2) (half_pos h),
  simpa [S] using m,
end

/--
If `k ∉ S`, then as `δ ≤ |x - k/n|`, we have the inequality `1 ≤ δ^-2 * (x - k/n)^2`.
This particular formulation will be helpful later.
-/
lemma le_of_mem_S_compl
  {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : fin (n+1)} (m : k ∈ (S f ε h n x)ᶜ) :
  (1 : ℝ) ≤ (δ f ε h)^(-2 : ℤ) * (x - k/ₙ) ^ 2 :=
begin
  simp only [finset.mem_compl, not_lt, set.mem_to_finset, set.mem_set_of_eq, S] at m,
  field_simp,
  erw [le_div_iff (pow_pos f.modulus_pos 2), one_mul],
  apply sq_le_sq,
  rw abs_eq_self.mpr (le_of_lt f.modulus_pos),
  rw [dist_comm] at m,
  exact m,
end

end bernstein_approximation

open bernstein_approximation
open bounded_continuous_function
open filter

open_locale topological_space

/--
The Bernstein approximations
```
∑ k : fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)
```
for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.

This is the proof given in [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D,
and reproduced on wikipedia.
-/
theorem bernstein_approximation_uniform (f : C(I, ℝ)) :
  tendsto (λ n : ℕ, bernstein_approximation n f) at_top (𝓝 f) :=
begin
  simp only [metric.nhds_basis_ball.tendsto_right_iff, metric.mem_ball, dist_eq_norm],
  intros ε h,
  let δ := δ f ε h,
  have nhds_zero := tendsto_const_div_at_top_nhds_0_nat (2 * ∥f∥ * δ ^ (-2 : ℤ)),
  filter_upwards [nhds_zero.eventually (gt_mem_nhds (half_pos h)), eventually_gt_at_top 0],
  intros n nh npos',
  have npos : 0 < (n:ℝ) := by exact_mod_cast npos',
  -- Two easy inequalities we'll need later:
  have w₁ : 0 ≤ 2 * ∥f∥ := mul_nonneg (by norm_num) (norm_nonneg f),
  have w₂ : 0 ≤ 2 * ∥f∥ * δ^(-2 : ℤ) := mul_nonneg w₁ pow_minus_two_nonneg,
  -- As `[0,1]` is compact, it suffices to check the inequality pointwise.
  rw (continuous_map.norm_lt_iff _ h),
  intro x,
  -- The idea is to split up the sum over `k` into two sets,
  -- `S`, where `x - k/n < δ`, and its complement.
  let S := S f ε h n x,
  calc
    |(bernstein_approximation n f - f) x|
        = |bernstein_approximation n f x - f x|
                              : rfl
    ... = |bernstein_approximation n f x - f x * 1|
                              : by rw mul_one
    ... = |bernstein_approximation n f x - f x * (∑ k : fin (n+1), bernstein n k x)|
                              : by rw bernstein.probability
    ... = |∑ k : fin (n+1), (f k/ₙ - f x) * bernstein n k x|
                              : by simp [bernstein_approximation, finset.mul_sum, sub_mul]
    ... ≤ ∑ k : fin (n+1), |(f k/ₙ - f x) * bernstein n k x|
                              : finset.abs_sum_le_sum_abs _ _
    ... = ∑ k : fin (n+1), |f k/ₙ - f x| * bernstein n k x
                              : by simp_rw [abs_mul, abs_eq_self.mpr bernstein_nonneg]
    ... = ∑ k in S, |f k/ₙ - f x| * bernstein n k x +
          ∑ k in Sᶜ, |f k/ₙ - f x| * bernstein n k x
                              : (S.sum_add_sum_compl _).symm
    -- We'll now deal with the terms in `S` and the terms in `Sᶜ` in separate calc blocks.
    ... < ε/2 + ε/2 : add_lt_add_of_le_of_lt _ _
    ... = ε : add_halves ε,
    { -- We now work on the terms in `S`: uniform continuity and `bernstein.probability`
      -- quickly give us a bound.
      calc ∑ k in S, |f k/ₙ - f x| * bernstein n k x
          ≤ ∑ k in S, ε/2 * bernstein n k x
                                :  finset.sum_le_sum
                                    (λ k m, (mul_le_mul_of_nonneg_right (le_of_lt (lt_of_mem_S m))
                                      bernstein_nonneg))
      ... = ε/2 * ∑ k in S, bernstein n k x
                                : by rw finset.mul_sum
      -- In this step we increase the sum over `S` back to a sum over all of `fin (n+1)`,
      -- so that we can use `bernstein.probability`.
      ... ≤ ε/2 * ∑ k : fin (n+1), bernstein n k x
                                : mul_le_mul_of_nonneg_left
                                    (finset.sum_le_univ_sum_of_nonneg (λ k, bernstein_nonneg))
                                    (le_of_lt (half_pos h))
      ... = ε/2 : by rw [bernstein.probability, mul_one] },
      { -- We now turn to working on `Sᶜ`: we control the difference term just using `∥f∥`,
        -- and then insert a `δ^(-2) * (x - k/n)^2` factor
        -- (which is at least one because we are not in `S`).
        calc ∑ k in Sᶜ, |f k/ₙ - f x| * bernstein n k x
            ≤ ∑ k in Sᶜ, (2 * ∥f∥) * bernstein n k x
                                  : finset.sum_le_sum
                                      (λ k m, mul_le_mul_of_nonneg_right (f.dist_le_two_norm _ _)
                                        bernstein_nonneg)
        ... = (2 * ∥f∥) * ∑ k in Sᶜ, bernstein n k x
                                  : by rw finset.mul_sum
        ... ≤ (2 * ∥f∥) * ∑ k in Sᶜ, δ^(-2 : ℤ) * (x - k/ₙ)^2 * bernstein n k x
                                  : mul_le_mul_of_nonneg_left
                                      (finset.sum_le_sum (λ k m, begin
                                        conv_lhs { rw ←one_mul (bernstein _ _ _), },
                                        exact mul_le_mul_of_nonneg_right
                                          (le_of_mem_S_compl m) bernstein_nonneg,
                                      end)) w₁
        -- Again enlarging the sum from `Sᶜ` to all of `fin (n+1)`
        ... ≤ (2 * ∥f∥) * ∑ k : fin (n+1), δ^(-2 : ℤ) * (x - k/ₙ)^2 * bernstein n k x
                                  : mul_le_mul_of_nonneg_left
                                      (finset.sum_le_univ_sum_of_nonneg
                                        (λ k, mul_nonneg
                                          (mul_nonneg pow_minus_two_nonneg (sq_nonneg _))
                                          bernstein_nonneg)) w₁
        ... = (2 * ∥f∥) * δ^(-2 : ℤ) * ∑ k : fin (n+1), (x - k/ₙ)^2 * bernstein n k x
                                  : by conv_rhs {
                                      rw [mul_assoc, finset.mul_sum], simp only [←mul_assoc], }
        -- `bernstein.variance` and `x ∈ [0,1]` gives the uniform bound
        ... = (2 * ∥f∥) * δ^(-2 : ℤ) * x * (1-x) / n
                                  : by { rw variance npos, ring, }
        ... ≤ (2 * ∥f∥) * δ^(-2 : ℤ) / n
                                  : (div_le_div_right npos).mpr
                                    begin
                                      apply mul_nonneg_le_one_le w₂,
                                      apply mul_nonneg_le_one_le w₂ (le_refl _),
                                      all_goals { unit_interval, },
                                    end
        ... < ε/2 : nh, }
end

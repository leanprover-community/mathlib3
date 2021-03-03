/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.polynomial.bernstein
import topology.instances.real
import topology.algebra.continuous_functions
import topology.algebra.polynomial
import analysis.normed_space.basic
import topology.bounded_continuous_function
import topology.uniform_space.compact_separated
import algebra.floor
import analysis.specific_limits

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

-- FIXME find a home for this
lemma mul_unit_interval_le {α : Type*} [ordered_semiring α] {a b c : α}
  (h₁ : 0 ≤ c) (h₂ : a ≤ c) (h₃ : 0 ≤ b) (h₄ : b ≤ 1) : a * b ≤ c :=
begin
  conv_rhs { rw ←mul_one c, },
  exact mul_le_mul h₂ h₄ h₃ h₁,
end

/--
The Bernstein polynomials, as continuous functions on ℝ.
-/
def bernstein' (n ν : ℕ) : C(ℝ, ℝ) :=
⟨λ x : ℝ, (bernstein_polynomial ℝ n ν).eval x, by continuity⟩

-- TODO there's some orphaned development regarding `[0,1]` in `topology.path_connected`;
-- perhaps this should be consolidated.
local notation `I` := set.Icc (0 : ℝ) (1 : ℝ)

namespace unit_interval

lemma nonneg (x : I) : 0 ≤ (x : ℝ) := x.2.1
lemma one_minus_nonneg (x : I) : 0 ≤ 1 - (x : ℝ) := by simpa using x.2.2
lemma le_one (x : I) : (x : ℝ) ≤ 1 := x.2.2
lemma one_minus_le_one (x : I) : 1 - (x : ℝ) ≤ 1 := by simpa using x.2.1

end unit_interval

namespace tactic.interactive

/-- A tactic that solves `0 ≤ x`, `0 ≤ 1 - x`, `x ≤ 1`, and `1 - x ≤ 1` for `x : I`. -/
meta def unit_interval : tactic unit :=
`[apply unit_interval.nonneg] <|> `[apply unit_interval.one_minus_nonneg] <|>
`[apply unit_interval.le_one] <|> `[apply unit_interval.one_minus_le_one]

end tactic.interactive

instance : has_zero I := ⟨⟨0, ⟨le_refl _, le_of_lt real.zero_lt_one⟩⟩⟩
instance : has_one I := ⟨⟨1, ⟨le_of_lt real.zero_lt_one, le_refl _⟩⟩⟩
instance : nonempty I := ⟨0⟩

-- FIXME Where do these lemmas belong?
-- Should they become part of a public API, or remain hidden here?
-- They really belong on `C(α,β)` rather than `α →ᵇ β`.

namespace bounded_continuous_function
variables {α β : Type*} [metric_space α] [compact_space α] [metric_space β]

/-!
We now set up some abbreviations for the various components of
uniform continuity for a continuous function on a compact metric space.
-/
lemma uniform_continuity
  (f : α →ᵇ β) (ε : ℝ) (h : 0 < ε) :
  ∃ δ > 0, ∀ {x y}, dist x y < δ → dist (f x) (f y) < ε :=
metric.uniform_continuous_iff.mp
  (compact_space.uniform_continuous_of_continuous f.2.1) ε h

/--
The (noncomputable) modulus of uniform continuity for a given function `f` and `ε > 0`.
-/
def modulus (f : α →ᵇ β) (ε : ℝ) (h : 0 < ε) : ℝ :=
classical.some (uniform_continuity f ε h)

lemma modulus_pos (f : α →ᵇ β) {ε : ℝ} {h : 0 < ε} : 0 < f.modulus ε h :=
classical.some (classical.some_spec (uniform_continuity f ε h))

lemma dist_lt_of_dist_lt_modulus
  (f : α →ᵇ β) (ε : ℝ) (h : 0 < ε) {a b : α} (w : dist a b < f.modulus ε h) :
  dist (f a) (f b) < ε :=
classical.some_spec (classical.some_spec (uniform_continuity f ε h)) w

end bounded_continuous_function


/--
The Bernstein polynomials, as bounded continuous functions on `[0,1]`.
-/
def bernstein (n ν : ℕ) : I →ᵇ ℝ :=
bounded_continuous_function.mk_of_compact
  (λ x, bernstein' n ν x) (by continuity)

@[simp] lemma bernstein_apply (n ν : ℕ) (x : I) :
  bernstein n ν x = n.choose ν * x^ν * (1-x)^(n-ν) :=
begin
  dsimp [bernstein, bernstein', bernstein_polynomial],
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

namespace bernstein

/--
Send `k : fin (n+1)` to the equally spaced points `k/n` in the unit interval.
-/
def z {n : ℕ} (k : fin (n+1)) : I :=
⟨(k : ℝ) / n,
  begin
    rcases k with ⟨k,w⟩,
    fsplit,
    { simp only [fin.coe_mk, coe_coe],
      exact div_nonneg (nat.cast_nonneg k) (nat.cast_nonneg n), },
    { simp only [fin.coe_mk, coe_coe],
      cases n,
      norm_num,
      rw div_le_iff,
      { simp only [one_mul, nat.cast_succ], norm_cast, exact nat.le_of_lt_succ w, },
      { norm_cast, exact nat.succ_pos _, }, }
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
  have h' : (n : ℝ) ≠ 0 := (ne_of_lt h).symm,
  apply_fun (λ x : ℝ, x * n) using group_with_zero.mul_right_injective h',
  apply_fun (λ x : ℝ, x * n) using group_with_zero.mul_right_injective h',
  dsimp,
  conv_lhs { simp only [finset.sum_mul, z], },
  conv_rhs { rw div_mul_cancel _ h', },
  have := bernstein_polynomial.variance ℝ n,
  apply_fun (λ p, polynomial.aeval (x : ℝ) p) at this,
  simp [alg_hom.map_sum, finset.sum_range, polynomial.nat_smul] at this,
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

/--
The `n`-th approximation of a continuous function on `[0,1]` by Bernstein polynomials,
given by `∑ k, f (k/n) * bernstein n k x`.
-/
def bernstein_approximation (n : ℕ) (f : I →ᵇ ℝ) : I →ᵇ ℝ :=
∑ k : fin (n+1), f k/ₙ • bernstein n k

namespace bernstein_approximation

@[simp] lemma apply (n : ℕ) (f : I →ᵇ ℝ) (x : I) :
  bernstein_approximation n f x = ∑ k : fin (n+1), f k/ₙ * bernstein n k x :=
by simp [bernstein_approximation]

/--
The set of points `k` so `k/n` is within `δ` of `x`.
-/
def S (f : I →ᵇ ℝ) (ε : ℝ) (h : 0 < ε) (n : ℕ) (x : I) : finset (fin (n+1)) :=
{ k : fin (n+1) | dist k/ₙ x < f.modulus (ε/2) (half_pos h) }.to_finset

/--
If `k ∈ S`, then `f(k/n)` is close to `f x`.
-/
lemma lt_of_mem_S
  {f : I →ᵇ ℝ} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : fin (n+1)} (m : k ∈ S f ε h n x) :
  abs (f k/ₙ - f x) < ε/2 :=
begin
  apply f.dist_lt_of_dist_lt_modulus (ε/2) (half_pos h),
  simpa [S] using m,
end

/--
If `k ∉ S`, then as `δ ≤ abs (x - k/n)`, we have the inequality `1 ≤ δ^-2 * (x - k/n)^2`.
This particular formulation will be helpful later.
-/
lemma le_of_mem_S_compl
  {f : I →ᵇ ℝ} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : fin (n+1)} (m : k ∈ (S f ε h n x)ᶜ) :
  (1 : ℝ) ≤ (f.modulus (ε/2) (half_pos h))^(-2 : ℤ) * (x - k/ₙ) ^ 2 :=
begin
  simp only [finset.mem_compl, not_lt, set.mem_to_finset, set.mem_set_of_eq, S] at m,
  field_simp,
  erw [le_div_iff (pow_pos f.modulus_pos 2), one_mul],
  apply sqr_le_sqr,
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
This is the proof given in [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D,
and reproduced on wikipedia.
-/
theorem bernstein_approximation_uniform (f : I →ᵇ ℝ) :
  tendsto (λ n : ℕ, bernstein_approximation n f) at_top (𝓝 f) :=
begin
  apply normed_group.tendsto_at_top.mpr,
  intros ε h,
  let δ := f.modulus (ε/2) (half_pos h),
  let N : ℕ := _, use N, -- We postpone choosing `n` until we've obtained an explicit estimate.
  intros n nh,
  have npos : 0 < (n : ℝ) := by exact_mod_cast (pos_of_gt nh),
  -- Three easy inequalities we'll need later:
  have w₀ : 0 ≤ ε / 2 := le_of_lt (half_pos h),
  have w₁ : 0 ≤ 2 * ∥f∥ := mul_nonneg (by norm_num) (norm_nonneg f),
  have w₂ : 0 ≤ 2 * ∥f∥ * δ^(-2 : ℤ) := mul_nonneg w₁ pow_minus_two_nonneg,
  -- As `[0,1]` is compact, it suffices to check the inequality pointwise.
  apply bounded_continuous_function.norm_lt_of_compact,
  intro x,
  -- The idea is to split up the sum over `k` into two sets,
  -- `S`, where `x - k/n < δ`, and its complement.
  let S := S f ε h n x,
  calc
    abs ((bernstein_approximation n f - f) x)
        = abs (bernstein_approximation n f x - f x)
                              : rfl
    ... = abs (bernstein_approximation n f x - f x * 1)
                              : by rw mul_one
    ... = abs (bernstein_approximation n f x - f x * (∑ k : fin (n+1), bernstein n k x))
                              : by rw bernstein.probability
    ... = abs (bernstein_approximation n f x - (∑ k : fin (n+1), f x * bernstein n k x))
                              : by rw finset.mul_sum
    ... = abs (∑ k : fin (n+1), (f k/ₙ - f x) * bernstein n k x)
                              : begin
                                  dsimp [bernstein_approximation],
                                  simp only [coe_sum, coe_smul, finset.sum_apply,
                                    ←finset.sum_sub_distrib, algebra.id.smul_eq_mul, ←sub_mul],
                                end
    ... ≤ ∑ k : fin (n+1), abs ((f k/ₙ - f x) * bernstein n k x)
                              : finset.abs_sum_le_sum_abs
    ... = ∑ k : fin (n+1), abs (f k/ₙ - f x) * bernstein n k x
                              : by simp_rw [abs_mul, abs_eq_self.mpr bernstein_nonneg]
    ... = ∑ k in S, abs (f k/ₙ - f x) * bernstein n k x +
          ∑ k in Sᶜ, abs (f k/ₙ - f x) * bernstein n k x
                              : (S.sum_add_sum_compl _).symm
    -- We'll now deal with the terms in `S` and the terms in `Sᶜ` in separate calc blocks.
    ... < ε/2 + ε/2 : add_lt_add_of_le_of_lt _ _
    ... = ε : add_halves ε,
    { -- We now work on the terms in `S`: uniform continuity and `bernstein.probability`
      -- quickly give us a bound.
      calc ∑ k in S, abs (f k/ₙ - f x) * bernstein n k x
          ≤ ∑ k in S, (ε/2) * bernstein n k x
                                :  finset.sum_le_sum
                                    (λ k m, (mul_le_mul_of_nonneg_right (le_of_lt (lt_of_mem_S m))
                                      bernstein_nonneg))
      ... = (ε/2) * ∑ k in S, bernstein n k x
                                : by rw finset.mul_sum
      -- In this step we increase the sum of `S` back to a sum over all of `fin (n+1)`,
      -- so that we can use `bernstein.probability`.
      ... ≤ (ε/2) * ∑ k : fin (n+1), bernstein n k x
                                : mul_le_mul_of_nonneg_left
                                    (finset.sum_le_univ_sum_of_nonneg (λ k, bernstein_nonneg)) w₀
      ... = ε/2 : by rw [bernstein.probability, mul_one] },
      -- We now turn to working on `Sᶜ`: we control the difference term just using `∥f∥`,
      -- and then insert a `δ^(-2) * (x - k/n)^2` factor
      -- (which is at least one because we are not in `S`).
      calc ∑ k in Sᶜ, abs (f k/ₙ - f x) * bernstein n k x
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
                                        (mul_nonneg pow_minus_two_nonneg (pow_two_nonneg _))
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
                                    apply mul_unit_interval_le w₂,
                                    apply mul_unit_interval_le w₂ (le_refl _),
                                    all_goals { unit_interval, },
                                  end
      ... < ε/2 : _, -- We postpone this final step for a moment, in order to actually choose `n`!
  -- Choose `n` to make the inequality work.
  show ℕ, { exact nat_ceil (2 * (2 * ∥f∥ * δ^(-2 : ℤ)) / ε), },
  { -- And a final inequality bash gets us to the end.
    rw [lt_div_iff (show (0 : ℝ) < 2, by norm_num), mul_comm],
    rw [←mul_div_assoc, div_lt_iff npos, mul_comm ε, ←div_lt_iff h],
    replace nh : (N : ℝ) < (n : ℝ) := by exact_mod_cast nh,
    apply lt_of_le_of_lt (le_nat_ceil _) nh, },
end

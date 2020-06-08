/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.convex.specific_functions
import data.real.conjugate_exponents

/-!
# `L^p` distance on finite products of metric spaces

Given finitely many metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a real parameter `p ∈ [1, ∞)`, that also induce
the product topology. We will define them in this file.

For now, this file only contains the Hölder and Minkowski inequalities over finsets, which imply
the triangular inequality in finite `L^p` products.

## Main definitions and results

* The Hölder inequality over finite sets states that
  $$
  \left(\sum_i a_i b_i \right) \leq
    \left( \sum_i a_i^p\right)^{1/p} \cdot  \left(\sum_i b_i^q\right)^{1/q}
  $$
  when `p` and `q` are conjugate exponents. We prove it in `sum_rpow_holder_of_nonneg` when
  `a i` and `b i` are nonnegative reals, and we also give versions over `nnreal` and `ennreal`.
* The Minkowski inequality over finite sets states that
  $$
  \left(\sum_i (a_i + b_i)^p\right)^{1/p}
    \leq \left(\sum a_i^p\right)^{1/p} + \left(\sum b_i^p\right)^{1/p}
  $$
  when `p ≥ 1`. We prove it in `sum_rpow_minkowski_of_nonneg` when
  `a i` and `b i` are nonnegative reals, and we also give versions over `nnreal` and `ennreal`.

## Implementation notes

The Hölder and Minkowski inequalities have more general versions (for the integral over a general
measure space). This file only contains the finset version, which is the one needed to define finite
products of metric spaces. The finset version could be derived from the general version (which is
not formalized yet).
-/

open real set
open_locale big_operators uniformity topological_space

noncomputable theory

variables {ι : Type*}

namespace finset
/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with nonnegative functions. -/
theorem sum_rpow_holder_of_nonneg {s : finset ι} {f g : ι → ℝ} {p q : ℝ}
  (hpq : p.is_conjugate_exponent q) (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, 0 ≤ g x) :
  (∑ i in s, f i * g i) ≤ (∑ i in s, (f i)^p) ^ (1/p) * (∑ i in s, (g i)^q) ^ (1/q) :=
begin
  by_cases H : ∀ (i : ι), i ∈ s → g i = 0,
  { -- assume first that all `g i` vanish. Then the result is trivial.
    have A : (∑ i in s, f i * g i) = (∑ i in s, f i * 0),
    { apply finset.sum_congr rfl (λ x hx, _), simp [H x hx] },
    have B : (∑ i in s, (g i)^q) = (∑ i in s, 0),
    { apply finset.sum_congr rfl (λ x hx, _),
      simp [H x hx, zero_rpow hpq.symm.ne_zero] },
    simp [A, B, zero_rpow (inv_ne_zero hpq.symm.ne_zero)] },
  { /- Assume now that some `g i` is nonzero, so that the sum `S = ∑ i in s, (g i)^q` is nonzero.
    We will apply the convexity of the function `x ↦ x^p` to a suitable sum to get the result:
    write `a i = (g i)^q / S` (these coefficients add up to `1`). Then, by convexity,
    `(∑ a i * (f i * (g i)^(1-q))) ^ p ≤ (∑ a i * (f i * (g i)^(1-q)) ^ p)`. This is the desired
    inequality, up to trivial massaging, as the sum on the left is `(∑ f i * g i / S) ^ p` and the
    sum on the right is `(∑ (f i) ^ p) / S`. -/
    set S := (∑ i in s, (g i)^q) with hS,
    have S_ne : S ≠ 0,
    { assume Z,
      have : ∀ (i : ι), i ∈ s → 0 ≤ (g i)^q,
        by { assume i hi, exact rpow_nonneg_of_nonneg (hg i hi) _ },
      rw finset.sum_eq_zero_iff_of_nonneg this at Z,
      apply H,
      assume i hi,
      simpa [rpow_eq_zero_iff_of_nonneg (hg i hi), hpq.symm.ne_zero] using Z i hi },
    have S_pos : 0 < S,
    { have : 0 ≤ S := finset.sum_nonneg (λ i hi, rpow_nonneg_of_nonneg (hg i hi) _),
      exact lt_of_le_of_ne this (ne.symm S_ne) },
    set a := λ i, (g i)^q / S with ha,
    have fgS_nonneg : 0 ≤ ∑ (x : ι) in s, f x * g x / S :=
      finset.sum_nonneg (λ i hi, div_nonneg (mul_nonneg (hf i hi) (hg i hi)) S_pos),
    -- formulate the main convexity inequality, in a suitable form
    have main : (∑ i in s, f i * g i/S) ^ p ≤ (∑ i in s, (f i)^p) / S := calc
      (∑ i in s, f i * g i/S) ^ p
          = (∑ i in s, a i * (f i * (g i)^(1-q))) ^ p :
      begin
        congr' 1,
        apply finset.sum_congr rfl (λ i hi, _),
        have : q + (1-q) ≠ 0, by simp,
        have : g i = (g i)^q * (g i)^(1-q), by simp [← rpow_add' (hg i hi) this],
        conv_lhs { rw this },
        simp [ha],
        ring
      end
      ... ≤ (∑ i in s, a i * (f i * (g i)^(1-q))^p) :
      begin
        -- this is where something happens, i.e., we use convexity.
        apply (convex_on_rpow (le_of_lt hpq.one_lt)).map_sum_le,
        { assume i hi, exact div_nonneg (rpow_nonneg_of_nonneg (hg i hi) _) S_pos },
        { rw [ha, ← finset.sum_div, hS, div_self S_ne] },
        { assume i hi, exact mul_nonneg (hf i hi) (rpow_nonneg_of_nonneg (hg i hi) _) }
      end
      ... ≤ (∑ i in s, (f i)^p / S) :
      begin
        apply finset.sum_le_sum (λ i hi, _),
        calc a i * (f i * g i ^ (1 - q)) ^ p
            = a i * ((f i) ^ p * (g i)^ ((1-q) * p)) :
          by rw [mul_rpow (hf i hi) (rpow_nonneg_of_nonneg (hg i hi) _), ← rpow_mul (hg i hi)]
        ... = ((f i)^p / S) * ((g i)^q * (g i)^((1-q)*p)) : by { simp [ha], ring }
        ... ≤ (f i ^ p / S) * 1 :
        begin
          apply mul_le_mul_of_nonneg_left _ (div_nonneg (rpow_nonneg_of_nonneg (hf i hi) _) S_pos),
          have : q + (1 - q) * p = 0, by { field_simp [hpq.conj_eq, hpq.sub_one_ne_zero], ring },
          have : 1 = (g i) ^ (q + (1 - q) * p), by simp [this],
          conv_rhs { rw this },
          exact le_rpow_add (hg i hi) _ _,
        end
        ... = f i ^p / S : by rw [mul_one]
      end
      ... = (∑ i in s, (f i)^p) / S : by rw finset.sum_div,
    -- Now that we have proved the main inequality, deduce the result by putting the `S` factors
    -- in the right place.
    calc (∑ i in s, f i * g i)
      = S * ((∑ i in s, f i * g i/S) ^ p) ^ (1/p) :
      begin
        have : p * p⁻¹ = 1 := div_self hpq.ne_zero,
        simp only [← rpow_mul fgS_nonneg, this, one_div_eq_inv, rpow_one],
        rw [← finset.sum_div, mul_div_cancel' _ S_ne]
      end
      ... ≤ S * ((∑ i in s, (f i)^p) / S) ^ (1/p) :
      begin
        apply mul_le_mul_of_nonneg_left _ (le_of_lt S_pos),
        exact rpow_le_rpow (rpow_nonneg_of_nonneg fgS_nonneg _) main
          (div_nonneg zero_le_one (lt_trans zero_lt_one hpq.one_lt)),
      end
      ... = (∑ i in s, (f i)^p) ^ (1/p) * S ^ (1-1/p) :
      begin
        have : 0 ≤ ∑ (i : ι) in s, f i ^ p :=
          finset.sum_nonneg (λ i hi, rpow_nonneg_of_nonneg (hf i hi) _),
        simp only [sub_eq_add_neg, rpow_add S_pos, div_eq_inv_mul, mul_one, rpow_one],
        rw [mul_rpow (inv_nonneg.2 (le_of_lt S_pos)) this, ← rpow_neg_one,
            ← rpow_mul (le_of_lt S_pos)],
        simp only [neg_mul_eq_neg_mul_symm, one_mul],
        ring
      end
      ... = (∑ i in s, (f i)^p) ^ (1/p) * (∑ i in s, (g i)^q) ^ (1/q) :
        by rw sub_eq_of_eq_add' (eq.symm hpq.inv_add_inv_conj) }
end

/-- Minkowski inequality: the `L^p` norm satisfies the triangular inequality, i.e.,
`||f+g||_p ≤ ||f||_p + ||g||_p`. Version for sums over finite sets, with nonnegative functions. -/
theorem sum_rpow_minkowski_of_nonneg {s : finset ι} {f g : ι → ℝ} {p : ℝ}
  (hp : 1 ≤ p) (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, 0 ≤ g x) :
  (∑ i in s, (f i + g i) ^ p)^(1/p) ≤ (∑ i in s, (f i)^p) ^ (1/p) + (∑ i in s, (g i)^p) ^ (1/p) :=
begin
  -- The result is trivial when `p = 1`, so we can assume `1 < p`.
  rcases le_iff_eq_or_lt.1 hp with H|lt_p, { simp [← H, finset.sum_add_distrib] },
  let q := p.conjugate_exponent,
  have hpq : p.is_conjugate_exponent q := real.is_conjugate_exponent_conjugate_exponent lt_p,
  /- The trick is to start from the sum `S = ∑ i in s, (f i + g i) ^ p`, decompose the power as
  `f i * (f i + g i) ^ (p-1) + g i * (f i + g i) ^ (p-1)`, and apply Hölder inequality with the
  exponents `p` and `q` to each of the two resulting sums. As `(p-1) q = p`, this gives a bound
  involving the same sum `S`, but at the power `1/q`. Massaging this inequality gives the
  desired boud. -/
  set S := ∑ i in s, (f i + g i) ^ p with hS,
  have : 0 ≤ S :=
    finset.sum_nonneg (λ i hi, rpow_nonneg_of_nonneg (add_nonneg (hf i hi) (hg i hi)) _),
  rcases le_iff_eq_or_lt.1 this with H|S_pos,
  { /- The cancellation argument in the above sketch does not work when `S = 0`, so we first deal
    with this (trivial) case directly. -/
    simp only [← H, zero_rpow hpq.one_div_ne_zero],
    apply add_nonneg;
    refine rpow_nonneg_of_nonneg (finset.sum_nonneg (λ i hi, rpow_nonneg_of_nonneg _ _)) _,
    { exact hf i hi },
    { exact hg i hi } },
  { -- Assume now `0 < S`. We will flesh out the details of the above sketch.
    have S_eq : (∑ i in s, ((f i + g i)^(p-1))^q) = S,
    { apply finset.sum_congr rfl (λ i hi, _),
      rw ← rpow_mul (add_nonneg (hf i hi) (hg i hi)),
      congr' 1,
      field_simp [q, real.conjugate_exponent, hpq.sub_one_ne_zero],
      ring },
    have main : S^(1/p) * S^(1/q) ≤
         ((∑ i in s, (f i)^p) ^ (1/p) + (∑ i in s, (g i)^p) ^ (1/p)) * S ^ (1/q) := calc
      S^(1/p) * S^(1/q) = S :
        by rw [← rpow_add S_pos, hpq.inv_add_inv_conj, rpow_one]
      ... = (∑ i in s, f i * (f i + g i) ^ (p-1)) + (∑ i in s, g i * (f i + g i) ^ (p-1)) :
      begin
        have A : p = 1 + (p-1) := eq_add_of_sub_eq' rfl,
        have B : 1 + (p-1) ≠ 0, by { rw ← A, exact hpq.ne_zero },
        rw [← finset.sum_add_distrib, hS],
        apply finset.sum_congr rfl (λ i hi, _),
        conv_lhs { rw A },
        rw [← add_mul, rpow_add' (add_nonneg (hf i hi) (hg i hi)) B, rpow_one]
      end
      ... ≤ (∑ i in s, (f i)^p) ^ (1/p) * (∑ i in s, ((f i + g i)^(p-1))^q)^(1/q) +
            (∑ i in s, (g i)^p) ^ (1/p) * (∑ i in s, ((f i + g i)^(p-1))^q)^(1/q) :
      begin
        have A : ∀ i, i ∈ s → 0 ≤ (f i + g i)^(p-1) :=
          λ i hi, rpow_nonneg_of_nonneg (add_nonneg (hf i hi) (hg i hi)) _,
        apply add_le_add;
        apply finset.sum_rpow_holder_of_nonneg hpq (λ i hi, _) A,
        { exact hf i hi },
        { exact hg i hi }
      end
      ... = ((∑ i in s, (f i)^p) ^ (1/p) + (∑ i in s, (g i)^p) ^ (1/p)) * S ^ (1/q) :
        by rw [S_eq, add_mul],
    exact (mul_le_mul_right (rpow_pos_of_pos S_pos _)).mp main },
end

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `nnreal`-valued functions. -/
theorem sum_rpow_holder_nnreal {s : finset ι} {f g : ι → nnreal} {p q : ℝ}
  (hpq : p.is_conjugate_exponent q) :
  (∑ i in s, f i * g i) ≤ (∑ i in s, (f i)^p) ^ (1/p) * (∑ i in s, (g i)^q) ^ (1/q) :=
begin
  rw ← nnreal.coe_le_coe,
  have hf : ∀ i ∈ s, 0 ≤ (f i : ℝ) := λ i hi, nnreal.coe_nonneg (f i),
  have hg : ∀ i ∈ s, 0 ≤ (g i : ℝ) := λ i hi, nnreal.coe_nonneg (g i),
  exact_mod_cast sum_rpow_holder_of_nonneg hpq hf hg
end

/-- Minkowski inequality: the `L^p` norm satisfies the triangular inequality, i.e.,
`||f+g||_p ≤ ||f||_p + ||g||_p`. Version for sums over finite sets, with `nnreal`-valued
functions. -/
theorem sum_rpow_minkowski_nnreal {s : finset ι} {f g : ι → nnreal} {p : ℝ} (hp : 1 ≤ p) :
  (∑ i in s, (f i + g i) ^ p)^(1/p) ≤ (∑ i in s, (f i)^p) ^ (1/p) + (∑ i in s, (g i)^p) ^ (1/p) :=
begin
  rw ← nnreal.coe_le_coe,
  have hf : ∀ i ∈ s, 0 ≤ (f i : ℝ) := λ i hi, nnreal.coe_nonneg (f i),
  have hg : ∀ i ∈ s, 0 ≤ (g i : ℝ) := λ i hi, nnreal.coe_nonneg (g i),
  exact_mod_cast sum_rpow_minkowski_of_nonneg hp hf hg
end

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ennreal`-valued functions. -/
theorem sum_rpow_holder_ennreal {s : finset ι} {f g : ι → ennreal} {p q : ℝ}
  (hpq : p.is_conjugate_exponent q) :
  (∑ i in s, f i * g i) ≤ (∑ i in s, (f i)^p) ^ (1/p) * (∑ i in s, (g i)^q) ^ (1/q) :=
begin
  by_cases H : (∑ i in s, (f i)^p) ^ (1/p) = 0 ∨ (∑ i in s, (g i)^q) ^ (1/q) = 0,
  { replace H : (∀ i ∈ s, f i = 0) ∨ (∀ i ∈ s, g i = 0),
      by simpa [ennreal.rpow_eq_zero_iff, hpq.pos, hpq.symm.pos, asymm hpq.pos, asymm hpq.symm.pos,
                sum_eq_zero_iff_of_nonneg] using H,
    have : ∀ i ∈ s, f i * g i = 0 := λ i hi, by cases H; simp [H i hi],
    have : (∑ i in s, f i * g i) = (∑ i in s, 0) := sum_congr rfl this,
    simp [this] },
  push_neg at H,
  by_cases H' : (∑ i in s, (f i)^p) ^ (1/p) = ⊤ ∨ (∑ i in s, (g i)^q) ^ (1/q) = ⊤,
  { cases H'; simp [H', -one_div_eq_inv, H] },
  replace H' : (∀ i ∈ s, f i ≠ ⊤) ∧ (∀ i ∈ s, g i ≠ ⊤),
    by simpa [ennreal.rpow_eq_top_iff, asymm hpq.pos, asymm hpq.symm.pos, hpq.pos, hpq.symm.pos,
              ennreal.sum_eq_top_iff, not_or_distrib] using H',
  have := ennreal.coe_le_coe.2 (@sum_rpow_holder_nnreal _ s (λ i, ennreal.to_nnreal (f i))
              (λ i, ennreal.to_nnreal (g i)) _ _ hpq),
  push_cast [← ennreal.coe_rpow_of_nonneg, le_of_lt (hpq.pos), le_of_lt (hpq.one_div_pos),
             le_of_lt (hpq.symm.pos), le_of_lt (hpq.symm.one_div_pos)] at this,
  convert this using 1,
  { apply finset.sum_congr rfl (λ i hi, _), simp [H'.1 i hi, H'.2 i hi] },
  { congr' 2;
    apply finset.sum_congr rfl (λ i hi, _);
    simp [H'.1 i hi, H'.2 i hi] }
end

/-- Minkowski inequality: the `L^p` norm satisfies the triangular inequality, i.e.,
`||f+g||_p ≤ ||f||_p + ||g||_p`. Version for sums over finite sets, with `ennreal`-valued
functions. -/
theorem sum_rpow_minkowski_ennreal {s : finset ι} {f g : ι → ennreal} {p : ℝ} (hp : 1 ≤ p) :
  (∑ i in s, (f i + g i) ^ p)^(1/p) ≤ (∑ i in s, (f i)^p) ^ (1/p) + (∑ i in s, (g i)^p) ^ (1/p) :=
begin
  by_cases H' : (∑ i in s, (f i)^p) ^ (1/p) = ⊤ ∨ (∑ i in s, (g i)^p) ^ (1/p) = ⊤,
  { cases H'; simp [H', -one_div_eq_inv] },
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp,
  replace H' : (∀ i ∈ s, f i ≠ ⊤) ∧ (∀ i ∈ s, g i ≠ ⊤),
    by simpa [ennreal.rpow_eq_top_iff, asymm pos, pos, ennreal.sum_eq_top_iff,
              not_or_distrib] using H',
  have := ennreal.coe_le_coe.2 (@sum_rpow_minkowski_nnreal _ s (λ i, ennreal.to_nnreal (f i))
              (λ i, ennreal.to_nnreal (g i)) _  hp),
  push_cast [← ennreal.coe_rpow_of_nonneg, le_of_lt (pos), le_of_lt (one_div_pos_of_pos pos)] at this,
  convert this using 2,
  { apply finset.sum_congr rfl (λ i hi, _), simp [H'.1 i hi, H'.2 i hi] },
  repeat { congr' 1;
    apply finset.sum_congr rfl (λ i hi, _);
    simp [H'.1 i hi, H'.2 i hi] }
end

end finset

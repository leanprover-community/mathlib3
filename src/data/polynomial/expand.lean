/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ring_theory.polynomial.basic
import ring_theory.ideal.local_ring
import tactic.ring_exp

/-!
# Expand a polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `polynomial.expand R p f`: expand the polynomial `f` with coefficients in a
  commutative semiring `R` by a factor of p, so `expand R p (∑ aₙ xⁿ)` is `∑ aₙ xⁿᵖ`.
* `polynomial.contract p f`: the opposite of `expand`, so it sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`.

-/

universes u v w
open_locale classical big_operators polynomial
open finset

namespace polynomial

section comm_semiring

variables (R : Type u) [comm_semiring R] {S : Type v} [comm_semiring S] (p q : ℕ)

/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`. -/
noncomputable def expand : R[X] →ₐ[R] R[X] :=
{ commutes' := λ r, eval₂_C _ _,
  .. (eval₂_ring_hom C (X ^ p) : R[X] →+* R[X]) }

lemma coe_expand : (expand R p : R[X] → R[X]) = eval₂ C (X ^ p) := rfl

variables {R}

lemma expand_eq_sum {f : R[X]} :
  expand R p f = f.sum (λ e a, C a * (X ^ p) ^ e) :=
by { dsimp [expand, eval₂], refl, }

@[simp] lemma expand_C (r : R) : expand R p (C r) = C r := eval₂_C _ _
@[simp] lemma expand_X : expand R p X = X ^ p := eval₂_X _ _
@[simp] lemma expand_monomial (r : R) : expand R p (monomial q r) = monomial (q * p) r :=
by simp_rw [← smul_X_eq_monomial, alg_hom.map_smul, alg_hom.map_pow, expand_X, mul_comm, pow_mul]

theorem expand_expand (f : R[X]) : expand R p (expand R q f) = expand R (p * q) f :=
polynomial.induction_on f (λ r, by simp_rw expand_C)
  (λ f g ihf ihg, by simp_rw [alg_hom.map_add, ihf, ihg])
  (λ n r ih, by simp_rw [alg_hom.map_mul, expand_C, alg_hom.map_pow, expand_X,
    alg_hom.map_pow, expand_X, pow_mul])

theorem expand_mul (f : R[X]) : expand R (p * q) f = expand R p (expand R q f) :=
(expand_expand p q f).symm

@[simp] theorem expand_zero (f : R[X]) : expand R 0 f = C (eval 1 f) :=
by simp [expand]

@[simp] theorem expand_one (f : R[X]) : expand R 1 f = f :=
polynomial.induction_on f
  (λ r, by rw expand_C)
  (λ f g ihf ihg, by rw [alg_hom.map_add, ihf, ihg])
  (λ n r ih, by rw [alg_hom.map_mul, expand_C, alg_hom.map_pow, expand_X, pow_one])

theorem expand_pow (f : R[X]) : expand R (p ^ q) f = (expand R p ^[q] f) :=
nat.rec_on q (by rw [pow_zero, expand_one, function.iterate_zero, id]) $ λ n ih,
by rw [function.iterate_succ_apply', pow_succ, expand_mul, ih]

theorem derivative_expand (f : R[X]) :
  (expand R p f).derivative = expand R p f.derivative * (p * X ^ (p - 1)) :=
by rw [coe_expand, derivative_eval₂_C, derivative_pow, C_eq_nat_cast, derivative_X, mul_one]

theorem coeff_expand {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
  (expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0 :=
begin
  simp only [expand_eq_sum],
  simp_rw [coeff_sum, ← pow_mul, C_mul_X_pow_eq_monomial, coeff_monomial, sum],
  split_ifs with h,
  { rw [finset.sum_eq_single (n/p), nat.mul_div_cancel' h, if_pos rfl],
    { intros b hb1 hb2, rw if_neg, intro hb3, apply hb2, rw [← hb3, nat.mul_div_cancel_left b hp] },
    { intro hn, rw not_mem_support_iff.1 hn, split_ifs; refl } },
  { rw finset.sum_eq_zero, intros k hk, rw if_neg, exact λ hkn, h ⟨k, hkn.symm⟩, },
end

@[simp] theorem coeff_expand_mul {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
  (expand R p f).coeff (n * p) = f.coeff n :=
by rw [coeff_expand hp, if_pos (dvd_mul_left _ _), nat.mul_div_cancel _ hp]

@[simp] theorem coeff_expand_mul' {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
  (expand R p f).coeff (p * n) = f.coeff n :=
by rw [mul_comm, coeff_expand_mul hp]

/-- Expansion is injective. -/
lemma expand_injective {n : ℕ} (hn : 0 < n) : function.injective (expand R n) :=
λ g g' H, ext $ λ k, by rw [← coeff_expand_mul hn, H, coeff_expand_mul hn]

theorem expand_inj {p : ℕ} (hp : 0 < p) {f g : R[X]} :
  expand R p f = expand R p g ↔ f = g :=
(expand_injective hp).eq_iff

theorem expand_eq_zero {p : ℕ} (hp : 0 < p) {f : R[X]} : expand R p f = 0 ↔ f = 0 :=
(expand_injective hp).eq_iff' (map_zero _)

theorem expand_ne_zero {p : ℕ} (hp : 0 < p) {f : R[X]} : expand R p f ≠ 0 ↔ f ≠ 0 :=
(expand_eq_zero hp).not

theorem expand_eq_C {p : ℕ} (hp : 0 < p) {f : R[X]} {r : R} :
  expand R p f = C r ↔ f = C r :=
by rw [← expand_C, expand_inj hp, expand_C]

theorem nat_degree_expand (p : ℕ) (f : R[X]) :
  (expand R p f).nat_degree = f.nat_degree * p :=
begin
  cases p.eq_zero_or_pos with hp hp,
  { rw [hp, coe_expand, pow_zero, mul_zero, ← C_1, eval₂_hom, nat_degree_C] },
  by_cases hf : f = 0,
  { rw [hf, alg_hom.map_zero, nat_degree_zero, zero_mul] },
  have hf1 : expand R p f ≠ 0 := mt (expand_eq_zero hp).1 hf,
  rw [← with_bot.coe_eq_coe, ← degree_eq_nat_degree hf1],
  refine le_antisymm ((degree_le_iff_coeff_zero _ _).2 $ λ n hn, _) _,
  { rw coeff_expand hp, split_ifs with hpn,
    { rw coeff_eq_zero_of_nat_degree_lt, contrapose! hn,
      rw [with_bot.coe_le_coe, ← nat.div_mul_cancel hpn], exact nat.mul_le_mul_right p hn },
    { refl } },
  { refine le_degree_of_ne_zero _,
    rw [coeff_expand_mul hp, ← leading_coeff], exact mt leading_coeff_eq_zero.1 hf }
end

lemma monic.expand {p : ℕ} {f : R[X]} (hp : 0 < p) (h : f.monic) : (expand R p f).monic :=
begin
  rw [monic.def, leading_coeff, nat_degree_expand, coeff_expand hp],
  simp [hp, h],
end

theorem map_expand {p : ℕ} {f : R →+* S} {q : R[X]} :
  map f (expand R p q) = expand S p (map f q) :=
begin
  by_cases hp : p = 0,
  { simp [hp] },
  ext,
  rw [coeff_map, coeff_expand (nat.pos_of_ne_zero hp), coeff_expand (nat.pos_of_ne_zero hp)],
  split_ifs; simp,
end

@[simp]
lemma expand_eval (p : ℕ) (P : R[X]) (r : R) : eval r (expand R p P) = eval (r ^ p) P :=
begin
  refine polynomial.induction_on P (λ a, by simp) (λ f g hf hg, _) (λ n a h, by simp),
  rw [alg_hom.map_add, eval_add, eval_add, hf, hg]
end

@[simp]
lemma expand_aeval {A : Type*} [semiring A] [algebra R A] (p : ℕ) (P : R[X]) (r : A) :
  aeval r (expand R p P) = aeval (r ^ p) P :=
begin
  refine polynomial.induction_on P (λ a, by simp) (λ f g hf hg, _) (λ n a h, by simp),
  rw [alg_hom.map_add, aeval_add, aeval_add, hf, hg]
end

/-- The opposite of `expand`: sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`. -/
noncomputable def contract (p : ℕ) (f : R[X]) : R[X] :=
∑ n in range (f.nat_degree + 1), monomial n (f.coeff (n * p))

theorem coeff_contract {p : ℕ} (hp : p ≠ 0) (f : R[X]) (n : ℕ) :
  (contract p f).coeff n = f.coeff (n * p) :=
begin
  simp only [contract, coeff_monomial, sum_ite_eq', finset_sum_coeff, mem_range, not_lt,
    ite_eq_left_iff],
  assume hn,
  apply (coeff_eq_zero_of_nat_degree_lt _).symm,
  calc f.nat_degree < f.nat_degree + 1 : nat.lt_succ_self _
    ... ≤ n * 1 : by simpa only [mul_one] using hn
    ... ≤ n * p : mul_le_mul_of_nonneg_left (show 1 ≤ p, from hp.bot_lt) (zero_le n)
end

theorem contract_expand {f : R[X]} (hp : p ≠ 0) : contract p (expand R p f) = f :=
begin
  ext,
  simp [coeff_contract hp, coeff_expand hp.bot_lt, nat.mul_div_cancel _ hp.bot_lt]
end

section char_p

variable [char_p R p]

theorem expand_contract [no_zero_divisors R] {f : R[X]} (hf : f.derivative = 0)
  (hp : p ≠ 0) : expand R p (contract p f) = f :=
begin
  ext n,
  rw [coeff_expand hp.bot_lt, coeff_contract hp],
  split_ifs with h,
  { rw nat.div_mul_cancel h },
  { cases n,
    { exact absurd (dvd_zero p) h },
    have := coeff_derivative f n,
    rw [hf, coeff_zero, zero_eq_mul] at this,
    cases this,
    { rw this },
    rw [← nat.cast_succ, char_p.cast_eq_zero_iff R p] at this,
    exact absurd this h }
end

variable [hp : fact p.prime]
include hp

theorem expand_char (f : R[X]) : map (frobenius R p) (expand R p f) = f ^ p :=
begin
  refine f.induction_on' (λ a b ha hb, _) (λ n a, _),
  { rw [alg_hom.map_add, polynomial.map_add, ha, hb, add_pow_char], },
  { rw [expand_monomial, map_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
        mul_pow, ← C.map_pow, frobenius_def],
    ring_exp }
end

theorem map_expand_pow_char (f : R[X]) (n : ℕ) :
   map ((frobenius R p) ^ n) (expand R (p ^ n) f) = f ^ (p ^ n) :=
begin
  induction n,
  { simp [ring_hom.one_def] },
  symmetry,
  rw [pow_succ', pow_mul, ← n_ih, ← expand_char, pow_succ, ring_hom.mul_def,
      ← map_map, mul_comm, expand_mul, ← map_expand]
end

end char_p

end comm_semiring

section is_domain

variables (R : Type u) [comm_ring R] [is_domain R]

theorem is_local_ring_hom_expand {p : ℕ} (hp : 0 < p) :
  is_local_ring_hom (↑(expand R p) : R[X] →+* R[X]) :=
begin
  refine ⟨λ f hf1, _⟩, rw ← coe_fn_coe_base at hf1,
  have hf2 := eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf1),
  rw [coeff_expand hp, if_pos (dvd_zero _), p.zero_div] at hf2,
  rw [hf2, is_unit_C] at hf1, rw expand_eq_C hp at hf2, rwa [hf2, is_unit_C]
end

variable {R}

theorem of_irreducible_expand {p : ℕ} (hp : p ≠ 0) {f : R[X]}
  (hf : irreducible (expand R p f)) : irreducible f :=
let _ := is_local_ring_hom_expand R hp.bot_lt in by exactI of_irreducible_map ↑(expand R p) hf

theorem of_irreducible_expand_pow {p : ℕ} (hp : p ≠ 0) {f : R[X]} {n : ℕ} :
  irreducible (expand R (p ^ n) f) → irreducible f :=
nat.rec_on n (λ hf, by rwa [pow_zero, expand_one] at hf) $ λ n ih hf,
ih $ of_irreducible_expand hp $ by { rw pow_succ at hf, rwa [expand_expand] }

end is_domain

end polynomial

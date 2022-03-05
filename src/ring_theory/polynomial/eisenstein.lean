/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import ring_theory.eisenstein_criterion
import ring_theory.integrally_closed
import ring_theory.norm

/-!
# Eisenstein polynomials
Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]` is
*Eisenstein at `𝓟`* if `f.leading_coeff ∉ 𝓟`, `∀ n, n < f.nat_degree → f.coeff n ∈ 𝓟` and
`f.coeff 0 ∉ 𝓟 ^ 2`. In this file we gather miscellaneous results about Eisenstein polynomials.

## Main definitions
* `polynomial.is_eisenstein_at f 𝓟`: the property of being Eisenstein at `𝓟`.

## Main results
* `polynomial.is_eisenstein_at.irreducible`: if a primitive `f` satisfies `f.is_eisenstein_at 𝓟`,
  where `𝓟.is_prime`, then `f` is irreducible.

## Implementation details
We also define a notion `is_weakly_eisenstein_at` requiring only that
`∀ n < f.nat_degree → f.coeff n ∈ 𝓟`. This makes certain results slightly more general and it is
useful since it is sometimes better behaved (for example it is stable under `polynomial.map`).

-/

universes u v w z

variables {R : Type u}

open ideal algebra finset

open_locale big_operators polynomial

namespace polynomial

/-- Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]`
is *weakly Eisenstein at `𝓟`* if `∀ n, n < f.nat_degree → f.coeff n ∈ 𝓟`. -/
@[mk_iff] structure is_weakly_eisenstein_at [comm_semiring R] (f : R[X]) (𝓟 : ideal R) :
  Prop := (mem : ∀ {n}, n < f.nat_degree → f.coeff n ∈ 𝓟)

/-- Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]`
is *Eisenstein at `𝓟`* if `f.leading_coeff ∉ 𝓟`, `∀ n, n < f.nat_degree → f.coeff n ∈ 𝓟` and
`f.coeff 0 ∉ 𝓟 ^ 2`. -/
@[mk_iff] structure is_eisenstein_at [comm_semiring R] (f : R[X]) (𝓟 : ideal R) : Prop :=
(leading : f.leading_coeff ∉ 𝓟)
(mem : ∀ {n}, n < f.nat_degree → f.coeff n ∈ 𝓟)
(not_mem : f.coeff 0 ∉ 𝓟 ^ 2)

namespace is_weakly_eisenstein_at

section comm_semiring

variables [comm_semiring R] {𝓟 : ideal R} {f : R[X]} (hf : f.is_weakly_eisenstein_at 𝓟)

include hf

lemma map {A : Type v} [comm_ring A] (φ : R →+* A) : (f.map φ).is_weakly_eisenstein_at (𝓟.map φ) :=
begin
  refine (is_weakly_eisenstein_at_iff _ _).2 (λ n hn, _),
  rw [coeff_map],
  exact mem_map_of_mem _ (hf.mem (lt_of_lt_of_le hn (nat_degree_map_le _ _)))
end

end comm_semiring

section comm_ring

variables [comm_ring R] {𝓟 : ideal R} {f : R[X]} (hf : f.is_weakly_eisenstein_at 𝓟)
variables {S : Type v} [comm_ring S] [algebra R S]

section principal

variable {p : R}

local notation `P` := submodule.span R {p}

lemma exists_mem_adjoin_mul_eq_pow_nat_degree {x : S} (hx : aeval x f = 0)
  (hmo : f.monic) (hf : f.is_weakly_eisenstein_at P) : ∃ y ∈ adjoin R ({x} : set S),
  (algebra_map R S) p * y = x ^ (f.map (algebra_map R S)).nat_degree :=
begin
  rw [aeval_def, polynomial.eval₂_eq_eval_map, eval_eq_finset_sum, range_add_one,
    sum_insert not_mem_range_self, sum_range, (monic_map
    (algebra_map R S) hmo).coeff_nat_degree, one_mul] at hx,
  replace hx := eq_neg_of_add_eq_zero hx,
  have : ∀ n < f.nat_degree, p ∣ f.coeff n,
  { intros n hn,
    refine mem_span_singleton.1 (by simpa using hf.mem hn) },
  choose! φ hφ using this,
  conv_rhs at hx { congr, congr, skip, funext,
    rw [fin.coe_eq_val, coeff_map, hφ i.1 (lt_of_lt_of_le i.2 (nat_degree_map_le _ _)),
      ring_hom.map_mul, mul_assoc] },
  rw [hx, ← mul_sum, neg_eq_neg_one_mul, ← mul_assoc (-1 : S), mul_comm (-1 : S), mul_assoc],
  refine ⟨-1 * ∑ (i : fin (f.map (algebra_map R S)).nat_degree),
    (algebra_map R S) (φ i.1) * x ^ i.1, _, rfl⟩,
  exact subalgebra.mul_mem _ (subalgebra.neg_mem _ (subalgebra.one_mem _))
    (subalgebra.sum_mem _ (λ i hi, subalgebra.mul_mem _ (subalgebra.algebra_map_mem _ _)
    (subalgebra.pow_mem _ (subset_adjoin (set.mem_singleton x)) _)))
end

lemma exists_mem_adjoin_mul_eq_pow_nat_degree_le {x : S} (hx : aeval x f = 0)
  (hmo : f.monic) (hf : f.is_weakly_eisenstein_at P) :
  ∀ i, (f.map (algebra_map R S)).nat_degree ≤ i →
  ∃ y ∈ adjoin R ({x} : set S), (algebra_map R S) p * y = x ^ i :=
begin
  intros i hi,
  obtain ⟨k, hk⟩ := le_iff_exists_add.1 hi,
  rw [hk, pow_add],
  obtain ⟨y, hy, H⟩ := exists_mem_adjoin_mul_eq_pow_nat_degree hx hmo hf,
  refine ⟨y * x ^ k, _, _⟩,
  { exact subalgebra.mul_mem _ hy (subalgebra.pow_mem _  (subset_adjoin (set.mem_singleton x)) _) },
  { rw [← mul_assoc _ y, H] }
end

end principal

include hf

lemma pow_nat_degree_le_of_root_of_monic_mem {x : R} (hroot : is_root f x) (hmo : f.monic) :
  ∀ i, f.nat_degree ≤ i → x ^ i ∈ 𝓟 :=
begin
  intros i hi,
  obtain ⟨k, hk⟩ := le_iff_exists_add.1 hi,
  rw [hk, pow_add],
  suffices : x ^ f.nat_degree ∈ 𝓟,
  { exact mul_mem_right (x ^ k) 𝓟 this },
  rw [is_root.def, eval_eq_finset_sum, finset.range_add_one, finset.sum_insert
    finset.not_mem_range_self, finset.sum_range, hmo.coeff_nat_degree, one_mul] at hroot,
  rw [eq_neg_of_add_eq_zero hroot, neg_mem_iff],
  refine submodule.sum_mem _ (λ i hi,  mul_mem_right _ _ (hf.mem (fin.is_lt i)))
end

lemma pow_nat_degree_le_of_aeval_zero_of_monic_mem_map {x : S} (hx : aeval x f = 0)
  (hmo : f.monic) :
  ∀ i, (f.map (algebra_map R S)).nat_degree ≤ i → x ^ i ∈ 𝓟.map (algebra_map R S) :=
begin
  suffices : x ^ (f.map (algebra_map R S)).nat_degree ∈ 𝓟.map (algebra_map R S),
  { intros i hi,
    obtain ⟨k, hk⟩ := le_iff_exists_add.1 hi,
    rw [hk, pow_add],
    refine mul_mem_right _ _ this },
  rw [aeval_def, eval₂_eq_eval_map, ← is_root.def] at hx,
  refine pow_nat_degree_le_of_root_of_monic_mem (hf.map _) hx (monic_map _ hmo) _ rfl.le
end

end comm_ring

end is_weakly_eisenstein_at

namespace is_eisenstein_at

section comm_semiring

variables [comm_semiring R] {𝓟 : ideal R} {f : R[X]} (hf : f.is_eisenstein_at 𝓟)

include hf

lemma is_weakly_eisenstein_at : is_weakly_eisenstein_at f 𝓟 := ⟨hf.mem⟩

lemma coeff_mem {n : ℕ} (hn : n ≠ f.nat_degree) : f.coeff n ∈ 𝓟 :=
begin
  cases ne_iff_lt_or_gt.1 hn,
  { exact hf.mem h },
  { rw [coeff_eq_zero_of_nat_degree_lt h],
    exact ideal.zero_mem _}
end

end comm_semiring

section is_domain

variables [comm_ring R] [is_domain R] {𝓟 : ideal R} {f : R[X]} (hf : f.is_eisenstein_at 𝓟)

/-- If a primitive `f` satisfies `f.is_eisenstein_at 𝓟`, where `𝓟.is_prime`, then `f` is
irreducible. -/
lemma irreducible (hprime : 𝓟.is_prime) (hu : f.is_primitive)
  (hfd0 : 0 < f.nat_degree) : irreducible f :=
irreducible_of_eisenstein_criterion hprime hf.leading (λ n hn, hf.mem (coe_lt_degree.1 hn))
  (nat_degree_pos_iff_degree_pos.1 hfd0) hf.not_mem hu

end is_domain

end is_eisenstein_at

end polynomial

section is_integral

variables {K : Type v} {L : Type z} {p : R} [comm_ring R] [field K] [field L]
variables [algebra K L] [algebra R L] [algebra R K] [is_scalar_tower R K L] [is_separable K L]
variables [is_domain R] [normalized_gcd_monoid R] [is_fraction_ring R K] [is_integrally_closed R]

local notation `𝓟` := submodule.span R {p}

open is_integrally_closed power_basis nat polynomial is_scalar_tower

/-- Let `K` be the field of fraction of an integrally closed domain `R` and let `L` be a separable
extension of `K`, generated by an integral power basis `B` such that the minimal polynomial of
`B.gen` is Eisenstein. Given `z : L` integral over `R`, if `Q : polynomial R` is such that
`aeval B.gen Q = p • z`, then `p ∣ Q.coeff 0`. -/
lemma dvd_coeff_zero_of_aeval_eq_prime_smul_of_minpoly_is_eiseinstein_at {B : power_basis K L}
  (hp : prime p) (hei : (minpoly R B.gen).is_eisenstein_at 𝓟) (hBint : is_integral R B.gen) {z : L}
  {Q : polynomial R} (hQ : aeval B.gen Q = p • z) (hzint : is_integral R z) :
  p ∣ Q.coeff 0 :=
begin
  -- First define some abbreviations.
  letI := B.finite_dimensional,
  let P := minpoly R B.gen,
  obtain ⟨n , hn⟩ := nat.exists_eq_succ_of_ne_zero B.dim_pos.ne',
  have finrank_K_L : finite_dimensional.finrank K L = B.dim := B.finrank,
  have deg_K_P : (minpoly K B.gen).nat_degree = B.dim := B.nat_degree_minpoly,
  have deg_R_P : P.nat_degree = B.dim,
  { rw [← deg_K_P, minpoly.gcd_domain_eq_field_fractions K hBint,
        nat_degree_map_of_monic (minpoly.monic hBint) (algebra_map R K)] },
  choose! f hf using hei.is_weakly_eisenstein_at.exists_mem_adjoin_mul_eq_pow_nat_degree_le
    (minpoly.aeval R B.gen) (minpoly.monic hBint),
  simp only [nat_degree_map_of_monic (minpoly.monic hBint), deg_R_P] at hf,

  -- The Eisenstein condition shows that `p` divides `Q.coeff 0`
  -- if `p^n` divides the following multiple of `Q^n`:
  suffices : p ^ n.succ ∣
    (Q.coeff 0 ^ n.succ * ((-1) ^ (n.succ * n) * (minpoly R B.gen).coeff 0 ^ n)),
  { have hndiv : ¬ p ^ 2 ∣ ((minpoly R B.gen)).coeff 0 := λ h,
      hei.not_mem ((span_singleton_pow p 2).symm ▸ (ideal.mem_span_singleton.2 h)),
    refine prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd hp ((_ : _ ^ n.succ ∣ _)) hndiv,
    convert (is_unit.dvd_mul_right ⟨(-1) ^ (n.succ * n), rfl⟩).mpr this using 1,
    push_cast,
    ring_nf, simp [pow_right_comm _ _ 2] },

  -- We claim the quotient of `Q^n * _` by `p^n` is the following `r`:
  have aux : ∀ i ∈ (range (Q.nat_degree + 1)).erase 0, B.dim ≤ i + n,
  { intros i hi,
    simp only [mem_range, mem_erase] at hi,
    rw [hn],
    exact le_add_pred_of_pos _ hi.1 },
  have hintsum : is_integral R (z * B.gen ^ n -
    ∑ (x : ℕ) in (range (Q.nat_degree + 1)).erase 0, Q.coeff x • f (x + n)),
  { refine is_integral_sub (is_integral_mul hzint (is_integral.pow hBint _))
      (is_integral.sum _ (λ i hi, (is_integral_smul _ _))),
    exact adjoin_le_integral_closure hBint (hf _ (aux i hi)).1 },
  obtain ⟨r, hr⟩ := is_integral_iff.1 (is_integral_norm K hintsum),
  use r,

  -- Do the computation in `K` so we can work in terms of `z` instead of `r`.
  apply is_fraction_ring.injective R K,
  simp only [_root_.map_mul, _root_.map_pow, _root_.map_neg, _root_.map_one],
  -- Both sides are actually norms:
  calc _ = norm K (Q.coeff 0 • B.gen ^ n) : _
  ... = norm K (p • (z * B.gen ^ n) - ∑ (x : ℕ) in (range (Q.nat_degree + 1)).erase 0,
          p • Q.coeff x • f (x + n))
    : congr_arg (norm K) (eq_sub_of_add_eq _)
  ... = _ : _,
  { simp only [algebra.smul_def, algebra_map_apply R K L, norm_algebra_map, _root_.map_mul,
      _root_.map_pow, finrank_K_L, power_basis.norm_gen_eq_coeff_zero_minpoly,
      minpoly.gcd_domain_eq_field_fractions K hBint, coeff_map, ← hn],
    ring_exp },
  swap, { simp_rw [← smul_sum, ← smul_sub, algebra.smul_def p, algebra_map_apply R K L,
      _root_.map_mul, norm_algebra_map, finrank_K_L, hr, ← hn] },

  calc _ = (Q.coeff 0 • 1 + ∑ (x : ℕ) in (range (Q.nat_degree + 1)).erase 0,
              Q.coeff x • B.gen ^ x) * B.gen ^ n : _
  ... = (Q.coeff 0 • B.gen ^ 0 + ∑ (x : ℕ) in (range (Q.nat_degree + 1)).erase 0,
              Q.coeff x • B.gen ^ x) * B.gen ^ n : by rw pow_zero
  ... = (aeval B.gen Q) * B.gen ^ n : _
  ... = _ : by rw [hQ, algebra.smul_mul_assoc],
  { have : ∀ i ∈ (range (Q.nat_degree + 1)).erase 0,
      Q.coeff i • (B.gen ^ i * B.gen ^ n) =
      p • Q.coeff i • f (i + n),
    { intros i hi,
      rw [← pow_add, ← (hf _ (aux i hi)).2, ← smul_def, smul_smul, mul_comm _ p, smul_smul] },
    simp only [add_mul, smul_mul_assoc, one_mul, sum_mul, sum_congr rfl this] },
  { rw [aeval_eq_sum_range,
        finset.add_sum_erase (range (Q.nat_degree + 1)) (λ i, Q.coeff i • B.gen ^ i)],
    simp },
end

end is_integral

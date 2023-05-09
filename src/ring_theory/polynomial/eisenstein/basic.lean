/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import ring_theory.eisenstein_criterion
import ring_theory.polynomial.scale_roots

/-!
# Eisenstein polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
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
  rw [aeval_def, polynomial.eval₂_eq_eval_map, eval_eq_sum_range, range_add_one,
    sum_insert not_mem_range_self, sum_range, (hmo.map
    (algebra_map R S)).coeff_nat_degree, one_mul] at hx,
  replace hx := eq_neg_of_add_eq_zero_left hx,
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
  obtain ⟨k, hk⟩ := exists_add_of_le hi,
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
  obtain ⟨k, hk⟩ := exists_add_of_le hi,
  rw [hk, pow_add],
  suffices : x ^ f.nat_degree ∈ 𝓟,
  { exact mul_mem_right (x ^ k) 𝓟 this },
  rw [is_root.def, eval_eq_sum_range, finset.range_add_one, finset.sum_insert
    finset.not_mem_range_self, finset.sum_range, hmo.coeff_nat_degree, one_mul] at hroot,
  rw [eq_neg_of_add_eq_zero_left hroot, neg_mem_iff],
  refine submodule.sum_mem _ (λ i hi,  mul_mem_right _ _ (hf.mem (fin.is_lt i)))
end

lemma pow_nat_degree_le_of_aeval_zero_of_monic_mem_map {x : S} (hx : aeval x f = 0)
  (hmo : f.monic) :
  ∀ i, (f.map (algebra_map R S)).nat_degree ≤ i → x ^ i ∈ 𝓟.map (algebra_map R S) :=
begin
  suffices : x ^ (f.map (algebra_map R S)).nat_degree ∈ 𝓟.map (algebra_map R S),
  { intros i hi,
    obtain ⟨k, hk⟩ := exists_add_of_le hi,
    rw [hk, pow_add],
    refine mul_mem_right _ _ this },
  rw [aeval_def, eval₂_eq_eval_map, ← is_root.def] at hx,
  refine pow_nat_degree_le_of_root_of_monic_mem (hf.map _) hx (hmo.map _) _ rfl.le
end

end comm_ring

end is_weakly_eisenstein_at

section scale_roots

variables {A : Type*} [comm_ring R] [comm_ring A]

lemma scale_roots.is_weakly_eisenstein_at (p : R[X]) {x : R}
  {P : ideal R} (hP : x ∈ P) : (scale_roots p x).is_weakly_eisenstein_at P :=
begin
  refine ⟨λ i hi, _⟩,
  rw coeff_scale_roots,
  rw [nat_degree_scale_roots, ← tsub_pos_iff_lt] at hi,
  exact ideal.mul_mem_left _ _ (ideal.pow_mem_of_mem P hP _ hi)
end

lemma dvd_pow_nat_degree_of_eval₂_eq_zero {f : R →+* A}
  (hf : function.injective f) {p : R[X]} (hp : p.monic) (x y : R) (z : A)
  (h : p.eval₂ f z = 0) (hz : f x * z = f y) : x ∣ y ^ p.nat_degree :=
begin
  rw [← nat_degree_scale_roots p x, ← ideal.mem_span_singleton],
  refine (scale_roots.is_weakly_eisenstein_at _ (ideal.mem_span_singleton.mpr $ dvd_refl x))
    .pow_nat_degree_le_of_root_of_monic_mem _ ((monic_scale_roots_iff x).mpr hp) _ le_rfl,
  rw injective_iff_map_eq_zero' at hf,
  have := scale_roots_eval₂_eq_zero f h,
  rwa [hz, polynomial.eval₂_at_apply, hf] at this
end

lemma dvd_pow_nat_degree_of_aeval_eq_zero [algebra R A] [nontrivial A]
  [no_zero_smul_divisors R A] {p : R[X]} (hp : p.monic) (x y : R) (z : A)
  (h : polynomial.aeval z p = 0) (hz : z * algebra_map R A x = algebra_map R A y) :
  x ∣ y ^ p.nat_degree :=
dvd_pow_nat_degree_of_eval₂_eq_zero (no_zero_smul_divisors.algebra_map_injective R A)
  hp x y z h ((mul_comm _ _).trans hz)

end scale_roots

namespace is_eisenstein_at

section comm_semiring

variables [comm_semiring R] {𝓟 : ideal R} {f : R[X]} (hf : f.is_eisenstein_at 𝓟)

lemma _root_.polynomial.monic.leading_coeff_not_mem (hf : f.monic) (h : 𝓟 ≠ ⊤) :
  ¬f.leading_coeff ∈ 𝓟 :=
hf.leading_coeff.symm ▸ (ideal.ne_top_iff_one _).1 h

lemma _root_.polynomial.monic.is_eisenstein_at_of_mem_of_not_mem (hf : f.monic) (h : 𝓟 ≠ ⊤)
  (hmem : ∀ {n}, n < f.nat_degree → f.coeff n ∈ 𝓟) (hnot_mem : f.coeff 0 ∉ 𝓟 ^ 2) :
  f.is_eisenstein_at 𝓟 :=
{ leading := hf.leading_coeff_not_mem h,
  mem := λ n hn, hmem hn,
  not_mem := hnot_mem }

include hf

lemma is_weakly_eisenstein_at : is_weakly_eisenstein_at f 𝓟 := ⟨λ _, hf.mem⟩

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

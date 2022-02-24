/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Best, Riccardo Brasca, Eric Rodriguez
-/

import algebra.is_prime_pow
import number_theory.cyclotomic.basic
import ring_theory.adjoin.power_basis
import ring_theory.polynomial.cyclotomic.eval
import ring_theory.norm

/-!
# Primitive roots in cyclotomic fields
If `is_cyclotomic_extension {n} A B`, we define an element `zeta n A B : B` that is (under certain
assumptions) a primitive `n`-root of unity in `B` and we study its properties. We also prove related
theorems under the more general assumption of just being a primitive root, for reasons described
in the implementation details section.

## Main definitions
* `is_cyclotomic_extension.zeta n A B`: if `is_cyclotomic_extension {n} A B`, than `zeta n A B`
  is an element of `B` that plays the role of a primitive `n`-th root of unity.
* `is_primitive_root.power_basis`: if `K` and `L` are fields such that
  `is_cyclotomic_extension {n} K L` and `ne_zero (↑n : K)`, then `is_primitive_root.power_basis`
  gives a K-power basis for L given a primitive root `ζ`.
* `is_primitive_root.embeddings_equiv_primitive_roots`: the equivalence between `L →ₐ[K] A`
  and `primitive_roots n A` given by the choice of `ζ`.

## Main results
* `is_cyclotomic_extension.zeta_primitive_root`: if `is_domain B` and `ne_zero (↑n : B)`, then
  `zeta n A B` is a primitive `n`-th root of unity.
* `is_cyclotomic_extension.finrank`: if `irreducible (cyclotomic n K)` (in particular for
  `K = ℚ`), then the `finrank` of a cyclotomic extension is `n.totient`.
* `is_primitive_root.norm_eq_one`: If `K` is linearly ordered (in particular for `K = ℚ`), the norm
  of a primitive root is `1` if `n` is odd.
* `is_primitive_root.sub_one_norm_eq_eval_cyclotomic`: if `irreducible (cyclotomic n K)`
  (in particular for `K = ℚ`), then the norm of `ζ - 1` is `eval 1 (cyclotomic n ℤ)`, for a
  primitive root ζ. We also prove the analogous of this result for `zeta`.
* `is_primitive_root.prime_ne_two_pow.sub_one_norm` : if `irreducible (cyclotomic (p ^ (k + 1)) K)`
  (in particular for `K = ℚ`) and `p` is an odd prime, then the norm of `ζ - 1` is `p`. We also
  prove the analogous of this result for `zeta`.
  gives a K-power basis for L given a primitive root `ζ`.
* `is_primitive_root.embeddings_equiv_primitive_roots`: the equivalence between `L →ₐ[K] A`
  and `primitive_roots n A` given by the choice of `ζ`.

## Implementation details
`zeta n A B` is defined as any root of `cyclotomic n A` in `B`, that exists because of
`is_cyclotomic_extension {n} A B`. It is not true in general that it is a primitive `n`-th root of
unity, but this holds if `is_domain B` and `ne_zero (↑n : B)`.

`zeta n A B` is defined using `exists.some`, which means we cannot control it.
For example, in normal mathematics, we can demand that `(zeta p ℤ ℤ[ζₚ] : ℚ(ζₚ))` is equal to
`zeta p ℚ ℚ(ζₚ)`, as we are just choosing "an arbitrary primitive root" and we can internally
specify that our choices agree. This is not the case here, and it is indeed impossible to prove that
these two are equal. Therefore, whenever possible, we prove our results for any primitive root,
and only at the "final step", when we need to provide an "explicit" primitive root, we use `zeta`.

-/

open polynomial algebra finset finite_dimensional is_cyclotomic_extension nat pnat


universes u v w z

variables {n : ℕ+} (A : Type w) (B : Type z) (K : Type u) {L : Type v} (C : Type w)
variables [comm_ring A] [comm_ring B] [algebra A B] [is_cyclotomic_extension {n} A B]

section zeta

namespace is_cyclotomic_extension

variables (n)

/-- If `B` is a `n`-th cyclotomic extension of `A`, then `zeta n A B` is any root of
`cyclotomic n A` in L. -/
noncomputable def zeta : B :=
  (exists_root $ set.mem_singleton n : ∃ r : B, aeval r (cyclotomic n A) = 0).some

@[simp] lemma zeta_spec : aeval (zeta n A B) (cyclotomic n A) = 0 :=
classical.some_spec (exists_root (set.mem_singleton n) : ∃ r : B, aeval r (cyclotomic n A) = 0)

lemma zeta_spec' : is_root (cyclotomic n B) (zeta n A B) :=
by { convert zeta_spec n A B, rw [is_root.def, aeval_def, eval₂_eq_eval_map, map_cyclotomic] }

lemma zeta_pow : (zeta n A B) ^ (n : ℕ) = 1 :=
is_root_of_unity_of_root_cyclotomic (nat.mem_divisors_self _ n.pos.ne') (zeta_spec' _ _ _)

/-- If `is_domain B` and `ne_zero (↑n : B)` then `zeta n A B` is a primitive `n`-th root of
unity. -/
lemma zeta_primitive_root [is_domain B] [ne_zero ((n : ℕ) : B)] :
  is_primitive_root (zeta n A B) n :=
by { rw ←is_root_cyclotomic_iff, exact zeta_spec' n A B }

end is_cyclotomic_extension

end zeta

section no_order

variables [field K] [field L] [comm_ring C] [algebra K L] [algebra K C]
          [is_cyclotomic_extension {n} K L]
          {ζ : L} (hζ : is_primitive_root ζ n)

namespace is_primitive_root

/-- The `power_basis` given by a primitive root `ζ`. -/
@[simps] noncomputable def power_basis : power_basis K L :=
power_basis.map (algebra.adjoin.power_basis $ integral {n} K L ζ) $
(subalgebra.equiv_of_eq _ _ (is_cyclotomic_extension.adjoin_primitive_root_eq_top n _ hζ)).trans
top_equiv

variables {K}

/-- The equivalence between `L →ₐ[K] A` and `primitive_roots n A` given by a primitive root `ζ`. -/
@[simps] noncomputable def embeddings_equiv_primitive_roots [is_domain C] [ne_zero ((n : ℕ) : K)]
  (hirr : irreducible (cyclotomic n K)) : (L →ₐ[K] C) ≃ primitive_roots n C :=
((hζ.power_basis K).lift_equiv).trans
{ to_fun    := λ x,
  begin
    haveI hn := ne_zero.of_no_zero_smul_divisors K C n,
    refine ⟨x.1, _⟩,
    cases x,
    rwa [mem_primitive_roots n.pos, ←is_root_cyclotomic_iff, is_root.def,
         ←map_cyclotomic _ (algebra_map K C), hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
         ←eval₂_eq_eval_map, ←aeval_def]
  end,
  inv_fun   := λ x,
  begin
    haveI hn := ne_zero.of_no_zero_smul_divisors K C n,
    refine ⟨x.1, _⟩,
    cases x,
    rwa [aeval_def, eval₂_eq_eval_map, hζ.power_basis_gen K,
         ←hζ.minpoly_eq_cyclotomic_of_irreducible hirr, map_cyclotomic, ←is_root.def,
         is_root_cyclotomic_iff, ← mem_primitive_roots n.pos]
  end,
  left_inv  := λ x, subtype.ext rfl,
  right_inv := λ x, subtype.ext rfl }

end is_primitive_root

namespace is_cyclotomic_extension

variables {K} (L)

/-- If `irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the `finrank` of a
cyclotomic extension is `n.totient`. -/
lemma finrank (hirr : irreducible (cyclotomic n K)) [ne_zero ((n : ℕ) : K)] :
  finrank K L = (n : ℕ).totient :=
begin
  haveI := ne_zero.of_no_zero_smul_divisors K L n,
  rw [((zeta_primitive_root n K L).power_basis K).finrank, is_primitive_root.power_basis_dim,
      ←(zeta_primitive_root n K L).minpoly_eq_cyclotomic_of_irreducible hirr, nat_degree_cyclotomic]
end

end is_cyclotomic_extension

end no_order

section norm

namespace is_primitive_root

variables [field L] {ζ : L} (hζ : is_primitive_root ζ n)

include hζ

/-- If `K` is linearly ordered (in particular for `K = ℚ`), the norm of a primitive root is `1`
if `n` is odd. -/
lemma norm_eq_one [linear_ordered_field K] [algebra K L] (hodd : odd (n : ℕ)) : norm K ζ = 1 :=
begin
  haveI := ne_zero.of_no_zero_smul_divisors K L n,
  have hz := congr_arg (norm K) ((is_primitive_root.iff_def _ n).1 hζ).1,
  rw [←(algebra_map K L).map_one , norm_algebra_map, one_pow, map_pow, ←one_pow ↑n] at hz,
  exact strict_mono.injective hodd.strict_mono_pow hz
end

variables {K} [field K] [algebra K L] [ne_zero ((n : ℕ) : K)]

/-- If `irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the norm of
`ζ - 1` is `eval 1 (cyclotomic n ℤ)`. -/
lemma sub_one_norm_eq_eval_cyclotomic [is_cyclotomic_extension {n} K L]
  (h : 2 < (n : ℕ)) (hirr : irreducible (cyclotomic n K)) :
  norm K (ζ - 1) = ↑(eval 1 (cyclotomic n ℤ)) :=
begin
  let E := algebraic_closure L,
  obtain ⟨z, hz⟩ := is_alg_closed.exists_root _ (degree_cyclotomic_pos n E n.pos).ne.symm,
  apply (algebra_map K E).injective,
  letI := finite_dimensional {n} K L,
  letI := is_galois n K L,
  rw [norm_eq_prod_embeddings],
  conv_lhs { congr, skip, funext,
    rw [← neg_sub, alg_hom.map_neg, alg_hom.map_sub, alg_hom.map_one, neg_eq_neg_one_mul] },
  rw [prod_mul_distrib, prod_const, card_univ, alg_hom.card, is_cyclotomic_extension.finrank L hirr,
      neg_one_pow_of_even (totient_even h), one_mul],
  have : univ.prod (λ (σ : L →ₐ[K] E), 1 - σ ζ) = eval 1 (cyclotomic' n E),
  { rw [cyclotomic', eval_prod, ← @finset.prod_attach E E, ← univ_eq_attach],
    refine fintype.prod_equiv (hζ.embeddings_equiv_primitive_roots E hirr) _ _ (λ σ, _),
    simp },
  haveI : ne_zero ((n : ℕ) : E) := (ne_zero.of_no_zero_smul_divisors K _ (n : ℕ)),
  rw [this, cyclotomic', ← cyclotomic_eq_prod_X_sub_primitive_roots (is_root_cyclotomic_iff.1 hz),
      ← map_cyclotomic_int, (algebra_map K E).map_int_cast, ←int.cast_one, eval_int_cast_map,
      ring_hom.eq_int_cast, int.cast_id]
end

/-- If `is_prime_pow (n : ℕ)`, `n ≠ 2` and `irreducible (cyclotomic n K)` (in particular for
`K = ℚ`), then the norm of `ζ - 1` is `(n : ℕ).min_fac`. -/
lemma sub_one_norm_is_prime_pow (hn : is_prime_pow (n : ℕ)) [is_cyclotomic_extension {n} K L]
  (hirr : irreducible (cyclotomic (n : ℕ) K)) (h : n ≠ 2) :
  norm K (ζ - 1) = (n : ℕ).min_fac :=
begin
  have := (coe_lt_coe 2 _).1 (lt_of_le_of_ne (succ_le_of_lt (is_prime_pow.one_lt hn))
    (function.injective.ne pnat.coe_injective h).symm),
  letI hprime : fact ((n : ℕ).min_fac.prime) := ⟨min_fac_prime (is_prime_pow.ne_one hn)⟩,
  rw [sub_one_norm_eq_eval_cyclotomic hζ this hirr],
  nth_rewrite 0 [← is_prime_pow.min_fac_pow_factorization_eq hn],
  obtain ⟨k, hk⟩ : ∃ k, ((n : ℕ).factorization) (n : ℕ).min_fac = k + 1 :=
    exists_eq_succ_of_ne_zero (((n : ℕ).factorization.mem_support_to_fun (n : ℕ).min_fac).1 $
      factor_iff_mem_factorization.2 $ (mem_factors (is_prime_pow.ne_zero hn)).2
        ⟨hprime.out, min_fac_dvd _⟩),
  simp [hk, sub_one_norm_eq_eval_cyclotomic hζ this hirr],
end

omit hζ

/-- If `irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is an odd
prime, then the norm of `ζ - 1` is `p`. -/
lemma prime_ne_two_pow_sub_one_norm {p : ℕ+} [ne_zero ((p : ℕ) : K)] {k : ℕ}
  (hζ : is_primitive_root ζ ↑(p ^ (k + 1))) [hpri : fact (p : ℕ).prime]
  [is_cyclotomic_extension {p ^ (k + 1)} K L]
  (hirr : irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) (h : p ≠ 2) :
  norm K (ζ - 1) = p :=
begin
  haveI : ne_zero ((↑(p ^ (k + 1)) : ℕ) : K),
  { refine ⟨λ hzero, _⟩,
    rw [pow_coe] at hzero,
    simpa [ne_zero.ne ((p : ℕ) : K)] using hzero },
  have : 2 < p ^ (k + 1),
  { rw [← coe_lt_coe, pow_coe, pnat.coe_bit0, one_coe],
    calc 2 < (p : ℕ) : lt_of_le_of_ne hpri.1.two_le (by contrapose! h; exact coe_injective h.symm)
      ...  = (p : ℕ) ^ 1 : (pow_one _).symm
      ...  ≤ (p : ℕ) ^ (k + 1) : pow_le_pow (nat.prime.pos hpri.out) le_add_self },
  simp [sub_one_norm_eq_eval_cyclotomic hζ this hirr]
end

/-- If `irreducible (cyclotomic p K)` (in particular for `K = ℚ`) and `p` is an odd prime,
then the norm of `ζ - 1` is `p`. -/
lemma sub_one_norm_prime {p : ℕ+} [ne_zero ((p : ℕ) : K)] [hpri : fact (p : ℕ).prime]
  [hcyc : is_cyclotomic_extension {p} K L] (hζ: is_primitive_root ζ p)
  (hirr : irreducible (cyclotomic p K)) (h : p ≠ 2) :
  norm K (ζ - 1) = p :=
begin
  replace hirr : irreducible (cyclotomic (↑(p ^ (0 + 1)) : ℕ) K) := by simp [hirr],
  replace hζ : is_primitive_root ζ (↑(p ^ (0 + 1)) : ℕ) := by simp [hζ],
  haveI : ne_zero ((↑(p ^ (0 + 1)) : ℕ) : K) := ⟨by simp [ne_zero.ne ((p : ℕ) : K)]⟩,
  haveI : is_cyclotomic_extension {p ^ (0 + 1)} K L := by simp [hcyc],
  simpa using prime_ne_two_pow_sub_one_norm hζ hirr h
end

/-- If `irreducible (cyclotomic (2 ^ k) K)` (in particular for `K = ℚ`) and `k` is at least `2`,
then the norm of `ζ - 1` is `2`. -/
lemma sub_one_norm_pow_two [ne_zero (2 : K)] {k : ℕ} (hζ : is_primitive_root ζ (2 ^ k)) (hk : 2 ≤ k)
  [is_cyclotomic_extension {2 ^ k} K L] (hirr : irreducible (cyclotomic (2 ^ k) K)) :
  norm K (ζ - 1) = 2 :=
begin
  haveI : ne_zero (((2 ^ k : ℕ+) : ℕ) : K),
  { refine ⟨λ hzero, _⟩,
    rw [pow_coe, pnat.coe_bit0, one_coe, cast_pow, cast_bit0, cast_one,
      pow_eq_zero_iff (lt_of_lt_of_le zero_lt_two hk)] at hzero,
    exact (ne_zero.ne (2 : K)) hzero,
    apply_instance },
  have : 2 < (2 ^ k : ℕ+),
  { simp only [← coe_lt_coe, pnat.coe_bit0, one_coe, pow_coe],
    nth_rewrite 0 [← pow_one 2],
    exact pow_lt_pow one_lt_two (lt_of_lt_of_le one_lt_two hk) },
  replace hirr : irreducible (cyclotomic (2 ^ k : ℕ+) K) := by simp [hirr],
  replace hζ : is_primitive_root ζ (2 ^ k : ℕ+) := by simp [hζ],
  obtain ⟨k₁, hk₁⟩ := exists_eq_succ_of_ne_zero ((lt_of_lt_of_le zero_lt_two hk).ne.symm),
  simpa [hk₁] using sub_one_norm_eq_eval_cyclotomic hζ this hirr,
end

end is_primitive_root

namespace is_cyclotomic_extension

open is_primitive_root

/-- If `K` is linearly ordered (in particular for `K = ℚ`), the norm of `zeta n K L` is `1`
if `n` is odd. -/
lemma norm_zeta_eq_one (K : Type u) [linear_ordered_field K] (L : Type v) [field L] [algebra K L]
  [is_cyclotomic_extension {n} K L] (hodd : odd (n : ℕ)) : norm K (zeta n K L) = 1 :=
begin
  haveI := ne_zero.of_no_zero_smul_divisors K L n,
  exact norm_eq_one K (zeta_primitive_root n K L) hodd,
end

variables {K} (L) [field K] [field L] [algebra K L] [ne_zero ((n : ℕ) : K)]

/-- If `is_prime_pow (n : ℕ)`, `n ≠ 2` and `irreducible (cyclotomic n K)` (in particular for
`K = ℚ`), then the norm of `zeta n K L - 1` is `(n : ℕ).min_fac`. -/
lemma is_prime_pow_norm_zeta_sub_one (hn : is_prime_pow (n : ℕ))
  [is_cyclotomic_extension {n} K L]
  (hirr : irreducible (cyclotomic (n : ℕ) K)) (h : n ≠ 2) :
  norm K (zeta n K L - 1) = (n : ℕ).min_fac :=
begin
  haveI := ne_zero.of_no_zero_smul_divisors K L n,
  exact sub_one_norm_is_prime_pow (zeta_primitive_root n K L) hn hirr h,
end

/-- If `irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is an odd
prime, then the norm of `zeta (p ^ (k + 1)) K L - 1` is `p`. -/
lemma prime_ne_two_pow_norm_zeta_sub_one {p : ℕ+} [ne_zero ((p : ℕ) : K)] (k : ℕ)
  [hpri : fact (p : ℕ).prime]
  [is_cyclotomic_extension {p ^ (k + 1)} K L]
  (hirr : irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) (h : p ≠ 2) :
  norm K (zeta (p ^ (k + 1)) K L - 1) = p :=
begin
  haveI := ne_zero.of_no_zero_smul_divisors K L p,
  haveI : ne_zero ((↑(p ^ (k + 1)) : ℕ) : L),
  { refine ⟨λ hzero, _⟩,
    rw [pow_coe] at hzero,
    simpa [ne_zero.ne ((p : ℕ) : L)] using hzero },
  exact prime_ne_two_pow_sub_one_norm (zeta_primitive_root _ K L) hirr h,
end

/-- If `irreducible (cyclotomic p K)` (in particular for `K = ℚ`) and `p` is an odd prime,
then the norm of `zeta p K L - 1` is `p`. -/
lemma prime_ne_two_norm_zeta_sub_one {p : ℕ+} [ne_zero ((p : ℕ) : K)] [hpri : fact (p : ℕ).prime]
  [hcyc : is_cyclotomic_extension {p} K L] (hirr : irreducible (cyclotomic p K)) (h : p ≠ 2) :
  norm K (zeta p K L - 1) = p :=
begin
  haveI := ne_zero.of_no_zero_smul_divisors K L p,
  exact sub_one_norm_prime (zeta_primitive_root _ K L) hirr h,
end

/-- If `irreducible (cyclotomic (2 ^ k) K)` (in particular for `K = ℚ`) and `k` is at least `2`,
then the norm of `zeta (2 ^ k) K L - 1` is `2`. -/
lemma two_pow_norm_zeta_sub_one [ne_zero (2 : K)] {k : ℕ} (hk : 2 ≤ k)
  [is_cyclotomic_extension {2 ^ k} K L] (hirr : irreducible (cyclotomic (2 ^ k) K)) :
  norm K (zeta (2 ^ k) K L - 1) = 2 :=
begin
  haveI : ne_zero (((2 ^ k : ℕ+) : ℕ) : L),
  { refine ⟨λ hzero, _⟩,
    rw [pow_coe, pnat.coe_bit0, one_coe, cast_pow, cast_bit0, cast_one, pow_eq_zero_iff
      (lt_of_lt_of_le zero_lt_two hk), show (2 : L) = algebra_map K L 2, by simp,
      show (0 : L) = algebra_map K L 0, by simp] at hzero,
    exact (ne_zero.ne (2 : K)) ((algebra_map K L).injective hzero),
    apply_instance },
  refine sub_one_norm_pow_two _ hk hirr,
  simpa using zeta_primitive_root (2 ^ k) K L,
end

end is_cyclotomic_extension

end norm

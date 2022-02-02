/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Best, Riccardo Brasca, Eric Rodriguez
-/

import number_theory.cyclotomic.basic
import ring_theory.polynomial.cyclotomic.eval
import ring_theory.adjoin.power_basis
import ring_theory.norm

/-!
# `ζ` elements in cyclotmic fields
If `is_cyclotomic_extension {n} A B`, we define an element `zeta n A B : B` that is (under certain
assumptions) a primitive `n`-root of unity in `B` and we study its properties.

## Main definitions
* `is_cyclotomic_extension.zeta n A B` : if `is_cyclotomic_extension {n} A B`, than `zeta n A B`
  is an element of `B` that plays the role of a primitive `n`-th root of unity.
* `is_cyclotomic_extension.zeta.power_basis` : if `K` and `L` are fields such that
  `is_cyclotomic_extension {n} K L` and `ne_zero (↑n : K)`, then `zeta.power_basis` is the
  power basis given by `zeta n K L`.
* `is_cyclotomic_extension.zeta.embeddings_equiv_primitive_roots` : the equiv between `L →ₐ[K] A`
  and `primitive_roots n A` given by the choice of `zeta`.

## Main results
* `is_cyclotomic_extension.zeta_primitive_root` : if `is_domain B` and `ne_zero (↑n : B)` then
  `zeta n A B` is a primitive `n`-th root of unity.
* `is_cyclotomic_extension.finrank` : if `irreducible (cyclotomic n K)` (in particular for
  `K = ℚ`), then the `finrank` of a cyclotomic extension is `n.totient`.
* `is_cyclotomic_extension.norm_zeta_sub_one_eq_eval_cyclotomic` : if `irreducible (cyclotomic n K)`
  (in particular for `K = ℚ`), then the norm of `zeta n K L - 1` is `eval 1 (cyclotomic n ℤ)`.
* `is_cyclotomic_extension.prime_ne_two_pow.norm_zeta_sub_one` : if
  `irreducible (cyclotomic (p ^ k) K)` (in particular for `K = ℚ`) and `p` is an odd prime,
  then the norm of `zeta (p  ^ k) K L - 1` is `p`.

## Implementation details
`zeta n A B` is defined as any root of `cyclotomic n A` in `B`, that exists because of
`is_cyclotomic_extension {n} A B`. It is not true in general that it is a primitive `n`-th root of
unity, but this holds if `is_domain B` and `ne_zero (↑n : B)`.

-/

noncomputable theory

open polynomial algebra finset finite_dimensional

universes u v w z

variables (n : ℕ+) (A : Type w) (B : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B] [is_cyclotomic_extension {n} A B]

namespace is_cyclotomic_extension

/-- If `B` is a `n`-th cyclotomic extension of `A`, then `zeta n A B` is any root of
`cyclotomic n A` in L. -/
def zeta : B := (exists_root (set.mem_singleton n) : ∃ r : B, aeval r (cyclotomic n A) = 0).some

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

section field

variables {K : Type u} (L : Type v) (C : Type w)
variables [field K] [field L] [comm_ring C] [algebra K L] [algebra K C]
variables [is_cyclotomic_extension {n} K L] [ne_zero ((n : ℕ) : K)]

/-- If `irreducible (cyclotomic n K)`, then the minimal polynomial of `zeta n K A` is
`cyclotomic n K`. -/
lemma zeta_minpoly {n : ℕ+} (hirr : irreducible (cyclotomic n K)) [is_cyclotomic_extension {n} K C]
  [nontrivial C] : minpoly K (zeta n K C) = cyclotomic n K :=
(minpoly.eq_of_irreducible_of_monic hirr (zeta_spec _ _ _) (cyclotomic.monic n K)).symm

include n

variable (K)

/-- The `power_basis` given by `zeta n K L`. -/
@[simps] def zeta.power_basis : power_basis K L :=
begin
  haveI := ne_zero.of_no_zero_smul_divisors K L n,
  refine power_basis.map
    (algebra.adjoin.power_basis $ integral {n} K L $ zeta n K L) _,
  exact (subalgebra.equiv_of_eq _ _
      (is_cyclotomic_extension.adjoin_primitive_root_eq_top n _ $ zeta_primitive_root n K L)).trans
      top_equiv
end

variables {K} {n}

lemma zeta.power_basis_gen_minpoly (hirr : irreducible (cyclotomic n K)) :
  minpoly K (zeta.power_basis n K L).gen = cyclotomic n K :=
begin
  rw [zeta.power_basis_gen],
  exact zeta_minpoly L hirr
end

/-- If `irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the `finrank` of a
cyclotomic extension is `n.totient`. -/
lemma finrank (hirr : irreducible (cyclotomic n K)) : finrank K L = (n : ℕ).totient :=
begin
  rw [power_basis.finrank (zeta.power_basis n K L), zeta.power_basis_dim, ← zeta.power_basis_gen,
    zeta.power_basis_gen_minpoly L hirr, nat_degree_cyclotomic]
end

/-- `zeta.embeddings_equiv_primitive_roots` is the equiv between `L →ₐ[K] A` and
  `primitive_roots n A` given by the choice of `zeta`. -/
@[simps]
def zeta.embeddings_equiv_primitive_roots [is_domain C] (hirr : irreducible (cyclotomic n K)) :
  (L →ₐ[K] C) ≃ primitive_roots n C :=
((zeta.power_basis n K L).lift_equiv).trans
{ to_fun    := λ x,
  begin
    haveI hn := ne_zero.of_no_zero_smul_divisors K C n,
    refine ⟨x.1, _⟩,
    cases x,
    rwa [mem_primitive_roots n.pos, ←is_root_cyclotomic_iff, is_root.def,
      ← map_cyclotomic _ (algebra_map K C), ← zeta.power_basis_gen_minpoly L hirr,
      ← eval₂_eq_eval_map, ← aeval_def]
  end,
  inv_fun   := λ x,
  begin
    haveI hn := ne_zero.of_no_zero_smul_divisors K C n,
    refine ⟨x.1, _⟩,
    cases x,
    rwa [aeval_def, eval₂_eq_eval_map, zeta.power_basis_gen_minpoly L hirr, map_cyclotomic,
      ← is_root.def, is_root_cyclotomic_iff, ← mem_primitive_roots n.pos],
  end,
  left_inv  := λ x, subtype.ext rfl,
  right_inv := λ x, subtype.ext rfl }

/-- If `K` is linearly ordered (in particular for `K = ℚ`), the norm of `zeta n K L` is `1`
if `n` is odd. -/
lemma norm_zeta_eq_one (K : Type u) [linear_ordered_field K] (L : Type v) [field L] [algebra K L]
  [is_cyclotomic_extension {n} K L] (hodd : odd (n : ℕ)) : norm K (zeta n K L) = 1 :=
begin
  haveI := ne_zero.of_no_zero_smul_divisors K L n,
  have hz := congr_arg (norm K) ((is_primitive_root.iff_def _ n).1 (zeta_primitive_root n K L)).1,
  rw [← ring_hom.map_one (algebra_map K L), norm_algebra_map, one_pow, monoid_hom.map_pow,
    ← one_pow ↑n] at hz,
  exact strict_mono.injective hodd.strict_mono_pow hz
end

/-- If `irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the norm of
`zeta n K L - 1` is `eval 1 (cyclotomic n ℤ)`. -/
lemma norm_zeta_sub_one_eq_eval_cyclotomic (hirr : irreducible (cyclotomic n K)) (h : 2 < (n : ℕ)) :
  norm K (zeta n K L - 1) = ↑(eval 1 (cyclotomic n ℤ)) :=
begin
  let E := algebraic_closure L,
  obtain ⟨z, hz⟩ := is_alg_closed.exists_root _ (degree_cyclotomic_pos n E n.pos).ne.symm,
  apply (algebra_map K E).injective,
  letI := finite_dimensional {n} K L,
  letI := is_galois n K L,
  rw [norm_eq_prod_embeddings],
  conv_lhs { congr, skip, funext,
    rw [← neg_sub, alg_hom.map_neg, alg_hom.map_sub, alg_hom.map_one, neg_eq_neg_one_mul] },
  rw [prod_mul_distrib, prod_const, card_univ, alg_hom.card, finrank L hirr,
    nat.neg_one_pow_of_even (nat.totient_even h), one_mul],
  have : univ.prod (λ (σ : L →ₐ[K] E), 1 - σ (zeta n K L)) = eval 1 (cyclotomic' n E),
  { rw [cyclotomic', eval_prod, ← @finset.prod_attach E E, ← univ_eq_attach],
    refine fintype.prod_equiv (zeta.embeddings_equiv_primitive_roots L E hirr) _ _ (λ σ, _),
    simp },
  haveI : ne_zero ((n : ℕ) : E) := (ne_zero.of_no_zero_smul_divisors K _ (n : ℕ)),
  rw [this, cyclotomic', ← cyclotomic_eq_prod_X_sub_primitive_roots (is_root_cyclotomic_iff.1 hz),
      ← map_cyclotomic_int, (algebra_map K E).map_int_cast, ←int.cast_one, eval_int_cast_map,
      ring_hom.eq_int_cast, int.cast_id]
end

omit n

/-- If `irreducible (cyclotomic (p ^ k) K)` (in particular for `K = ℚ`) and `p` is an odd prime,
then the norm of `zeta (p  ^ k) K L - 1` is `p`. -/
lemma prime_ne_two_pow.norm_zeta_sub_one {p : ℕ+} {K : Type u} (L : Type v) [field K] [field L]
  [ne_zero ((p : ℕ) : K)] (k : ℕ) [hpri : fact (p : ℕ).prime] [algebra K L]
  [is_cyclotomic_extension {p ^ (k + 1)} K L]
  (hirr : irreducible (cyclotomic ((↑(p ^ (k + 1)) : ℕ)) K)) (h : p ≠ 2) :
  norm K ((zeta (p ^ (k + 1)) K L) - 1) = p :=
begin
  haveI : ne_zero ((↑(p ^ (k + 1)) : ℕ) : K),
  { refine ⟨λ hzero, _⟩,
    rw [pnat.pow_coe] at hzero,
    simpa [ne_zero.ne ((p : ℕ) : K)] using hzero },
  have : 2 < p ^ (k + 1),
  { rw [← pnat.coe_lt_coe, pnat.pow_coe, pnat.coe_bit0, pnat.one_coe],
    have := lt_of_le_of_ne hpri.1.two_le (by contrapose! h; exact pnat.coe_injective h.symm),
    refine lt_of_lt_of_le this _,
    nth_rewrite 0 [← pow_one ↑p],
    refine pow_le_pow (nat.one_le_of_lt this) le_add_self },
  simp [norm_zeta_sub_one_eq_eval_cyclotomic L hirr this]
end

/-- If `irreducible (cyclotomic p K)` (in particular for `K = ℚ`) and `p` is an odd prime,
then the norm of `zeta p K L - 1` is `p`. -/
lemma prime_ne_two.norm_zeta_sub_one {p : ℕ+} {K : Type u} (L : Type v) [field K] [field L]
  [ne_zero ((p : ℕ) : K)] [hpri : fact (p : ℕ).prime] [algebra K L]
  [hcyc : is_cyclotomic_extension {p} K L] (hirr : irreducible (cyclotomic p K)) (h : p ≠ 2) :
  norm K ((zeta p K L) - 1) = p :=
begin
  replace hirr : irreducible (cyclotomic ((↑(p ^ (0 + 1)) : ℕ)) K) := by simp [hirr],
  haveI : ne_zero ((↑(p ^ (0 + 1)) : ℕ) : K) := ⟨by simp [ne_zero.ne ((p : ℕ) : K)]⟩,
  haveI : is_cyclotomic_extension {p ^ (0 + 1)} K L := by simp [hcyc],
  simpa using prime_ne_two_pow.norm_zeta_sub_one L 0 hirr h
end

/-- If `irreducible (cyclotomic (2 ^ k) K)` (in particular for `K = ℚ`) and `k` is at least `2`,
then the norm of `zeta (2  ^ k) K L - 1` is `2`. -/
lemma two_pow.norm_zeta_sub_one {K : Type u} (L : Type v) [field K] [field L]
  [ne_zero (2 : K)] {k : ℕ} (hk : 2 ≤ k) [algebra K L] [is_cyclotomic_extension {2 ^ k} K L]
  (hirr : irreducible (cyclotomic (2 ^ k) K)) :
  norm K ((zeta (2 ^ k) K L) - 1) = 2 :=
begin
  haveI : ne_zero (((2 ^ k : ℕ+) : ℕ) : K),
  { refine ⟨λ hzero, _⟩,
    rw [pnat.pow_coe, pnat.coe_bit0, pnat.one_coe, nat.cast_pow, nat.cast_bit0, nat.cast_one,
      pow_eq_zero_iff (lt_of_lt_of_le zero_lt_two hk)] at hzero,
    exact (ne_zero.ne (2 : K)) hzero,
    apply_instance },
  have : 2 < (2 ^ k : ℕ+),
  { simp only [← pnat.coe_lt_coe, pnat.coe_bit0, pnat.one_coe, pnat.pow_coe],
    nth_rewrite 0 [← pow_one 2],
    refine pow_lt_pow one_lt_two (lt_of_lt_of_le one_lt_two hk) },
  replace hirr : irreducible (cyclotomic ((2 ^ k : ℕ+)) K) := by simp [hirr],
  obtain ⟨k₁, hk₁⟩ := nat.exists_eq_succ_of_ne_zero ((lt_of_lt_of_le zero_lt_two hk).ne.symm),
  simpa [hk₁] using norm_zeta_sub_one_eq_eval_cyclotomic L hirr this,
end

end field

end is_cyclotomic_extension

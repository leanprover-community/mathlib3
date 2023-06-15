/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import ring_theory.adjoin.basic
import ring_theory.power_basis
import linear_algebra.matrix.basis

/-!
# Power basis for `algebra.adjoin R {x}`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the canonical power basis on `algebra.adjoin R {x}`,
where `x` is an integral element over `R`.
-/


variables {K S : Type*} [field K] [comm_ring S] [algebra K S]

namespace algebra

open polynomial
open power_basis

open_locale big_operators

/-- The elements `1, x, ..., x ^ (d - 1)` for a basis for the `K`-module `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable def adjoin.power_basis_aux {x : S} (hx : is_integral K x) :
  basis (fin (minpoly K x).nat_degree) K (adjoin K ({x} : set S)) :=
begin
  have hST : function.injective (algebra_map (adjoin K ({x} : set S)) S) := subtype.coe_injective,
  have hx' : is_integral K
    (show adjoin K ({x} : set S), from ⟨x, subset_adjoin (set.mem_singleton x)⟩),
  { apply (is_integral_algebra_map_iff hST).mp,
    convert hx,
    apply_instance },
  have minpoly_eq := minpoly.eq_of_algebra_map_eq hST hx' rfl,
  apply @basis.mk (fin (minpoly K x).nat_degree) _
    (adjoin K {x}) (λ i, ⟨x, subset_adjoin (set.mem_singleton x)⟩ ^ (i : ℕ)),
  { have := linear_independent_pow _,
    rwa minpoly_eq at this },
  { rintros ⟨y, hy⟩ _,
    have := hx'.mem_span_pow,
    rw minpoly_eq at this,
    apply this,
    { rw [adjoin_singleton_eq_range_aeval] at hy,
      obtain ⟨f, rfl⟩ := (aeval x).mem_range.mp hy,
      use f,
      ext,
      exact aeval_algebra_map_apply S (⟨x, _⟩ : adjoin K {x}) _, } }
end

/-- The power basis `1, x, ..., x ^ (d - 1)` for `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. See `algebra.adjoin.power_basis'` for
a version over a more general base ring. -/
@[simps gen dim] noncomputable def adjoin.power_basis {x : S} (hx : is_integral K x) :
  power_basis K (adjoin K ({x} : set S)) :=
{ gen := ⟨x, subset_adjoin (set.mem_singleton x)⟩,
  dim := (minpoly K x).nat_degree,
  basis := adjoin.power_basis_aux hx,
  basis_eq_pow := basis.mk_apply _ _ }

end algebra

open algebra

/-- The power basis given by `x` if `B.gen ∈ adjoin K {x}`. See `power_basis.of_gen_mem_adjoin'`
for a version over a more general base ring. -/
@[simps] noncomputable def power_basis.of_gen_mem_adjoin {x : S} (B : power_basis K S)
  (hint : is_integral K x) (hx : B.gen ∈ adjoin K ({x} : set S)) : power_basis K S :=
(algebra.adjoin.power_basis hint).map $
  (subalgebra.equiv_of_eq _ _ $ power_basis.adjoin_eq_top_of_gen_mem_adjoin hx).trans
  subalgebra.top_equiv

section is_integral

namespace power_basis

open polynomial

open_locale polynomial

variables {R : Type*} [comm_ring R] [algebra R S] [algebra R K] [is_scalar_tower R K S]
variables {A : Type*} [comm_ring A] [algebra R A] [algebra S A]
variables [is_scalar_tower R S A] {B : power_basis S A} (hB : is_integral R B.gen)

include hB

/-- If `B : power_basis S A` is such that `is_integral R B.gen`, then
`is_integral R (B.basis.repr (B.gen ^ n) i)` for all `i` if
`minpoly S B.gen = (minpoly R B.gen).map (algebra_map R S)`. This is the case if `R` is a GCD domain
and `S` is its fraction ring. -/
lemma repr_gen_pow_is_integral [is_domain S]
  (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebra_map R S)) (n : ℕ) :
  ∀ i, is_integral R (B.basis.repr (B.gen ^ n) i) :=
begin
  intro i,
  let Q := (X ^ n) %ₘ (minpoly R B.gen),
  have : B.gen ^ n = aeval B.gen Q,
  { rw [← @aeval_X_pow R _ _ _ _ B.gen, ← mod_by_monic_add_div (X ^ n) (minpoly.monic hB)],
    simp },
  by_cases hQ : Q = 0,
  { simp [this, hQ, is_integral_zero] },
  have hlt : Q.nat_degree < B.dim,
  { rw [← B.nat_degree_minpoly, hmin, (minpoly.monic hB).nat_degree_map,
      nat_degree_lt_nat_degree_iff hQ],
    letI : nontrivial R := nontrivial.of_polynomial_ne hQ,
    exact degree_mod_by_monic_lt _ (minpoly.monic hB),
    apply_instance },
  rw [this, aeval_eq_sum_range' hlt],
  simp only [linear_equiv.map_sum, linear_equiv.map_smulₛₗ, ring_hom.id_apply, finset.sum_apply'],
  refine is_integral.sum _ (λ j hj, _),
  replace hj := finset.mem_range.1 hj,
  rw [← fin.coe_mk hj, ← B.basis_eq_pow, algebra.smul_def,
    is_scalar_tower.algebra_map_apply R S A, ← algebra.smul_def, linear_equiv.map_smul],
  simp only [algebra_map_smul, finsupp.coe_smul, pi.smul_apply, B.basis.repr_self_apply],
  by_cases hij : (⟨j, hj⟩ : fin _) = i,
  { simp only [hij, eq_self_iff_true, if_true],
    rw [algebra.smul_def, mul_one],
    exact is_integral_algebra_map },
  { simp [hij, is_integral_zero] }
end

variable {B}

/-- Let `B : power_basis S A` be such that `is_integral R B.gen`, and let `x y : A` be elements with
integral coordinates in the base `B.basis`. Then `is_integral R ((B.basis.repr (x * y) i)` for all
`i` if `minpoly S B.gen = (minpoly R B.gen).map (algebra_map R S)`. This is the case if `R` is a GCD
domain and `S` is its fraction ring. -/
lemma repr_mul_is_integral [is_domain S] {x y : A} (hx : ∀ i, is_integral R (B.basis.repr x i))
  (hy : ∀ i, is_integral R (B.basis.repr y i))
  (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebra_map R S)) :
  ∀ i, is_integral R ((B.basis.repr (x * y) i)) :=
begin
  intro i,
  rw [← B.basis.sum_repr x, ← B.basis.sum_repr y, finset.sum_mul_sum, linear_equiv.map_sum,
    finset.sum_apply'],
  refine is_integral.sum _ (λ I hI, _),
  simp only [algebra.smul_mul_assoc, algebra.mul_smul_comm, linear_equiv.map_smulₛₗ,
    ring_hom.id_apply, finsupp.coe_smul, pi.smul_apply, id.smul_eq_mul],
  refine is_integral_mul (hy _) (is_integral_mul (hx _) _),
  simp only [coe_basis, ← pow_add],
  refine repr_gen_pow_is_integral hB hmin _ _,
end

/-- Let `B : power_basis S A` be such that `is_integral R B.gen`, and let `x : A` be and element
with integral coordinates in the base `B.basis`. Then `is_integral R ((B.basis.repr (x ^ n) i)` for
all `i` and all `n` if `minpoly S B.gen = (minpoly R B.gen).map (algebra_map R S)`. This is the case
if `R` is a GCD domain and `S` is its fraction ring. -/
lemma repr_pow_is_integral [is_domain S] {x : A} (hx : ∀ i, is_integral R (B.basis.repr x i))
  (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebra_map R S)) (n : ℕ) :
  ∀ i, is_integral R ((B.basis.repr (x ^ n) i)) :=
begin
  nontriviality A using [subsingleton.elim (x ^ n) 0, is_integral_zero],
  revert hx,
  refine nat.case_strong_induction_on n _ (λ n hn, _),
  { intros hx i,
    rw [pow_zero, ← pow_zero B.gen, ← fin.coe_mk B.dim_pos, ← B.basis_eq_pow,
      B.basis.repr_self_apply],
    split_ifs,
    { exact is_integral_one },
    { exact is_integral_zero } },
  { intros hx,
    rw [pow_succ],
    exact repr_mul_is_integral hB hx (λ _, hn _ le_rfl (λ _, hx _) _) hmin }
end

/-- Let `B B' : power_basis K S` be such that `is_integral R B.gen`, and let `P : R[X]` be such that
`aeval B.gen P = B'.gen`. Then `is_integral R (B.basis.to_matrix B'.basis i j)` for all `i` and `j`
if `minpoly K B.gen = (minpoly R B.gen).map (algebra_map R L)`. This is the case
if `R` is a GCD domain and `K` is its fraction ring. -/
lemma to_matrix_is_integral {B B' : power_basis K S} {P : R[X]} (h : aeval B.gen P = B'.gen)
  (hB : is_integral R B.gen) (hmin : minpoly K B.gen = (minpoly R B.gen).map (algebra_map R K)) :
  ∀ i j, is_integral R (B.basis.to_matrix B'.basis i j) :=
begin
  intros i j,
  rw [B.basis.to_matrix_apply, B'.coe_basis],
  refine repr_pow_is_integral hB (λ i, _) hmin _ _,
  rw [← h, aeval_eq_sum_range, linear_equiv.map_sum, finset.sum_apply'],
  refine is_integral.sum _ (λ n hn, _),
  rw [algebra.smul_def, is_scalar_tower.algebra_map_apply R K S, ← algebra.smul_def,
    linear_equiv.map_smul, algebra_map_smul],
  exact is_integral_smul _ (repr_gen_pow_is_integral hB hmin _ _),
end

end power_basis

end is_integral

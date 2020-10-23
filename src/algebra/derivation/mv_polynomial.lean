/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.derivation.basic
import data.mv_polynomial.comm_ring
import data.mv_polynomial.pderiv

/-!
# Kähler differentials for multivariate polynomials

In this file we work on Kähler differentials for multivariate polynomials.
-/

universes u v w u₁ v₁ w₁

variables (R : Type u) (A : Type v) [comm_ring R] [comm_ring A] [algebra R A]
variables (M : Type w) [add_comm_group M] [module A M]

namespace derivation

open mv_polynomial
open_locale classical big_operators

variables (ι : Type u₁) (i : ι)

protected noncomputable def mv_polynomial : derivation R (mv_polynomial ι R) (mv_polynomial ι R) :=
{ to_fun := pderiv i,
  add := linear_map.map_add _,
  mul := λ x y, by simp_rw [pderiv_mul, smul_eq_mul, mul_comm, add_comm],
  algebra := λ r, pderiv_C }

variables {ι}
theorem mv_polynomial_eval (D : derivation R A M) (p : mv_polynomial ι R) (f : ι → A) :
  D (aeval f p) = ∑ i in p.vars, aeval f (pderiv i p) • D (f i) :=
begin
  cases subsingleton_or_nontrivial R; resetI,
  { letI := semimodule.subsingleton R A, letI := semimodule.subsingleton A M,
    exact subsingleton.elim _ _ },
  have : ∀ p : mv_polynomial ι R, ∀ q : finset ι, p.vars ⊆ q →
    ∑ i in p.vars, aeval f (pderiv i p) • D (f i) =
    ∑ i in q, aeval f (pderiv i p) • D (f i),
  { intros p q hpq, refine finset.sum_subset hpq (λ i hiq hip, _),
    rw [pderiv_eq_zero_of_not_mem_vars hip, alg_hom.map_zero, zero_smul] },
  refine induction_on p _ _ _,
  { intros r, rw [aeval_C, D.map_algebra_map, vars_C, finset.sum_empty] },
  { intros p q ihp ihq,
    rw [alg_hom.map_add, D.map_add, ihp, ihq,
        this p (p.vars ∪ q.vars) (finset.subset_union_left _ _),
        this q (p.vars ∪ q.vars) (finset.subset_union_right _ _),
        this (p+q) (p.vars ∪ q.vars) (vars_add_subset p q),
        ← finset.sum_add_distrib],
    refine finset.sum_congr rfl (λ i hi, _),
    rw [linear_map.map_add, alg_hom.map_add, add_smul] },
  { intros p i ih,
    rw [alg_hom.map_mul, aeval_X, D.map_mul, ih,
        this (p * X i) (p.vars ∪ {i}) (finset.subset.trans (vars_mul p _)
          (finset.union_subset (finset.subset_union_left _ _)
          (@vars_X R _ i _ _ ▸ finset.subset_union_right _ _))),
        finset.union_comm, ← finset.insert_eq, add_comm],
    simp only [pderiv_mul, alg_hom.map_add, add_smul, finset.sum_add_distrib,
        alg_hom.map_mul, aeval_X, finset.smul_sum, smul_smul, mul_comm (f i)],
    rw finset.sum_insert_of_eq_zero_if_not_mem, congr' 1,
    rw [finset.sum_eq_single i, pderiv_X_self, alg_hom.map_one, mul_one],
    { intros b _ hbi, rw [pderiv_X_ne R b i hbi, alg_hom.map_zero, mul_zero, zero_smul] },
    { intro h, exact absurd (finset.mem_insert_self i p.vars) h },
    { intro hip, rw [pderiv_eq_zero_of_not_mem_vars hip, alg_hom.map_zero, zero_mul, zero_smul] } }
end

end derivation

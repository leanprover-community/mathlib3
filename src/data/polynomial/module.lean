/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import ring_theory.finiteness

/-!
# Polynomial module

In this file, we define the polynomial module for an `R`-module `M`, i.e. the `R[X]`-module `M[X]`.

-/

universes u v

open polynomial
open_locale polynomial big_operators

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M] (I : ideal R)

/-- The `R[X]`-module `M[X]` for an `R`-module `M`. -/
abbreviation polynomial_module (M : Type*) [add_comm_monoid M] := ℕ →₀ M

namespace polynomial_module

-- this is definitionally equal to `module_polynomial_of_endo _`, but that is not used since the
-- simp lemmas associated to it is undesirable here.
noncomputable
instance : module R[X] (polynomial_module M) :=
begin
  refine module.comp_hom (polynomial_module M)
    (polynomial.aeval (_ : (polynomial_module M) →ₗ[R] (polynomial_module M))).to_ring_hom,
  exact
  { to_fun := λ f,
    { support := f.support.image (λ x, x + 1),
      to_fun := λ i, ite (i = 0) 0 (f (i - 1)),
      mem_support_to_fun := λ a, by cases a; simp only [nat.succ_eq_add_one, nat.add_succ_sub_one,
        finsupp.mem_support_iff, add_left_inj, exists_prop, exists_eq_right, nat.succ_ne_zero, ne.def,
        finset.mem_image, add_zero, if_false, exists_false, if_true, not_true, eq_self_iff_true] },
    map_add' := λ i j, finsupp.ext (λ i, by cases i; simp only [eq_self_iff_true, if_true,
      add_zero, finsupp.coe_add, pi.add_apply, finsupp.coe_mk, nat.succ_ne_zero, if_false]),
    map_smul' := λ i j, finsupp.ext (λ i, by cases i; simp only [nat.nat_zero_eq_zero, if_true,
      finsupp.coe_smul, zero_tsub, ring_hom.id_apply, eq_self_iff_true, pi.smul_apply, smul_zero,
      finsupp.coe_mk, tsub_zero, nat.succ_sub_succ_eq_sub, nat.succ_ne_zero, if_false]) },
end

instance (M : Type u) [add_comm_group M] [module R M] : is_scalar_tower R R[X] (ℕ →₀ M) :=
module_polynomial_of_endo.is_scalar_tower _

@[simp]
lemma monomial_smul_single (i : ℕ) (r : R) (j : ℕ) (m : M) :
  monomial i r • finsupp.single j m = finsupp.single (i + j) (r • m) :=
begin
  simp only [module_polynomial_of_endo_to_distrib_mul_action_to_mul_action_to_has_scalar_smul,
    linear_map.mul_apply, linear_map.coe_mk, polynomial.aeval_monomial, linear_map.pow_apply,
    module.algebra_map_End_apply],
  induction i generalizing r j m,
  { simp },
  { rw [function.iterate_succ, function.comp_app, nat.succ_eq_add_one, add_assoc, ← i_ih],
    congr' 2,
    ext a,
    cases a; simp [finsupp.single_apply, nat.succ_eq_one_add] }
end

@[simp]
lemma monomial_smul_apply (i : ℕ) (r : R) (g : ℕ →₀ M) (n : ℕ) :
  (monomial i r • g) n = ite (i ≤ n) (r • (g $ n - i)) 0 :=
begin
  induction g using finsupp.induction_linear with p q hp hq,
  { simp only [smul_zero, finsupp.zero_apply, if_t_t] },
  { simp only [smul_add, finsupp.add_apply, hp, hq],
    split_ifs, exacts [rfl, zero_add 0] },
  { rw [monomial_smul_single, finsupp.single_apply, finsupp.single_apply,
      smul_ite, smul_zero, ← ite_and],
    congr,
    rw eq_iff_iff,
    split,
    { rintro rfl, simp },
    { rintro ⟨e, rfl⟩, rw [add_comm, tsub_add_cancel_of_le e] } }
end

@[simp]
lemma smul_single_apply (i : ℕ) (f : R[X]) (m : M) (n : ℕ) :
  (f • finsupp.single i m) n = ite (i ≤ n) (f.coeff (n - i) • m) 0 :=
begin
  induction f using polynomial.induction_on' with p q hp hq,
  { rw [add_smul, finsupp.add_apply, hp, hq, coeff_add, add_smul],
    split_ifs, exacts [rfl, zero_add 0] },
  { rw [monomial_smul_single, finsupp.single_apply, coeff_monomial,
      ite_smul, zero_smul],
    by_cases h : i ≤ n,
    { simp_rw [eq_tsub_iff_add_eq_of_le h, if_pos h] },
    { rw [if_neg h, ite_eq_right_iff], intro e, exfalso, linarith } }
end

lemma smul_apply (f : R[X]) (g : ℕ →₀ M) (n : ℕ) :
  (f • g) n = ∑ x in finset.nat.antidiagonal n, f.coeff x.1 • g x.2 :=
begin
  induction f using polynomial.induction_on' with p q hp hq,
  { rw [add_smul, finsupp.add_apply, hp, hq, ← finset.sum_add_distrib],
    congr',
    ext,
    rw [coeff_add, add_smul] },
  { rw [finset.nat.sum_antidiagonal_eq_sum_range_succ (λ i j, (monomial f_n f_a).coeff i • g j),
      monomial_smul_apply],
    dsimp [monomial, monomial_fun],
    simp_rw [finsupp.single_smul, finsupp.single_apply],
    rw finset.sum_ite_eq,
    simp [nat.lt_succ_iff] }
end

end polynomial_module

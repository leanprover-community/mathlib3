/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import ring_theory.finiteness

/-!
# Polynomial module

In this file, we define the polynomial module for an `R`-module `M`, i.e. the `R[X]`-module `M[X]`.

This is defined as an type alias `polynomial_module R M := ℕ →₀ M`, since there might be different
module structures on `ℕ →₀ M` of interest. See the docstring of ``polynomial_module` for details.

-/

universes u v

open polynomial
open_locale polynomial big_operators

variables (R M : Type*) [comm_ring R] [add_comm_group M] [module R M] (I : ideal R)

include R

/--
The `R[X]`-module `M[X]` for an `R`-module `M`.

We require all the module instances `module S (polynomial_module R M)` to factor through `R` except
`module R[X] (polynomial_module R M)`.
In this constraint, we have the following instances for example :
- `R` acts on `polynomial_module R R[X]`.
- `R[X]` acts on `polynomial_module R R[X]` as `R[Y]` acting on `R[X][Y]`
- `R[X]` acts on `polynomial_module R[X] R[X]`.
- `R[X]` acts on `polynomial_module R[X] R[X]` as `R[X]` acting on `R[X][Y]`
- `R[X][X]` acts on `polynomial_module R[X] R[X]` as `R[X][Y]` acting on itself.

This is also the reason why `R` is included in the alias, or else there will be two different
instances of `module R[X] (polynomial_module R[X])`.

See https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2315065.20polynomial.20modules
for the full discussion.
-/
@[derive add_comm_group, derive inhabited, nolint unused_arguments]
def polynomial_module := ℕ →₀ M

omit R

variables {M}
variables {S : Type*} [comm_semiring S] [algebra S R] [module S M] [is_scalar_tower S R M]

namespace polynomial_module

/-- This is required to have the `is_scalar_tower S R M` instance to avoid diamonds. -/
@[nolint unused_arguments]
noncomputable
instance : module S (polynomial_module R M) :=
finsupp.module ℕ M

instance : has_coe_to_fun (polynomial_module R M) (λ _, ℕ → M) :=
finsupp.has_coe_to_fun

/-- The monomial `m * x ^ i`. This is defeq to `finsupp.single_add_hom`, and is redefined here
so that it has the desired type signature.  -/
noncomputable
def single (i : ℕ) : M →+ polynomial_module R M :=
finsupp.single_add_hom i

lemma single_apply (i : ℕ) (m : M) (n : ℕ) : single R i m n = ite (i = n) m 0 :=
finsupp.single_apply

/-- `polynomial_module.single` as a linear map. -/
noncomputable
def lsingle (i : ℕ) : M →ₗ[R] polynomial_module R M :=
finsupp.lsingle i

lemma lsingle_apply (i : ℕ) (m : M) (n : ℕ) : lsingle R i m n = ite (i = n) m 0 :=
finsupp.single_apply

variable {R}

lemma induction_linear {P : polynomial_module R M → Prop} (f : polynomial_module R M)
  (h0 : P 0) (hadd : ∀ f g, P f → P g → P (f + g)) (hsingle : ∀ a b, P (single R a b)) : P f :=
finsupp.induction_linear f h0 hadd hsingle

@[semireducible] noncomputable
instance polynomial_module : module R[X] (polynomial_module R M) :=
module_polynomial_of_endo ({ to_fun := λ (f : polynomial_module R M),
    { support := f.support.image (λ x, x + 1),
      to_fun := λ i, ite (i = 0) 0 (f (i - 1)),
      mem_support_to_fun := λ a, by cases a; simp only [nat.succ_eq_add_one, nat.add_succ_sub_one,
        finsupp.mem_support_iff, add_left_inj, exists_prop, exists_eq_right, nat.succ_ne_zero,
        finset.mem_image, add_zero, if_false, nat.succ_ne_zero, ne.def, finset.mem_image,
        exists_false, if_true, not_true, eq_self_iff_true] },
    map_add' := λ i j, finsupp.ext (λ i, by cases i; simp only [eq_self_iff_true, if_true,
      add_zero, finsupp.coe_add, pi.add_apply, finsupp.coe_mk, nat.succ_ne_zero, if_false]),
    map_smul' := λ i j, finsupp.ext (λ i, by cases i; simp only [nat.nat_zero_eq_zero, if_true,
      finsupp.coe_smul, zero_tsub, ring_hom.id_apply, eq_self_iff_true, pi.smul_apply, smul_zero,
      finsupp.coe_mk, tsub_zero, nat.succ_sub_succ_eq_sub, nat.succ_ne_zero, if_false]) } :
  module.End R (polynomial_module R M))

instance (M : Type u) [add_comm_group M] [module R M] :
  is_scalar_tower R R[X] (polynomial_module R M) :=
module_polynomial_of_endo.is_scalar_tower _

@[simp]
lemma monomial_smul_single (i : ℕ) (r : R) (j : ℕ) (m : M) :
  monomial i r • single R j m = single R (i + j) (r • m) :=
begin
  simp only [module_polynomial_of_endo_smul_def, linear_map.mul_apply, linear_map.coe_mk,
    polynomial.aeval_monomial, linear_map.pow_apply,  module.algebra_map_End_apply],
  induction i generalizing r j m,
  { simp [single] },
  { rw [function.iterate_succ, function.comp_app, nat.succ_eq_add_one, add_assoc, ← i_ih],
    congr' 2,
    ext a,
    cases a; simp [single_apply, nat.succ_eq_one_add] }
end

@[simp]
lemma monomial_smul_apply (i : ℕ) (r : R) (g : polynomial_module R M) (n : ℕ) :
  (monomial i r • g) n = ite (i ≤ n) (r • (g $ n - i)) 0 :=
begin
  induction g using polynomial_module.induction_linear with p q hp hq,
  { simp only [smul_zero, finsupp.zero_apply, if_t_t] },
  { simp only [smul_add, finsupp.add_apply, hp, hq],
    split_ifs, exacts [rfl, zero_add 0] },
  { rw [monomial_smul_single, single_apply, single_apply, smul_ite, smul_zero, ← ite_and],
    congr,
    rw eq_iff_iff,
    split,
    { rintro rfl, simp },
    { rintro ⟨e, rfl⟩, rw [add_comm, tsub_add_cancel_of_le e] } }
end

@[simp]
lemma smul_single_apply (i : ℕ) (f : R[X]) (m : M) (n : ℕ) :
  (f • single R i m) n = ite (i ≤ n) (f.coeff (n - i) • m) 0 :=
begin
  induction f using polynomial.induction_on' with p q hp hq,
  { rw [add_smul, finsupp.add_apply, hp, hq, coeff_add, add_smul],
    split_ifs, exacts [rfl, zero_add 0] },
  { rw [monomial_smul_single, single_apply, coeff_monomial, ite_smul, zero_smul],
    by_cases h : i ≤ n,
    { simp_rw [eq_tsub_iff_add_eq_of_le h, if_pos h] },
    { rw [if_neg h, ite_eq_right_iff], intro e, exfalso, linarith } }
end

lemma smul_apply (f : R[X]) (g : polynomial_module R M) (n : ℕ) :
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

/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import ring_theory.finite_type

/-!
# Polynomial module

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define the polynomial module for an `R`-module `M`, i.e. the `R[X]`-module `M[X]`.

This is defined as an type alias `polynomial_module R M := ℕ →₀ M`, since there might be different
module structures on `ℕ →₀ M` of interest. See the docstring of `polynomial_module` for details.

-/

universes u v

open polynomial
open_locale polynomial big_operators

variables (R M : Type*) [comm_ring R] [add_comm_group M] [module R M] (I : ideal R)

include R

/--
The `R[X]`-module `M[X]` for an `R`-module `M`.
This is isomorphic (as an `R`-module) to `M[X]` when `M` is a ring.

We require all the module instances `module S (polynomial_module R M)` to factor through `R` except
`module R[X] (polynomial_module R M)`.
In this constraint, we have the following instances for example :
- `R` acts on `polynomial_module R R[X]`
- `R[X]` acts on `polynomial_module R R[X]` as `R[Y]` acting on `R[X][Y]`
- `R` acts on `polynomial_module R[X] R[X]`
- `R[X]` acts on `polynomial_module R[X] R[X]` as `R[X]` acting on `R[X][Y]`
- `R[X][X]` acts on `polynomial_module R[X] R[X]` as `R[X][Y]` acting on itself

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

lemma single_smul (i : ℕ) (r : R) (m : M) : single R i (r • m) = r • (single R i m) :=
(lsingle R i).map_smul r m

variable {R}

lemma induction_linear {P : polynomial_module R M → Prop} (f : polynomial_module R M)
  (h0 : P 0) (hadd : ∀ f g, P f → P g → P (f + g)) (hsingle : ∀ a b, P (single R a b)) : P f :=
finsupp.induction_linear f h0 hadd hsingle

@[semireducible] noncomputable
instance polynomial_module : module R[X] (polynomial_module R M) :=
module_polynomial_of_endo (finsupp.lmap_domain _ _ nat.succ)

instance (M : Type u) [add_comm_group M] [module R M] [module S M] [is_scalar_tower S R M] :
  is_scalar_tower S R (polynomial_module R M) :=
finsupp.is_scalar_tower _ _

instance is_scalar_tower' (M : Type u) [add_comm_group M] [module R M] [module S M]
  [is_scalar_tower S R M] :
  is_scalar_tower S R[X] (polynomial_module R M) :=
begin
  haveI : is_scalar_tower R R[X] (polynomial_module R M) :=
    module_polynomial_of_endo.is_scalar_tower _,
  constructor,
  intros x y z,
  rw [← @is_scalar_tower.algebra_map_smul S R, ← @is_scalar_tower.algebra_map_smul S R,
    smul_assoc],
end

@[simp]
lemma monomial_smul_single (i : ℕ) (r : R) (j : ℕ) (m : M) :
  monomial i r • single R j m = single R (i + j) (r • m) :=
begin
  simp only [linear_map.mul_apply, polynomial.aeval_monomial, linear_map.pow_apply,
    module.algebra_map_End_apply, module_polynomial_of_endo_smul_def],
  induction i generalizing r j m,
  { simp [single] },
  { rw [function.iterate_succ, function.comp_app, nat.succ_eq_add_one, add_assoc, ← i_ih],
    congr' 2,
    ext a,
    dsimp [single],
    rw [finsupp.map_domain_single, nat.succ_eq_one_add] }
end

@[simp]
lemma monomial_smul_apply (i : ℕ) (r : R) (g : polynomial_module R M) (n : ℕ) :
  (monomial i r • g) n = ite (i ≤ n) (r • g (n - i)) 0 :=
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
    dsimp [monomial],
    simp_rw [finsupp.single_smul, finsupp.single_apply],
    rw finset.sum_ite_eq,
    simp [nat.lt_succ_iff] }
end

/-- `polynomial_module R R` is isomorphic to `R[X]` as an `R[X]` module. -/
noncomputable
def equiv_polynomial_self : polynomial_module R R ≃ₗ[R[X]] R[X] :=
{ map_smul' := λ r x, begin
    induction r using polynomial.induction_on' with _ _ _ _ n p,
    { simp only [add_smul, map_add, ring_equiv.to_fun_eq_coe, *] at * },
    { ext i,
      dsimp,
      rw [monomial_smul_apply, ← polynomial.C_mul_X_pow_eq_monomial, mul_assoc,
        polynomial.coeff_C_mul, polynomial.coeff_X_pow_mul', mul_ite, mul_zero],
      simp }
  end,
  ..(polynomial.to_finsupp_iso R).symm  }

/-- `polynomial_module R S` is isomorphic to `S[X]` as an `R` module. -/
noncomputable
def equiv_polynomial {S : Type*} [comm_ring S] [algebra R S] :
  polynomial_module R S ≃ₗ[R] S[X] :=
{ map_smul' := λ r x, rfl, ..(polynomial.to_finsupp_iso S).symm  }

variables (R' : Type*) {M' : Type*} [comm_ring R'] [add_comm_group M'] [module R' M']
variables [algebra R R'] [module R M'] [is_scalar_tower R R' M']

/-- The image of a polynomial under a linear map. -/
noncomputable
def map (f : M →ₗ[R] M') : polynomial_module R M →ₗ[R] polynomial_module R' M' :=
finsupp.map_range.linear_map f

@[simp]
lemma map_single (f : M →ₗ[R] M') (i : ℕ) (m : M) :
  map R' f (single R i m) = single R' i (f m) :=
finsupp.map_range_single

lemma map_smul (f : M →ₗ[R] M') (p : R[X]) (q : polynomial_module R M) :
  map R' f (p • q) = p.map (algebra_map R R') • map R' f q :=
begin
  apply induction_linear q,
  { rw [smul_zero, map_zero, smul_zero] },
  { intros f g e₁ e₂, rw [smul_add, map_add, e₁, e₂, map_add, smul_add] },
  intros i m,
  apply polynomial.induction_on' p,
  { intros p q e₁ e₂, rw [add_smul, map_add, e₁, e₂, polynomial.map_add, add_smul] },
  { intros j s,
    rw [monomial_smul_single, map_single, polynomial.map_monomial, map_single,
      monomial_smul_single, f.map_smul, algebra_map_smul] }
end

/-- Evaulate a polynomial `p : polynomial_module R M` at `r : R`. -/
@[simps (lemmas_only)]
def eval (r : R) : polynomial_module R M →ₗ[R] M :=
{ to_fun := λ p, p.sum (λ i m, r ^ i • m),
  map_add' := λ x y, finsupp.sum_add_index' (λ _, smul_zero _) (λ _ _ _, smul_add _ _ _),
  map_smul' := λ s m, begin
    refine (finsupp.sum_smul_index' _).trans _,
    { exact λ i, smul_zero _ },
    { simp_rw [← smul_comm s, ← finsupp.smul_sum], refl }
  end }

@[simp]
lemma eval_single (r : R) (i : ℕ) (m : M) : eval r (single R i m) = r ^ i • m :=
finsupp.sum_single_index (smul_zero _)

@[simp]
lemma eval_lsingle (r : R) (i : ℕ) (m : M) : eval r (lsingle R i m) = r ^ i • m :=
eval_single r i m

lemma eval_smul (p : R[X]) (q : polynomial_module R M) (r : R) :
  eval r (p • q) = p.eval r • eval r q :=
begin
  apply induction_linear q,
  { rw [smul_zero, map_zero, smul_zero] },
  { intros f g e₁ e₂, rw [smul_add, map_add, e₁, e₂, map_add, smul_add] },
  intros i m,
  apply polynomial.induction_on' p,
  { intros p q e₁ e₂, rw [add_smul, map_add, polynomial.eval_add, e₁, e₂, add_smul] },
  { intros j s,
    rw [monomial_smul_single, eval_single, polynomial.eval_monomial, eval_single,
      smul_comm, ← smul_smul, pow_add, mul_smul] }
end

@[simp]
lemma eval_map (f : M →ₗ[R] M') (q : polynomial_module R M) (r : R) :
  eval (algebra_map R R' r) (map R' f q) = f (eval r q) :=
begin
  apply induction_linear q,
  { simp_rw map_zero },
  { intros f g e₁ e₂, simp_rw [map_add, e₁, e₂] },
  { intros i m,
    rw [map_single, eval_single, eval_single, f.map_smul, ← map_pow, algebra_map_smul] }
end

@[simp]
lemma eval_map' (f : M →ₗ[R] M) (q : polynomial_module R M) (r : R) :
  eval r (map R f q) = f (eval r q) :=
eval_map R f q r

/-- `comp p q` is the composition of `p : R[X]` and `q : M[X]` as `q(p(x))`.  -/
@[simps] noncomputable
def comp (p : R[X]) : polynomial_module R M →ₗ[R] polynomial_module R M :=
((eval p).restrict_scalars R).comp (map R[X] (lsingle R 0))

lemma comp_single (p : R[X]) (i : ℕ) (m : M) : comp p (single R i m) = p ^ i • single R 0 m :=
begin
  rw comp_apply,
  erw [map_single, eval_single],
  refl
end

lemma comp_eval (p : R[X]) (q : polynomial_module R M) (r : R) :
  eval r (comp p q) = eval (p.eval r) q :=
begin
  rw ← linear_map.comp_apply,
  apply induction_linear q,
  { rw [map_zero, map_zero] },
  { intros _ _ e₁ e₂, rw [map_add, map_add, e₁, e₂] },
  { intros i m,
    rw [linear_map.comp_apply, comp_single, eval_single, eval_smul, eval_single, pow_zero,
      one_smul, polynomial.eval_pow] }
end

lemma comp_smul (p p' : R[X]) (q : polynomial_module R M) :
  comp p (p' • q) = p'.comp p • comp p q :=
begin
  rw [comp_apply, map_smul, eval_smul, polynomial.comp, polynomial.eval_map, comp_apply],
  refl
end

end polynomial_module

/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import ring_theory.adjoin.polynomial
import data.mv_polynomial.variables

/-!
# Polynomials supported by a set of variables

This file contains the definition and lemmas about `mv_polynomial.supported`.

## Main definitions

* `mv_polynomial.supported` : Given a set `s : set σ`, `supported R s` is the subalgebra of
  `mv_polynomial σ R` consisting of polynomials whose set of variables is contained in `s`.
  This subalgebra is isomorphic to `mv_polynomial s R`

## Tags
variables, polynomial, vars
-/
universes u v w

namespace mv_polynomial
variables {σ τ : Type*} {R : Type u} {S : Type v} {r : R} {e : ℕ} {n m : σ}

section comm_semiring
variables [comm_semiring R] {p q : mv_polynomial σ R}

variables (R)

/-- The set of polynomials whose variables are contained in `s` as a `subalgebra` over `R`. -/
noncomputable def supported (s : set σ) : subalgebra R (mv_polynomial σ R) :=
algebra.adjoin R (X '' s)

variables {σ R}

open_locale classical
open algebra

lemma supported_eq_range_rename (s : set σ) :
  supported R s = (rename (coe : s → σ)).range :=
by rw [supported, set.image_eq_range, adjoin_range_eq_range_aeval, rename]

/--The isomorphism between the subalgebra of polynomials supported by `s` and `mv_polynomial s R`-/
noncomputable def supported_equiv_mv_polynomial (s : set σ) :
  supported R s ≃ₐ[R] mv_polynomial s R :=
(subalgebra.equiv_of_eq _ _ (supported_eq_range_rename s)).trans
(alg_equiv.of_injective (rename (coe : s → σ))
  (rename_injective _ subtype.val_injective)).symm

@[simp] lemma supported_equiv_mv_polynomial_symm_C (s : set σ) (x : R) :
  (supported_equiv_mv_polynomial s).symm (C x) = algebra_map R (supported R s) x :=
begin
  ext1,
  simp [supported_equiv_mv_polynomial, mv_polynomial.algebra_map_eq],
end

@[simp] lemma supported_equiv_mv_polynomial_symm_X (s : set σ) (i : s) :
  (↑((supported_equiv_mv_polynomial s).symm (X i : mv_polynomial s R)) : mv_polynomial σ R) = X i :=
by simp [supported_equiv_mv_polynomial]

variables {s t : set σ}

lemma mem_supported : p ∈ (supported R s) ↔ ↑p.vars ⊆ s :=
begin
  rw [supported_eq_range_rename, alg_hom.mem_range],
  split,
  { rintros ⟨p, rfl⟩,
    refine trans (finset.coe_subset.2 (vars_rename _ _)) _,
    simp },
  { intros hs,
    exact exists_rename_eq_of_vars_subset_range p (coe : s → σ) subtype.val_injective (by simpa) }
end

lemma supported_eq_vars_subset : (supported R s : set (mv_polynomial σ R)) = {p | ↑p.vars ⊆ s} :=
set.ext $ λ _, mem_supported

@[simp] lemma mem_supported_vars (p : mv_polynomial σ R) : p ∈ supported R (↑p.vars : set σ) :=
by rw [mem_supported]

variable (s)

lemma supported_eq_adjoin_X : supported R s = algebra.adjoin R (X '' s) := rfl

@[simp] lemma supported_univ : supported R (set.univ : set σ) = ⊤ :=
by simp [algebra.eq_top_iff, mem_supported]

@[simp] lemma supported_empty : supported R (∅ : set σ) = ⊥ :=
by simp [supported_eq_adjoin_X]

variables {s}

lemma supported_mono (st : s ⊆ t) : supported R s ≤ supported R t :=
algebra.adjoin_mono (set.image_subset _ st)

@[simp] lemma X_mem_supported [nontrivial R] {i : σ} : (X i) ∈ supported R s ↔ i ∈ s :=
by simp [mem_supported]

@[simp] lemma supported_le_supported_iff [nontrivial R] :
  supported R s ≤ supported R t ↔ s ⊆ t :=
begin
  split,
  { intros h i,
    simpa using @h (X i) },
  { exact supported_mono }
end

lemma supported_strict_mono [nontrivial R] :
  strict_mono (supported R : set σ → subalgebra R (mv_polynomial σ R)) :=
strict_mono_of_le_iff_le (λ _ _, supported_le_supported_iff.symm)

end comm_semiring

end mv_polynomial

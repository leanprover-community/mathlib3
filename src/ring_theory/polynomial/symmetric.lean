/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang, Johan Commelin
-/
import tactic
import data.mv_polynomial.rename
import data.mv_polynomial.comm_ring

/-!
# Symmetric Polynomials and Elementary Symmetric Polynomials

This file defines symmetric polynomials and elementary symmetric polynomials.
We also prove some basic facts about them.

## Main declarations

* `mv_polynomial.is_symmetric`

* `mv_polynomial.esymm`

## Notation

+ `esymm σ R n`, is the `n`th elementary symmetric polynomial in `mv_polynomial σ R`.

As in other polynomial files, we typically use the notation:

+ `σ τ α : Type*` (indexing the variables)

+ `R S : Type*` `[comm_semiring R]` `[comm_semiring S]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ α`

-/

open equiv (perm)
open_locale big_operators
noncomputable theory

namespace mv_polynomial

variables {σ : Type*} {R : Type*}
variables {τ : Type*} {S : Type*}

/-- A mv_polynomial φ is symmetric if it is invariant under
permutations of its variables by the  `rename` operation -/
def is_symmetric [comm_semiring R] (φ : mv_polynomial σ R) : Prop :=
∀ e : perm σ, rename e φ = φ

namespace is_symmetric
variables [comm_semiring R] [comm_semiring S] {φ ψ : mv_polynomial σ R}

@[simp]
lemma C (r : R) : is_symmetric (C r : mv_polynomial σ R) :=
λ e, rename_C e r

@[simp]
lemma zero : is_symmetric (0 : mv_polynomial σ R) :=
by { rw [← C_0], exact is_symmetric.C 0 }

@[simp]
lemma one : is_symmetric (1 : mv_polynomial σ R) :=
by { rw [← C_1], exact is_symmetric.C 1 }

@[simp]
lemma add (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ + ψ) :=
λ e, by rw [alg_hom.map_add, hφ, hψ]

@[simp]
lemma mul (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ * ψ) :=
λ e, by rw [alg_hom.map_mul, hφ, hψ]

@[simp]
lemma smul (r : R) (hφ : is_symmetric φ) : is_symmetric (r • φ) :=
λ e, by rw [alg_hom.map_smul, hφ]

@[simp]
lemma map (hφ : is_symmetric φ) (f : R →+* S) : is_symmetric (map f φ) :=
λ e, by rw [← map_rename, hφ]

end is_symmetric

namespace is_symmetric

variables [comm_ring R] {φ ψ : mv_polynomial σ R}

@[simp]
lemma neg (hφ : is_symmetric φ) : is_symmetric (-φ) :=
λ e, by rw [alg_hom.map_neg, hφ]

@[simp]
lemma sub (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ - ψ) :=
λ e, by rw [alg_hom.map_sub, hφ, hψ]

end is_symmetric

section elementary_symmetric

open finset

variables (σ R) [comm_semiring R] [comm_semiring S] [fintype σ] [fintype τ]

/-- Define `esymm σ R n` as the `n`th elementary symmetric polynomial in `mv_polynomial σ R`. -/
def esymm (n : ℕ) : mv_polynomial σ R :=
∑ t in powerset_len n univ, ∏ i in t, X i

/-- A second definition of `esymm σ R n` that ranges over a subtype instead of `powerset_len`.
  Sometimes it's easier to reason with subtypes. -/
lemma esymm₂ (n : ℕ) : (esymm σ R n) =
  ∑ t : {s : finset σ // s.card = n}, ∏ i in (t : finset σ), X i :=
begin
  rw esymm,
  let i : Π (a : finset σ), a ∈ powerset_len n univ → {s : finset σ // s.card = n} :=
  by {intros a ha, split, exact (mem_powerset_len.mp ha).2, apply_instance },
  refine sum_bij i (λ a ha, mem_univ (i a ha)) _ (λ _ _ _ _ hi, subtype.ext_iff_val.mp hi) _,
  { intros,
    apply prod_congr,
    simp only [subtype.coe_mk],
    intros, refl,},
  { refine (λ b H, ⟨b.val, mem_powerset_len.mpr ⟨subset_univ b.val, b.property⟩, _⟩),
    simp [i] },
end

@[simp] lemma esymm_zero : esymm σ R 0 = 1 :=
by simp only [esymm, powerset_len_zero, sum_singleton, prod_empty]

lemma map_esymm (n : ℕ) (f : R →+* S) :
  map f (esymm σ R n) = esymm σ S n :=
begin
  rw [esymm, (map f).map_sum],
  refine sum_congr rfl (λ x hx, _),
  rw (map f).map_prod,
  simp,
end

lemma rename_esymm (n : ℕ) (e : σ ≃ τ) :
  rename e (esymm σ R n) = esymm τ R n :=
begin
  simp [esymm, esymm₂, (rename e).map_sum],
  let e' : {s : finset σ // s.card = n} ≃ {s : finset τ // s.card = n} :=
  equiv.subtype_congr (equiv.finset_congr e)
    (by { intro, rw [equiv.finset_congr_apply, card_map] }),
  rw ← equiv.sum_comp e'.symm,
  apply fintype.sum_congr,
  intro,
  calc _ = (∏ i in (e'.symm a : finset σ), (rename e) (X i)) : (rename e).map_prod _ _
     ... = (∏ i in (a : finset τ), (rename e) (X (e.symm i))) : prod_map (a : finset τ) _ _
     ... = _ : _,
  apply finset.prod_congr rfl,
  intros,
  simp,
end

lemma esymm_is_symmetric (n : ℕ) : is_symmetric (esymm σ R n) :=
by { intro, rw rename_esymm }

end elementary_symmetric

end mv_polynomial

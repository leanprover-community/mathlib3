/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang, Johan Commelin
-/
import data.mv_polynomial.rename
import data.mv_polynomial.comm_ring
import algebra.algebra.subalgebra.basic

/-!
# Symmetric Polynomials and Elementary Symmetric Polynomials

This file defines symmetric `mv_polynomial`s and elementary symmetric `mv_polynomial`s.
We also prove some basic facts about them.

## Main declarations

* `mv_polynomial.is_symmetric`

* `mv_polynomial.symmetric_subalgebra`

* `mv_polynomial.esymm`

## Notation

+ `esymm σ R n`, is the `n`th elementary symmetric polynomial in `mv_polynomial σ R`.

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R S : Type*` `[comm_semiring R]` `[comm_semiring S]` (the coefficients)

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `φ ψ : mv_polynomial σ R`

-/

open equiv (perm)
open_locale big_operators
noncomputable theory

namespace multiset

variables {R : Type*} [comm_semiring R]

/-- The `n`th elementary symmetric function evaluated at the elements of `s` -/
def esymm (s : multiset R) (n : ℕ) : R := ((s.powerset_len n).map multiset.prod).sum

lemma _root_.finset.esymm_map_val {σ} (f : σ → R) (s : finset σ) (n : ℕ) :
  (s.val.map f).esymm n = (s.powerset_len n).sum (λ t, t.prod f) :=
by simpa only [esymm, powerset_len_map, ← finset.map_val_val_powerset_len, map_map]

end multiset

namespace mv_polynomial

variables {σ : Type*} {R : Type*}
variables {τ : Type*} {S : Type*}

/-- A `mv_polynomial φ` is symmetric if it is invariant under
permutations of its variables by the  `rename` operation -/
def is_symmetric [comm_semiring R] (φ : mv_polynomial σ R) : Prop :=
∀ e : perm σ, rename e φ = φ

variables (σ R)

/-- The subalgebra of symmetric `mv_polynomial`s. -/
def symmetric_subalgebra [comm_semiring R] : subalgebra R (mv_polynomial σ R) :=
{ carrier := set_of is_symmetric,
  algebra_map_mem' := λ r e, rename_C e r,
  mul_mem' := λ a b ha hb e, by rw [alg_hom.map_mul, ha, hb],
  add_mem' := λ a b ha hb e, by rw [alg_hom.map_add, ha, hb] }

variables {σ R}

@[simp] lemma mem_symmetric_subalgebra [comm_semiring R] (p : mv_polynomial σ R) :
  p ∈ symmetric_subalgebra σ R ↔ p.is_symmetric := iff.rfl

namespace is_symmetric

section comm_semiring
variables [comm_semiring R] [comm_semiring S] {φ ψ : mv_polynomial σ R}

@[simp]
lemma C (r : R) : is_symmetric (C r : mv_polynomial σ R) :=
(symmetric_subalgebra σ R).algebra_map_mem r

@[simp]
lemma zero : is_symmetric (0 : mv_polynomial σ R) :=
(symmetric_subalgebra σ R).zero_mem

@[simp]
lemma one : is_symmetric (1 : mv_polynomial σ R) :=
(symmetric_subalgebra σ R).one_mem

lemma add (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ + ψ) :=
(symmetric_subalgebra σ R).add_mem hφ hψ

lemma mul (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ * ψ) :=
(symmetric_subalgebra σ R).mul_mem hφ hψ

lemma smul (r : R) (hφ : is_symmetric φ) : is_symmetric (r • φ) :=
(symmetric_subalgebra σ R).smul_mem hφ r

@[simp]
lemma map (hφ : is_symmetric φ) (f : R →+* S) : is_symmetric (map f φ) :=
λ e, by rw [← map_rename, hφ]

end comm_semiring

section comm_ring
variables [comm_ring R] {φ ψ : mv_polynomial σ R}

lemma neg (hφ : is_symmetric φ) : is_symmetric (-φ) :=
(symmetric_subalgebra σ R).neg_mem hφ

lemma sub (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ - ψ) :=
(symmetric_subalgebra σ R).sub_mem hφ hψ

end comm_ring

end is_symmetric

section elementary_symmetric
open finset
variables (σ R) [comm_semiring R] [comm_semiring S] [fintype σ] [fintype τ]

/-- The `n`th elementary symmetric `mv_polynomial σ R`. -/
def esymm (n : ℕ) : mv_polynomial σ R :=
∑ t in powerset_len n univ, ∏ i in t, X i

/-- The `n`th elementary symmetric `mv_polynomial σ R` is obtained by evaluating the
`n`th elementary symmetric at the `multiset` of the monomials -/
lemma esymm_eq_multiset_esymm : esymm σ R = (finset.univ.val.map X).esymm :=
funext $ λ n, (finset.univ.esymm_map_val X n).symm

lemma aeval_esymm_eq_multiset_esymm [algebra R S] (f : σ → S) (n : ℕ) :
  aeval f (esymm σ R n) = (finset.univ.val.map f).esymm n :=
by simp_rw [esymm, aeval_sum, aeval_prod, aeval_X, esymm_map_val]

/-- We can define `esymm σ R n` by summing over a subtype instead of over `powerset_len`. -/
lemma esymm_eq_sum_subtype (n : ℕ) : esymm σ R n =
  ∑ t : {s : finset σ // s.card = n}, ∏ i in (t : finset σ), X i :=
sum_subtype _ (λ _, mem_powerset_len_univ_iff) _

/-- We can define `esymm σ R n` as a sum over explicit monomials -/
lemma esymm_eq_sum_monomial (n : ℕ) : esymm σ R n =
  ∑ t in powerset_len n univ, monomial (∑ i in t, finsupp.single i 1) 1 :=
begin
  simp_rw monomial_sum_one,
  refl,
end

@[simp] lemma esymm_zero : esymm σ R 0 = 1 :=
by simp only [esymm, powerset_len_zero, sum_singleton, prod_empty]

lemma map_esymm (n : ℕ) (f : R →+* S) : map f (esymm σ R n) = esymm σ S n :=
by simp_rw [esymm, map_sum, map_prod, map_X]

lemma rename_esymm (n : ℕ) (e : σ ≃ τ) : rename e (esymm σ R n) = esymm τ R n :=
calc rename e (esymm σ R n)
     = ∑ x in powerset_len n univ, ∏ i in x, X (e i)
       : by simp_rw [esymm, map_sum, map_prod, rename_X]
 ... = ∑ t in powerset_len n (univ.map e.to_embedding), ∏ i in t, X i
       : by simp [finset.powerset_len_map, -finset.map_univ_equiv]
 ... = ∑ t in powerset_len n univ, ∏ i in t, X i : by rw finset.map_univ_equiv

lemma esymm_is_symmetric (n : ℕ) : is_symmetric (esymm σ R n) :=
by { intro, rw rename_esymm }

lemma support_esymm'' (n : ℕ) [decidable_eq σ] [nontrivial R] :
  (esymm σ R n).support = (powerset_len n (univ : finset σ)).bUnion
    (λ t, (finsupp.single (∑ (i : σ) in t, finsupp.single i 1) (1:R)).support) :=
begin
  rw esymm_eq_sum_monomial,
  simp only [← single_eq_monomial],
  convert finsupp.support_sum_eq_bUnion (powerset_len n (univ : finset σ)) _,
  intros s t hst,
  rw finset.disjoint_left,
  simp only [finsupp.support_single_ne_zero _ one_ne_zero, mem_singleton],
  rintro a h rfl,
  have := congr_arg finsupp.support h,
  rw [finsupp.support_sum_eq_bUnion, finsupp.support_sum_eq_bUnion] at this,
  { simp only [finsupp.support_single_ne_zero _ one_ne_zero, bUnion_singleton_eq_self] at this,
    exact absurd this hst.symm },
  all_goals { intros x y, simp [finsupp.support_single_disjoint] }
end

lemma support_esymm' (n : ℕ) [decidable_eq σ] [nontrivial R] :
  (esymm σ R n).support =
  (powerset_len n (univ : finset σ)).bUnion (λ t, {∑ (i : σ) in t, finsupp.single i 1}) :=
begin
  rw support_esymm'',
  congr,
  funext,
  exact finsupp.support_single_ne_zero _ one_ne_zero
end

lemma support_esymm (n : ℕ) [decidable_eq σ] [nontrivial R] :
  (esymm σ R n).support =
  (powerset_len n (univ : finset σ)).image (λ t, ∑ (i : σ) in t, finsupp.single i 1) :=
by { rw support_esymm', exact bUnion_singleton }

lemma degrees_esymm [nontrivial R]
  (n : ℕ) (hpos : 0 < n) (hn : n ≤ fintype.card σ) :
  (esymm σ R n).degrees = (univ : finset σ).val :=
begin
  classical,
  have : (finsupp.to_multiset ∘ λ (t : finset σ), ∑ (i : σ) in t, finsupp.single i 1) = finset.val,
  { funext, simp [finsupp.to_multiset_sum_single] },
  rw [degrees, support_esymm, sup_finset_image, this, ←comp_sup_eq_sup_comp],
  { obtain ⟨k, rfl⟩ := nat.exists_eq_succ_of_ne_zero hpos.ne',
    simpa using powerset_len_sup _ _ (nat.lt_of_succ_le hn) },
  { intros,
    simp only [union_val, sup_eq_union],
    congr },
  { refl }
end

end elementary_symmetric

end mv_polynomial

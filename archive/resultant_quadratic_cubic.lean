/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import field_theory.is_alg_closed.basic
import linear_algebra.matrix
import ring_theory.polynomial.homogeneous
import tactic.linear_combination

/-! # The resultant of a quadratic and a cubic polynomial

We characterize when a quadratic and a cubic polynomial have a common root in `ℙ¹`, in terms of
their resultant.  We follow the sketch at
[Reid, *Undergraduate Algebraic Geometry*, exercise 1.10][Reid88].  This is just a special case of
the general result (for polynomials of general degree).

-/

open matrix mv_polynomial

open_locale classical

noncomputable theory

section mv_polynomial_lemmas

-- move this
lemma eval_eq_zero_of_dvd {σ R : Type*} [comm_semiring R] {p q : mv_polynomial σ R} {x : σ → R}
  (h : eval x p = 0) (hpq : p ∣ q) :
  eval x q = 0 :=
begin
  obtain ⟨r, rfl⟩ := hpq,
  simp [h],
end

-- move this (and state for polynomials in arbitrary many variables?)
lemma linear_has_root {K : Type*} [field K] {x : mv_polynomial (fin 2) K}
  (hx : x.is_homogeneous 1) :
  ∃ v : fin 2 → K, v ≠ 0 ∧ eval v x = 0 :=
sorry

-- move this
lemma match_roots_and_pigeonhole {K : Type*} [field K] [is_alg_closed K]
  (A B q c : mv_polynomial (fin 2) K) (hA : A.is_homogeneous 1) (hB : B.is_homogeneous 2)
  (hq : q.is_homogeneous 2) (hc : c.is_homogeneous 3) (H : B * q = A * c) :
  ∃ x : mv_polynomial (fin 2) K, x ≠ 0 ∧ x.is_homogeneous 1 ∧ x ∣ q ∧ x ∣ c :=
sorry

end mv_polynomial_lemmas

section ring
variables {R : Type*} [comm_ring R]

variables (a₀ a₁ a₂ b₀ b₁ b₂ b₃ U V : R)

/-- Defines a quadratic polynomial on `ℙ¹` -/
def q : mv_polynomial (fin 2) R := a₀ • (X 0) ^ 2 + a₁ • (X 0) * (X 1) + a₂ • (X 1) ^ 2

/-- Defines a cubic polynomial on `ℙ¹` -/
def c : mv_polynomial (fin 2) R :=
b₀ • (X 0) ^ 3 + b₁ • (X 0) ^ 2 * (X 1) + b₂ • X 0 * (X 1) ^ 2 + b₃ • (X 1) ^ 3

/-- **Sylvester matrix** associated to a quadratic and a cubic in `ℙ¹`; its determinant is called
the **resultant** of that quadratic and that cubic. -/
def mat : matrix (fin 5) (fin 5) R :=
![![a₀, a₁, a₂,  0,  0],
  ![ 0, a₀, a₁, a₂,  0],
  ![ 0,  0, a₀, a₁, a₂],
  ![b₀, b₁, b₂, b₃,  0],
  ![ 0, b₀, b₁, b₂, b₃]]

lemma sylvester_mul_rational_normal (a₀ a₁ a₂ b₀ b₁ b₂ b₃ U V : R) (k : fin 5 → R) :
  dot_product
    (vec_mul k (mat a₀ a₁ a₂ b₀ b₁ b₂ b₃))
    (![U ^ 4, U ^ 3 * V, U ^ 2 * V ^ 2, U * V ^ 3, V ^ 4])
  = (k 0 * U ^ 2 + k 1 * U * V + k 2 * V ^ 2) * (a₀ * U ^ 2 + a₁ * U * V + a₂ * V ^ 2)
    + (k 3 * U + k 4 * V) * (b₀ * U ^ 3 + b₁ * U ^ 2 * V + b₂ * U * V ^ 2 + b₃ * V ^ 3) :=
begin
  have H : (2 : fin (1+2)).succ = 3 := rfl,
  have H' : (2 : fin (nat.succ (1+2))).succ = 3 := rfl,
  have H'' : (3 : fin 4).succ = 4 := rfl,
  simp [mat, vec_mul, dot_product, fin.sum_univ_succ, q, c, H, H', H''],
  ring
end

variables [is_domain R]
variables {a₀ a₁ a₂ b₀ b₁ b₂ b₃ U V}

/-- If a quadratic and a cubic in `ℙ¹` have a common root, then their resultant is zero. -/
lemma resultant_eq_zero_of_common_root (hUV : ![U, V] ≠ 0) (hq : eval ![U, V] (q a₀ a₁ a₂) = 0)
  (hc : eval ![U, V] (c b₀ b₁ b₂ b₃) = 0) :
  det (mat a₀ a₁ a₂ b₀ b₁ b₂ b₃) = 0 :=
begin
  simp only [q, c, algebra.smul_mul_assoc, _root_.map_add, smul_eval, map_pow, eval_X, cons_val_zero,
    _root_.map_mul, cons_val_one, head_cons] at hq hc,
  rw ← matrix.exists_mul_vec_eq_zero_iff,
  refine ⟨![U ^ 4, U ^ 3 * V, U ^ 2 * V ^ 2, U * V ^ 3, V ^ 4], _, _⟩,
  { contrapose! hUV,
    ext i,
    fin_cases i,
    { have : U ^ 4 = 0 := congr_fun hUV 0,
      exact pow_eq_zero this },
    { have : V ^ 4 = 0 := congr_fun hUV 4,
      exact pow_eq_zero this } },
  ext i,
  fin_cases i;
  simp only [mat, cons_append, cons_val_fin_one, cons_val_one, cons_val_succ, cons_val_zero,
    cons_vec_alt0, cons_vec_alt1, cons_vec_bit0_eq_alt0, cons_vec_bit1_eq_alt1, dot_product,
    empty_append, fin.sum_univ_succ, finset.card_singleton, finset.sum_const,
    fintype.univ_of_subsingleton, head_cons, mul_vec, nat.cast_one, nsmul_eq_mul, pi.zero_apply],
  { linear_combination (hq, U^2) },
  { linear_combination (hq, U * V) },
  { linear_combination (hq, V^2) },
  { linear_combination (hc, U) },
  { linear_combination (hc, V) },
end
end ring

variables {K : Type*} [field K] [is_alg_closed K]
variables {a₀ a₁ a₂ b₀ b₁ b₂ b₃ : K}

/-- If the resultant of a certain quadratic and cubic in `ℙ¹` is zero, then that quadratic and cubic
have a common root. -/
lemma common_root_of_resultant_eq_zero (h : det (mat a₀ a₁ a₂ b₀ b₁ b₂ b₃) = 0) :
  ∃ v : fin 2 → K, v ≠ 0 ∧ eval v (q a₀ a₁ a₂) = 0 ∧ eval v (c b₀ b₁ b₂ b₃) = 0 :=
begin
  rw ← matrix.exists_vec_mul_eq_zero_iff at h,
  obtain ⟨k, hk, habk⟩ := h,
  rw mat at habk,
  let A : mv_polynomial (fin 2) K := C (k 3) * X 0 + C (k 4) * X 1,
  let B : mv_polynomial (fin 2) K := C (k 0) * X 0 ^ 2 + C (k 1) * X 0 * X 1 + C (k 2) * X 1 ^ 2,
  have : B * (q a₀ a₁ a₂) + A * (c b₀ b₁ b₂ b₃) = 0,
  { simp only [B, q, A, c, smul_eq_C_mul],
    set U : mv_polynomial (fin 2) K := X 0,
    set V : mv_polynomial (fin 2) K := X 1,
    have : vec_mul (C ∘ k) (mat (C a₀) (C a₁) (C a₂) (C b₀) (C b₁) (C b₂) (C b₃))
      = (0 : fin 5 → mv_polynomial (fin 2) K),
    calc vec_mul (C ∘ k) (mat (C a₀) (C a₁) (C a₂) (C b₀) (C b₁) (C b₂) (C b₃))
        = vec_mul (C ∘ k) ((mat a₀ a₁ a₂ b₀ b₁ b₂ b₃).map C) : _
    ... = C ∘ (vec_mul k (mat a₀ a₁ a₂ b₀ b₁ b₂ b₃)) : _
    ... = 0 : _,
    { congr,
      ext1 i j;
      fin_cases i;
      fin_cases j;
      simp only [matrix.map_apply, mat, C.map_zero, cons_val_zero, cons_vec_bit1_eq_alt1,
        cons_vec_bit0_eq_alt0, cons_append, empty_append, cons_vec_alt1, cons_vec_alt0,
        cons_val_one, head_cons], },
    { ext1 i,
      rw ← C.map_vec_mul (mat a₀ a₁ a₂ b₀ b₁ b₂ b₃) k i },
    { simp [mat, habk] },
    rw [← sylvester_mul_rational_normal (C a₀) (C a₁) (C a₂) (C b₀) (C b₁) (C b₂) (C b₃) U V
      (C ∘ k), this],
    simp },
  obtain ⟨x, hx, hx', hxq, hxc⟩ :=
    match_roots_and_pigeonhole (-A) B (q a₀ a₁ a₂) (c b₀ b₁ b₂ b₃) _ _ _ _ _,
  obtain ⟨v, hv, hvx⟩ := linear_has_root hx',
  refine ⟨v, hv, _, _⟩,
  { exact eval_eq_zero_of_dvd hvx hxq },
  { exact eval_eq_zero_of_dvd hvx hxc },
  { sorry }, -- homogeneity
  { sorry }, -- homogeneity
  { sorry }, -- homogeneity
  { sorry }, -- homogeneity
  { linear_combination this },
end

/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Kevin Buzzard
-/

import tactic.basic
import algebra.big_operators.basic
import analysis.inner_product_space.basic
import analysis.normed_space.is_R_or_C

/-!
# Gram-Schmidt Orthogonalization and Orthonormalization

In this file we introduce Gram-Schmidt Orthogonalization and Orthonormalization

## Main results

- `proj` : projection between two vectors in the inner product space
- `GS`   : Gram-Schmidt Process
- `GS_Orthogonal` : the proof that "GS" produces an orthogonal system of vectors
- `GS_unit` : Normalized "Gram-Schmidt" (i.e each vector in this system has unit length)
- `GS_Orthornormal` : the proof that "GS_unit" produces an orthornormal system of vectors
-/

open_locale big_operators

variables (𝕜 : Type*) (E : Type*) [is_R_or_C 𝕜] [inner_product_space 𝕜 E]

/-- projection in the inner product space -/
def proj (u v : E) : E := ((inner u v) / (inner u u) : 𝕜) • u

/-- Definition of Gram-Schmidt Process -/
def GS (f : ℕ → E) : ℕ → E
| n := f n - ∑ i in finset.range(n),
  if h1 : i < n then proj 𝕜 E (GS i) (f n) else f 37

/-- 'GS_n_1' helps us to get rid of 'ite' in the definition of GS -/
@[simp] lemma GS_n_1 (f : ℕ → E) (n : ℕ) :
GS 𝕜 E f (n + 1) = f (n + 1) - ∑ i in finset.range(n + 1), proj 𝕜 E (GS 𝕜 E f i) (f (n + 1)) :=
begin
  rw [GS, sub_right_inj],
  apply finset.sum_congr rfl,
  intros x hx,
  rw finset.mem_range at hx,
  rw if_pos hx,
end

/-- # Gram-Schmidt Orthogonalisation -/
theorem GS_Orthogonal (f : ℕ → E) (c : ℕ) :
∀ (a b : ℕ), a < b → b ≤ c → (inner (GS 𝕜 E f a) (GS 𝕜 E f b) : 𝕜) = 0 :=
begin
  induction c with c hc,
  { intros a b ha hb, simp at hb, simp [hb] at ha, contradiction },
  { intros a b ha hb, rw nat.le_add_one_iff at hb, cases hb with hb₁ hb₂,
    { specialize hc a b, simp [ha, hb₁] at hc, exact hc },
    { simp only [GS_n_1, hb₂, inner_sub_right, inner_sum],
      have h₀ : ∀ x ∈ finset.range(c + 1), x ≠ a
      → (inner (GS 𝕜 E f a) (proj 𝕜 E (GS 𝕜 E f x) (f (c + 1))) : 𝕜) = 0,
      { intros x hx₁ hx₂, simp [proj], rw inner_smul_right,
        have hxa : x < a ∨ a < x := ne.lt_or_lt hx₂, cases hxa with hxa₁ hxa₂,
        { have ha₂ : a ≤ c,
          { rw hb₂ at ha, exact nat.lt_succ_iff.mp ha },
          specialize hc x a, simp [hxa₁, ha₂] at hc,
          simp only [mul_eq_zero, div_eq_zero_iff, inner_self_eq_zero], right,
          rwa inner_eq_zero_sym at hc },
        { rw [finset.mem_range, nat.lt_succ_iff] at hx₁,
          specialize hc a x, simp [hxa₂, hx₁] at hc,
          simp only [mul_eq_zero, div_eq_zero_iff, inner_self_eq_zero], right,
          exact hc }},
      rw hb₂ at ha,
      have ha₂ : a ∈ finset.range(c+1) := finset.mem_range.mpr ha,
      rw finset.sum_eq_single_of_mem a ha₂ h₀, clear h₀,
      simp [proj], rw inner_smul_right,
      by_cases inner (GS 𝕜 E f a) (GS 𝕜 E f a) = (0 : 𝕜),
      { simp [inner_self_eq_zero] at h,
        repeat {rw h}, simp only [inner_zero_left, mul_zero, sub_zero] },
      { simp [h] }}}
end

theorem GS_orthogonal' (f : ℕ → E) :
∀ (a b : ℕ), a < b → (inner (GS 𝕜 E f a) (GS 𝕜 E f b) : 𝕜) = 0 :=
begin
  intros a b h,
  have hb : b ≤ b + 1 := by linarith,
  exact GS_Orthogonal 𝕜 E f (b + 1) a b h hb,
end

/-- Generalised Gram-Schmidt Orthorgonalization -/
theorem GS_orthogonal'' (f : ℕ → E) :
∀ (a b : ℕ), a ≠ b → (inner (GS 𝕜 E f a) (GS 𝕜 E f b) : 𝕜) = 0 :=
begin
  intros a b h,
  have hab : a < b ∨ b < a := ne.lt_or_lt h,
  cases hab with ha hb,
  { exact GS_orthogonal' 𝕜 E f a b ha },
  { rw inner_eq_zero_sym,
    exact GS_orthogonal' 𝕜 E f b a hb }
end

/-- Normalized Gram-Schmidt Process -/
noncomputable def GS_unit (f : ℕ → E) : ℕ → E
| n := (∥ GS 𝕜 E f n ∥ : 𝕜)⁻¹ • (GS 𝕜 E f n)

lemma GS_unit_length (f : ℕ → E) (n : ℕ) (hf : GS 𝕜 E f n ≠ 0) :
∥ GS_unit 𝕜 E f n ∥ = 1 := by simp only [GS_unit, norm_smul_inv_norm hf]

/-- # Gram-Schmidt Orthonormalization -/
theorem GS_Orthonormal (f : ℕ → E) (h : ∀ n, GS 𝕜 E f n ≠ 0) :
orthonormal 𝕜 (GS_unit 𝕜 E f) :=
begin
  simp [orthonormal], split,
  { simp [GS_unit_length, h] },
  { intros i j hij,
    have hij1 : i < j ∨ j < i := ne.lt_or_lt hij,
    cases hij1 with hij2 hij3,
    { simp [GS_unit, inner_smul_left, inner_smul_right], repeat {right},
      have hj : j ≤ j + 1 := by linarith,
      exact GS_Orthogonal 𝕜 E f (j+1) i j hij2 hj },
    { simp [GS_unit, inner_smul_left, inner_smul_right], repeat {right},
      have hi : i ≤ i + 1 := by linarith, rw inner_eq_zero_sym,
      exact GS_Orthogonal 𝕜 E f (i+1) j i hij3 hi }}
end

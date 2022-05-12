/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import analysis.normed.normed_field

/-!
# Seminorms and norms on (semi)rings

In this file we define structures `is_seminorm` and `is_norm` which indicate that a given function
`f : R → ℝ≥0` is a (semi)norm on the (semi)ring `R`. These clases are useful when one needs to
consider multiple (semi)norms on a given ring.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags
is_seminorm, is_norm
-/


noncomputable theory

open_locale topological_space nnreal

/-- A function `f : R → ℝ≥0` is a seminorm if `f 0 = 0` and it satisfies the inequality
  `f (r * s) ≤ f r * f s`. -/
structure is_seminorm {R : Type*} [semiring R] (f : R → ℝ≥0) : Prop :=
(zero : f 0 = 0)
(mul : ∀ r s, f (r * s) ≤ f r * f s)

lemma is_seminorm.pow_le {R : Type*} [semiring R] {f : R → ℝ≥0} (hf : is_seminorm f) (r : R) :
  ∀ {n : ℕ}, 0 < n → f (r ^ n) ≤ (f r) ^ n
| 1 h := by simp only [pow_one]
| (n + 2) h := by simpa [pow_succ _ (n + 1)] using le_trans (hf.mul r _)
    (mul_le_mul_left' (is_seminorm.pow_le n.succ_pos) _)

/-- A function `f : R → ℝ≥0` satisfies `is_norm_le_one_class` if `f 1 ≤ 1`. -/
def is_norm_le_one_class {R : Type*} [semiring R] (f : R → ℝ≥0) : Prop := f 1 ≤ 1

/-- A function `f : R → ℝ≥0` satisfies `is_norm_one_class` if `f 1 = 1`. -/
def is_norm_one_class {R : Type*} [semiring R] (f : R → ℝ≥0) : Prop := f 1 = 1

lemma is_norm_one_class_iff_nontrivial {R : Type*} [semiring R] {f : R → ℝ≥0} (hsn : is_seminorm f)
  (hf1 : f 1 ≤ 1) : is_norm_one_class f ↔ ∃ r : R, f r ≠ 0 :=
begin
  rw is_norm_one_class,
  refine ⟨λ h, _, λ h, _⟩,
  { use 1,
    rw h, exact one_ne_zero, },
  { obtain ⟨x, hx⟩ := h,
    by_cases hf0 : f 1 = 0,
    { have hx' : f x ≤ 0,
      { rw ← mul_one x,
        apply le_trans (hsn.mul x 1) _,
        rw [hf0, mul_zero], },
      exact absurd (le_antisymm hx' (f x).2 ) hx, },
    { have h1 : f 1 * 1 ≤ f 1 * f 1,
      { conv_lhs{ rw ← one_mul (1 : R)},
        convert hsn.mul 1 1,
        rw mul_one, },
      rw mul_le_mul_left (lt_of_le_of_ne (zero_le (f 1)) (ne.symm hf0)) at h1,
      exact le_antisymm hf1 h1, }}
end

/-- A function `f : R → ℝ≥0` is a norm if it is a seminorm and `f x = 0` implies `x = 0`. -/
structure is_norm {R : Type*} [semiring R] (f : R → ℝ≥0) extends (is_seminorm f) : Prop :=
(ne_zero : ∀ r, r ≠ 0 → 0 < f r)

lemma field.is_norm_of_is_seminorm {R : Type*} [field R] {f : R → ℝ≥0} (hf : is_seminorm f)
  (hnt : ∃ r : R, 0 ≠ f r) : is_norm f :=
{ ne_zero := λ x hx, begin
    obtain ⟨c, hc⟩ := hnt,
    have hfx : 0 ≠ f x,
    { intro h0,
      have hc' : f c ≤ 0,
      { rw [← mul_one c, ← mul_inv_cancel hx, ← mul_assoc, mul_comm c, mul_assoc],
        refine le_trans (hf.mul x _) _,
        rw [← h0, zero_mul] },
      exact hc (ge_antisymm hc' (zero_le (f c))), },
    exact lt_of_le_of_ne (zero_le (f _)) hfx,
  end,
  ..hf }

/-- Given a ring `R` with a norm `f` and an `R`-algebra `A`, a function `g : A → ℝ≥0` is an algebra
  norm if it is a norm on `A` and `g ((algebra_map R A r) * a) = f r * g a`. -/
structure is_algebra_norm (R : Type*) [comm_ring R] {f : R → ℝ≥0} (hf : is_norm f)
  {A : Type*} [ring A] [algebra R A] (g : A → ℝ≥0) extends (is_norm g) : Prop :=
(smul : ∀ (r : R) (a : A) , g ((algebra_map R A r) * a) = f r * g a)

/-- A function `f : R → ℝ≥0` is nonarchimedean if it satisfies the inequality
  `f (r + s) ≤ max (f r) (f s)`. -/
def is_nonarchimedean {R : Type*} [ring R] (f : R → ℝ≥0) : Prop :=
∀ r s, f (r + s) ≤ max (f r) (f s)

/-- A function `f : R → ℝ≥0` is power-multiplicative if for all `r ∈ R` and all positive `n ∈ ℕ`,
  `f (r ^ n) = (f r) ^ n`. -/
def is_pow_mul {R : Type*} [ring R] (f : R → ℝ≥0) :=
∀ (r : R) {n : ℕ} (hn : 1 ≤ n), f (r ^ n) = (f r) ^ n

lemma seminormed_ring.to_is_seminorm (R : Type*) [semi_normed_ring R] :
  is_seminorm (λ r : R, (⟨∥r∥, norm_nonneg _⟩ : ℝ≥0)) :=
{ zero   := by simp only [norm_zero, nonneg.mk_eq_zero],
  mul    := by {simp only [nonneg.mk_mul_mk, subtype.mk_le_mk], exact norm_mul_le }}

lemma normed_ring.to_is_norm (R : Type*) [normed_ring R] :
  is_norm (λ r : R, (⟨∥r∥, norm_nonneg _⟩ : ℝ≥0)) :=
{ zero    := by simp only [norm_zero, nonneg.mk_eq_zero],
  mul     := by { simp only [nonneg.mk_mul_mk, subtype.mk_le_mk], exact norm_mul_le },
  ne_zero := λ x hx, by { rw [pos_iff_ne_zero, ne.def, nonneg.mk_eq_zero, norm_eq_zero], exact hx }}

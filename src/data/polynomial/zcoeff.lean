/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.polynomial.div
import data.polynomial.erase_lead
import data.polynomial.degree.lemmas
import algebra.char_p.subring

/-! # ℤ-coefficients of polynomials

Let `R` be a (semi)ring, let `f : R[X]` be a polynomial and let `n : ℤ` be an integer.

This file defines `f.zcoeff n : R`, the coefficient of a polynomial in degree `n : ℤ`,
where we assign coefficient `0` to every negative degree.  Thus, `p.zcoeff n` coincides with
`p.coeff n`, when `0 ≤ n` and equals `0` otherwise. -/

open_locale polynomial

noncomputable theory
namespace polynomial

variables {R : Type*} [semiring R] {a b c d : ℤ} {r : R} {f g h : R[X]}

/--  The coefficient of a polynomial in some degree, where we assign coefficient `0` to every
negative degree.  If `R` is a semiring, `p : R[X]` is a polynomial and `n : ℤ` is an integer,
then `p.zcoeff n` coincides with `p.coeff n`, when `0 ≤ n` and equals `0` otherwise. -/
def zcoeff (f : R[X]) (n : ℤ) : R :=
ite (0 ≤ n) (f.coeff n.to_nat) 0

@[simp] lemma zcoeff_zero_fun : (0 : R[X]).zcoeff = 0 :=
by { funext, simp [zcoeff] }

@[simp] lemma zcoeff_zero : (0 : R[X]).zcoeff a = 0 :=
by simp

@[simp]
lemma zcoeff_add (f g : R[X]) (n : ℤ) :
  (f + g).zcoeff n = f.zcoeff n + g.zcoeff n :=
by simp [zcoeff, ite_add_zero]

@[simp] lemma zcoeff_eq_coeff_of_nonneg {n : ℤ} (n0 : 0 ≤ n) (f : R[X]) :
  f.zcoeff n = f.coeff n.to_nat :=
by simp [zcoeff, n0]

@[simp] lemma zcoeff_eq_coeff (n : ℕ) (f : R[X]) :
  f.zcoeff n = f.coeff n :=
by simp [zcoeff]

@[simp] lemma zcoeff_eq_zero_of_neg {n : ℤ} (n0 : n < 0) (f : R[X]) :
  f.zcoeff n = 0 :=
by simp [zcoeff, not_le.mpr n0]

lemma zcoeff_C (r : R) (n : ℤ) : (C r).zcoeff n = ite (n = 0) r 0 :=
begin
  rcases eq_or_ne n 0 with rfl | n0,
  { simp [zcoeff] },
  { simpa [n0, zcoeff, coeff_C, int.to_nat_eq_zero] using λ h1 h2, (n0 (le_antisymm h2 h1)).elim }
end

@[simp] lemma zcoeff_mul_C (f : R[X]) (r : R) (n : ℤ) :
  (f * C r).zcoeff n = f.zcoeff n * r :=
by simp [zcoeff]

@[simp] lemma zcoeff_mul_X (p : R[X]) (n : ℤ) : (p * X).zcoeff n = p.zcoeff (n - 1) :=
begin
  generalize' nn : n - 1 = n',
  rw sub_eq_iff_eq_add.mp nn,
  unfold zcoeff,
  split_ifs with hn1 hn,
  { lift n' to ℕ using hn,
    simp },
  { rw (show n' = - 1, by linarith),
    simp },
  { exact (hn1 (h.trans (le_add_of_nonneg_right zero_le_one))).elim },
  { refl }
end

@[simp] lemma zcoeff_mul_X_pow (p : R[X]) : ∀ (a : ℕ) (n : ℤ), (p * X ^ a).zcoeff n = p.zcoeff (n - a)
| 0 n       := by simp
| (a + 1) n := by simp [pow_succ', ← mul_assoc, sub_sub, add_comm, *]

lemma zcoeff_eq_zero_of_nat_degree_lt (fn : (f.nat_degree : ℤ) < a) :
  f.zcoeff a = 0 :=
by simpa [zcoeff, (int.coe_nat_nonneg _).trans fn] using
    coeff_eq_zero_of_nat_degree_lt (int.lt_to_nat.mpr fn)

end polynomial

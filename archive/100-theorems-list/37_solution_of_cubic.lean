/-
Copyright (c) 2021 Jeoff Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeoff Lee
-/
import tactic.basic
import data.complex.basic
import algebra.group.defs

/-!
# The Solution of Cubic

This file proves Theorem 37 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

The theorem `cubic_eq_zero_iff` gives solution to the cubic equation over ℂ,
`cubic_eq_zero_iff_of_discrim_eq_zero`
based on the [Cardano's Formula](https://en.wikipedia.org/wiki/Cubic_equation#Cardano's_formula).

## References

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL-ex/Cubic_Quartic.html) was written by Amine Chaieb.

## Tags
polynomial, cubic, root
-/

section

open complex

variables (a b c d : ℂ)
variables {p q r s t : ℂ}


noncomputable def ω : ℂ := ⟨-1/2, (real.sqrt 3)/2⟩

lemma omega_cube_eq_one : ω ^ 3 = 1 :=
begin
  unfold ω,
  have h3 : real.sqrt 3 * real.sqrt 3 = 3,
  { rw [← pow_two (real.sqrt 3), @real.sq_sqrt 3 (by linarith)], },
  rw [pow_succ, pow_succ, pow_one],
  ext,
  iterate 2
  { simp only [mul_re, mul_im],
    rw ← sub_eq_zero,
    field_simp [mul_add, h3],
    ring }
end

lemma omega_sum : 1 + ω + ω^2 = 0 :=
begin
  have : 1 - ω ≠ 0,
  { unfold ω, intro h, rw complex.ext_iff at h, norm_num at h },
  rw [← mul_right_inj' this, mul_zero],
  calc (1 - ω) * (1 + ω + ω^2)
        = 1 - ω^3 : by ring
    ... = 0 : by rw omega_cube_eq_one; norm_num
end

/-- The solution of the monic cubic equation, with 2nd coefficient set to zero. -/
lemma cubic_basic_eq_zero_iff
  (hp_nonzero : p ≠ 0)
  (hr : r^2 = q^2 + p^3)
  (hs3 : s^3 = q + r)
  (ht : t * s = p)
  (x : ℂ) :
    x^3 + 3 * p * x - 2 * q = 0 ↔
      x = s       - t        ∨
      x = s * ω   - t * ω^2  ∨
      x = s * ω^2 - t * ω    :=
begin
  have h₁ : ∀ x a₁ a₂ a₃ : ℂ, x = a₁ ∨ x = a₂ ∨ x = a₃ ↔ (x - a₁) * (x - a₂) * (x - a₃) = 0,
  { intros,
    iterate 2 { rw [mul_eq_zero] },
    iterate 3 { rw [sub_eq_zero] },
    rw or.assoc, },
  rw h₁,
  suffices : x ^ 3 + 3 * p * x - 2 * q
    = (x - (s - t)) * (x - (s * ω - t * ω^2)) * (x - (s * ω^2 - t * ω)),
  { rw this, },
  have hc : s^3 - t^3 = 2 * q,
  { have : s ≠ 0 := λ h, by { apply hp_nonzero, rw [h, mul_zero] at ht, exact ht.symm },
    have h_nonzero: q + r ≠ 0 := by { rw ← hs3, exact pow_ne_zero _ this },
    have hp3 : p^3 = r^2 - q^2 := by rw [hr]; ring,
    calc    s^3 - t^3
          = s^3 - p^3/s^3 : by { rw [← ht], field_simp, ring }
      ... = (q+r) - (r^2-q^2)/(q+r) : by rw [hs3, hp3]
      ... = (q+r) + (q-r) * ((q+r) / (q+r)): by ring
      ... = 2 * q : by rw div_self h_nonzero; ring },
  symmetry,
  calc (x - (s - t)) * (x - (s * ω - t * ω^2)) * (x - (s * ω^2 - t * ω))
      = x^3 - (s-t) * (1+ω+ω^2) * x^2
        + ((s^2+t^2)*ω*(1+ω+ω^2) - s*t*(-3 + 3*(1+ω+ω^2) + ω*(ω^3-1))) * x
        - (s^3-t^3)*ω^3 + s*t*(s-t)*ω^2*(1+ω+ω^2) : by ring
  ... = x^3 + 3*(t*s)*x - (s^3-t^3) : by { rw [omega_sum, omega_cube_eq_one], ring }
  ... = x^3 + 3*p*x - 2*q : by rw [ht, hc]
end

/-- the solution of the monic cubic equation. -/
lemma cubic_monic_eq_zero_iff
  (hp : p = (3 * c - b^2) / 9)
  (hp_nonzero : p ≠ 0)
  (hq :  q = (9 * b * c - 2 * b^3 - 27 * d) / 54)
  (hr : r^2 = q^2 + p^3)
  (hs3 : s^3 = q + r)
  (ht : t * s = p)
  (x : ℂ) :
    x^3 + b * x^2 + c * x + d = 0 ↔
      x = s       - t       - b / 3 ∨
      x = s * ω   - t * ω^2 - b / 3 ∨
      x = s * ω^2 - t * ω   - b / 3 :=
begin
  let y := x + b / 3,
  have h₁ : x^3 + b * x^2 + c * x + d = y^3 + 3 * p * y - 2 * q,
  { dsimp [y],
    rw [hp, hq],
    field_simp, ring, },
  have h₂ := @cubic_basic_eq_zero_iff p q r s t hp_nonzero hr hs3 ht y,
  rw [h₁, h₂],
  dsimp [y],
  have h₃ : ∀ s t : ℂ, x + b / 3 = s - t ↔ x = s - t - b / 3,
  { intros s t, split; intros h,
    { calc x = x + b / 3 - b / 3 : by ring
       ... = s - t - b / 3 : by rw h },
    { rw h, ring } },
  repeat { rw [h₃] } ,
end

/-- **The Solution of Cubic**
  the solution of cubic when p is nonzero. -/
theorem cubic_eq_zero_iff (ha : a ≠ 0)
  (hp : p = (3 * a * c - b^2) / (9 * a^2))
  (hp_nonzero : p ≠ 0)
  (hq : q = (9 * a * b * c - 2 * b^3 - 27 * a^2 * d) / (54 * a^3))
  (hr : r^2 = q^2 + p^3)
  (hs3 : s^3 = q + r)
  (ht : t * s = p)
  (x : ℂ) :
    a * x^3 + b * x^2 + c * x + d = 0 ↔
      x = s       - t       - b / (3 * a) ∨
      x = s * ω   - t * ω^2 - b / (3 * a) ∨
      x = s * ω^2 - t * ω   - b / (3 * a) :=
begin
  have h₁ : a * x^3 + b * x^2 + c * x + d = a * (x^3 + b/a * x^2 + c/a * x + d/a),
  { field_simp, ring },
  have h₂ : ∀ x, a * x = 0 ↔ x = 0, { intros x, simp [ha], },
  have hp' : p = (3 * (c/a) - (b/a) ^ 2) / 9, { field_simp [hp], ring_nf },
  have hq' : q = (9 * (b/a) * (c/a) - 2 * (b/a) ^ 3 - 27 * (d/a)) / 54,
  { field_simp [hq], ring_nf },
  have h₃ := @cubic_monic_eq_zero_iff (b/a) (c/a) (d/a)
    p q r s t hp' hp_nonzero hq' hr hs3 ht x,
  rw [h₁, h₂, h₃],
  have h₄ :=
    calc b / a / 3
       = b / (a * 3) : by { field_simp [ha] }
               ... = b / (3 * a) : by rw mul_comm,
  simp [h₄],
end

/-- the solution of cubic when p equals zero. -/
lemma cubic_eq_zero_iff_of_discrim_eq_zero (ha : a ≠ 0)
  (hpz : 3 * a * c - b^2 = 0)
  (hq : q = (9 * a * b * c - 2 * b^3 - 27 * a^2 * d) / (54 * a^3))
  (hs3 : s^3 = 2 * q)
  (x : ℂ) :
    a * x^3 + b * x^2 + c * x + d = 0 ↔
      x = s       - b / (3 * a) ∨
      x = s * ω   - b / (3 * a) ∨
      x = s * ω^2 - b / (3 * a) :=
begin
  have h₁ : ∀ x a₁ a₂ a₃ : ℂ, x = a₁ ∨ x = a₂ ∨ x = a₃ ↔ (x - a₁) * (x - a₂) * (x - a₃) = 0,
  { intros,
    iterate 2 { rw [mul_eq_zero] },
    iterate 3 { rw [sub_eq_zero] },
    rw or.assoc, },
  have hb2 : b^2 = 3 * a * c, { rw sub_eq_zero at hpz, rw hpz },
  have hb3 : b^3 = 3 * a * b * c, { rw [pow_succ, hb2], ring },
  have h₂ :=
    calc  a * x^3 + b * x^2 + c * x + d
        = a * (x + b/(3*a))^3 + (c - b^2/(3*a)) * x + (d - b^3/(27*a^2))
          : by { field_simp, ring }
    ... = a * (x + b/(3*a))^3 + (d - (9*a*b*c-2*b^3)/(27*a^2))
          : by { simp only [hb2, hb3], field_simp, ring }
    ... = a * ((x + b/(3*a))^3 - s^3)
          : by { rw [hs3, hq], field_simp, ring, },
  have h₃ : ∀ x, a * x = 0 ↔ x = 0, { intro x, simp [ha] },
  rw [h₁, h₂, h₃],
  suffices : ∀ x : ℂ, x^3 - s^3 = (x - s) * (x - s* ω) * (x - s * ω^2),
  { rw this (x + b/(3*a)), ring_nf},
  intro x,
  calc  x^3 - s^3
      = (x - s) * (x^2 + x*s + s^2) : by ring
  ... = (x - s) * (x^2 - (ω+ω^2)*x*s + (1+ω+ω^2)*x*s + s^2) : by ring
  ... = (x - s) * (x^2 - (ω+ω^2)*x*s + ω^3*s^2)
    : by { rw [omega_cube_eq_one, omega_sum], simp }
  ... = (x - s) * (x - s * ω) * (x - s * ω^2) : by ring
end

end

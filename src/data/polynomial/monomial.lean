/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.basic

/-!
# Univariate monomials

Preparatory lemmas for degree_basic.
-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

local attribute [instance, priority 10] is_semiring_hom.comp is_ring_hom.comp

open finsupp finset add_monoid_algebra
open_locale big_operators

namespace polynomial
universes u
variables {R : Type u} {a b : R} {m n : ℕ}

section semiring
variables [semiring R] {p q r : polynomial R}

section C
/-- `C a` is the constant polynomial `a`. -/
def C : R →+* polynomial R := add_monoid_algebra.algebra_map' (ring_hom.id R)

@[simp] lemma monomial_zero_left (a : R) : monomial 0 a = C a := rfl

lemma C_0 : C (0 : R) = 0 := single_zero

lemma C_1 : C (1 : R) = 1 := rfl

lemma C_mul : C (a * b) = C a * C b := C.map_mul a b

lemma C_add : C (a + b) = C a + C b := C.map_add a b

@[simp] lemma C_bit0 : C (bit0 a) = bit0 (C a) := C_add

@[simp] lemma C_bit1 : C (bit1 a) = bit1 (C a) := by simp [bit1, C_bit0]

instance C.is_semiring_hom : is_semiring_hom (C : R → polynomial R) :=
C.is_semiring_hom

lemma C_pow : C (a ^ n) = C a ^ n := C.map_pow a n

@[simp]
lemma C_eq_nat_cast (n : ℕ) : C (n : R) = (n : polynomial R) :=
C.map_nat_cast n

@[simp]
lemma sum_C_index {a} {β} [add_comm_monoid β] {f : ℕ → R → β} (h : f 0 0 = 0) :
  (C a).sum f = f 0 a :=
sum_single_index h
end C

section coeff

@[simp] lemma coeff_X_one : coeff (X : polynomial R) 1 = 1 := coeff_monomial

@[simp] lemma coeff_X_zero : coeff (X : polynomial R) 0 = 0 := coeff_monomial

lemma coeff_X : coeff (X : polynomial R) n = if 1 = n then 1 else 0 := coeff_monomial

lemma coeff_C : coeff (C a) n = ite (n = 0) a 0 :=
by { convert coeff_monomial using 2, simp [eq_comm], }

@[simp] lemma coeff_C_zero : coeff (C a) 0 = a := coeff_monomial

theorem nonzero.of_polynomial_ne (h : p ≠ q) : nontrivial R :=
⟨⟨0, 1, λ h01 : 0 = 1, h $
    by rw [← mul_one p, ← mul_one q, ← C_1, ← h01, C_0, mul_zero, mul_zero] ⟩⟩

lemma single_eq_C_mul_X : ∀{n}, monomial n a = C a * X^n
| 0     := (mul_one _).symm
| (n+1) :=
  calc monomial (n + 1) a = monomial n a * X : by { rw [X, monomial_mul_monomial, mul_one], }
    ... = (C a * X^n) * X : by rw [single_eq_C_mul_X]
    ... = C a * X^(n+1) : by simp only [pow_add, mul_assoc, pow_one]

end coeff

end semiring



section nonzero_semiring

variables [semiring R] [nontrivial R] {p q : polynomial R}
lemma X_ne_zero : (X : polynomial R) ≠ 0 :=
mt (congr_arg (λ p, coeff p 1)) (by simp)

end nonzero_semiring

section ring
variables [ring R]


end ring

end polynomial

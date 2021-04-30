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

namespace polynomial

universes u
variables {R : Type u} {a b : R} {m n : ℕ}
variables [semiring R] {p q r : polynomial R}

/--
`C a` is the constant polynomial `a`.
`C` is provided as a ring homomorphism.
-/
def C : R →+* polynomial R :=
{ map_one' := by simp [monomial_zero_one],
  map_mul' := by simp [monomial_mul_monomial],
  map_zero' := by simp,
  .. monomial 0 }

@[simp] lemma monomial_zero_left (a : R) : monomial 0 a = C a := rfl

lemma C_0 : C (0 : R) = 0 := rfl

lemma C_1 : C (1 : R) = 1 := rfl

lemma C_mul : C (a * b) = C a * C b := C.map_mul a b

lemma C_add : C (a + b) = C a + C b := C.map_add a b

@[simp] lemma C_bit0 : C (bit0 a) = bit0 (C a) := C_add

@[simp] lemma C_bit1 : C (bit1 a) = bit1 (C a) := by simp [bit1, C_bit0]

lemma C_pow : C (a ^ n) = C a ^ n := C.map_pow a n

@[simp] lemma C_mul_monomial : C a * monomial n b = monomial n (a * b) :=
by simp only [←monomial_zero_left, monomial_mul_monomial, zero_add]

@[simp] lemma monomial_mul_C : monomial n a * C b = monomial n (a * b) :=
by simp only [←monomial_zero_left, monomial_mul_monomial, add_zero]

@[simp]
lemma C_eq_nat_cast (n : ℕ) : C (n : R) = (n : polynomial R) :=
C.map_nat_cast n

@[simp]
lemma sum_C_index {a} {β} [add_comm_monoid β] {f : ℕ → R → β} (h : f 0 0 = 0) :
  (C a).sum f = f 0 a :=
sum_monomial_index 0 a f h

lemma coeff_C : coeff (C a) n = ite (n = 0) a 0 :=
by { convert coeff_monomial using 2, simp [eq_comm], }

@[simp] lemma coeff_C_zero : coeff (C a) 0 = a := coeff_monomial

lemma coeff_C_ne_zero (h : n ≠ 0) : (C a).coeff n = 0 :=
by rw [coeff_C, if_neg h]

theorem nontrivial.of_polynomial_ne (h : p ≠ q) : nontrivial R :=
⟨⟨0, 1, λ h01 : 0 = 1, h $
    by rw [← mul_one p, ← mul_one q, ← C_1, ← h01, C_0, mul_zero, mul_zero] ⟩⟩

lemma monomial_eq_C_mul_X : ∀{n}, monomial n a = C a * X^n
| 0     := (mul_one _).symm
| (n+1) :=
  calc monomial (n + 1) a = monomial n a * X : by { rw [X, monomial_mul_monomial, mul_one], }
    ... = (C a * X^n) * X : by rw [monomial_eq_C_mul_X]
    ... = C a * X^(n+1) : by simp only [pow_add, mul_assoc, pow_one]

@[simp] lemma C_inj : C a = C b ↔ a = b :=
⟨λ h, coeff_C_zero.symm.trans (h.symm ▸ coeff_C_zero), congr_arg C⟩

@[simp] lemma C_eq_zero : C a = 0 ↔ a = 0 :=
calc C a = 0 ↔ C a = C 0 : by rw C_0
         ... ↔ a = 0 : C_inj

lemma monomial_one_eq_iff [nontrivial R] {i j : ℕ} :
  (monomial i 1 : polynomial R) = monomial j 1 ↔ i = j :=
by simp [monomial, monomial_fun, finsupp.single_eq_single_iff]

instance [nontrivial R] : infinite (polynomial R) :=
infinite.of_injective (λ i, monomial i 1) $
λ m n h, by simpa [monomial_one_eq_iff] using h

lemma monomial_eq_smul_X {n} : monomial n (a : R) = a • X^n :=
calc monomial n a = monomial n (a * 1) : by simp
  ... = a • monomial n 1 : by simp [monomial, monomial_fun, smul_to_finsupp]
  ... = a • X^n  : by rw X_pow_eq_monomial

lemma card_support_le_one_iff_monomial {f : polynomial R} :
  finset.card f.support ≤ 1 ↔ ∃ n a, f = monomial n a :=
begin
  split,
  { assume H,
    rw finset.card_le_one_iff_subset_singleton at H,
    rcases H with ⟨n, hn⟩,
    refine ⟨n, f.coeff n, _⟩,
    ext i,
    by_cases hi : i = n,
    { simp [hi, coeff_monomial] },
    { have : f.coeff i = 0,
      { rw ← not_mem_support_iff,
        exact λ hi', hi (finset.mem_singleton.1 (hn hi')) },
      simp [this, ne.symm hi, coeff_monomial] } },
  { rintros ⟨n, a, rfl⟩,
    rw ← finset.card_singleton n,
    apply finset.card_le_of_subset,
    exact support_monomial' _ _ }
end

lemma ring_hom_ext {S} [semiring S] {f g : polynomial R →+* S}
  (h₁ : ∀ a, f (C a) = g (C a)) (h₂ : f X = g X) : f = g :=
begin
  set f' := f.comp (to_finsupp_iso R).symm.to_ring_hom with hf',
  set g' := g.comp (to_finsupp_iso R).symm.to_ring_hom with hg',
  have A : f' = g',
  { ext,
    { simp [h₁, ring_equiv.to_ring_hom_eq_coe] },
    { simpa [ring_equiv.to_ring_hom_eq_coe] using h₂, } },
  have B : f = f'.comp (to_finsupp_iso R),
    by { rw [hf', ring_hom.comp_assoc], ext x, simp [ring_equiv.to_ring_hom_eq_coe] },
  have C : g = g'.comp (to_finsupp_iso R),
    by { rw [hg', ring_hom.comp_assoc], ext x, simp [ring_equiv.to_ring_hom_eq_coe] },
  rw [B, C, A]
end

@[ext] lemma ring_hom_ext' {S} [semiring S] {f g : polynomial R →+* S}
  (h₁ : f.comp C = g.comp C) (h₂ : f X = g X) : f = g :=
ring_hom_ext (ring_hom.congr_fun h₁) h₂

end polynomial

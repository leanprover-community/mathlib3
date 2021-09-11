/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.mv_polynomial.basic
import ring_theory.derivation

/-!
# Derivations of multivariate polynomials

In this file we prove that a variation of `mv_polynomial σ R` is defined by its values on all
monomials `mv_polynomial.X i`. We also provide a constructor `mv_polynomial.mk_derivation` that
builds a derivation from its values on `X i`s and a linear equivalence
`mv_polynomial.equiv_derivation` between `σ → A` and `derivation (mv_polynomial σ R) A`. -/

namespace mv_polynomial

open_locale big_operators

noncomputable theory

variables {σ R A : Type*} [comm_ring R] [add_comm_group A]
  [module R A] [module (mv_polynomial σ R) A]

section

variable (R)

def mk_derivationₗ (f : σ → A) :
  mv_polynomial σ R →ₗ[R] A :=
finsupp.lsum R $ λ xs : σ →₀ ℕ, (linear_map.ring_lmap_equiv_self R _ R).symm $
  xs.sum $ λ i k, monomial (xs - finsupp.single i 1) (k : R) • f i

end

variables [is_scalar_tower R (mv_polynomial σ R) A]

lemma leibniz_iff_X
  (f : mv_polynomial σ R →ₗ[R] A) :
  (∀ p q, f (p * q) = p • f q + q • f p) ↔ f 1 = 0 ∧
    (∀ s i, f (monomial s 1 * X i) = (monomial s 1 : mv_polynomial σ R) • f (X i) +
      (X i : mv_polynomial σ R) • f (monomial s 1)) :=
begin
  refine ⟨λ H, ⟨_, λ p i, H _ _⟩, λ H, _⟩,
  { simpa using H 1 1 },
  { have : ∀ p i, f (p * X i) = p • f (X i) + (X i : mv_polynomial σ R) • f p,
    { intros p i,
      induction p using mv_polynomial.induction_on' with s r p q hp hq,
      { rw [← mul_one r, ← C_mul_monomial, mul_assoc, C_mul', f.map_smul, H.2, C_mul', smul_assoc,
          smul_add, f.map_smul, smul_comm r (X i)], apply_instance },
      { rw [add_mul, f.map_add, f.map_add, hp, hq, add_smul, smul_add, add_add_add_comm] } },
    intros p q,
    induction q using mv_polynomial.induction_on,
    case h_C : c {
      rw [mul_comm, C_mul', f.map_smul, C_eq_smul_one, f.map_smul, H.1, smul_one_smul, smul_zero,
        smul_zero, zero_add] },
    case h_add : q₁ q₂ h₁ h₂ {
      simp only [mul_add, f.map_add, h₁, h₂, smul_add, add_smul], abel },
    case h_X : q i hq {
      simp only [this, ← mul_assoc, hq, mul_smul, smul_add, smul_comm (X i), add_assoc] } }
end

@[simp] lemma derivation_C (f : derivation R (mv_polynomial σ R) A) (a : R) : f (C a) = 0 :=
f.map_algebra_map a

@[ext] lemma derivation_ext {f g : derivation R (mv_polynomial σ R) A}
  (h : ∀ i, f (X i) = g (X i)) :
  f = g :=
begin
  apply derivation.to_linear_map_injective, ext s, dsimp,
  induction s using finsupp.induction with i n s hi hn ihs,
  { exact f.map_one_eq_zero.trans g.map_one_eq_zero.symm },
  { simp only [monomial_single_add, ihs, h, derivation.leibniz, derivation.leibniz_pow] }
end

variables {R} [module (mv_polynomial σ R) A] [is_scalar_tower R (mv_polynomial σ R) A]

lemma mk_derivationₗ_monomial (f : σ → A) (s : σ →₀ ℕ) (r : R) :
  mk_derivationₗ R f (monomial s r) =
    r • (s.sum $ λ i k, monomial (s - finsupp.single i 1) (k : R) • f i) :=
sum_monomial_eq $ linear_map.map_zero _

variable (R)

def mk_derivation (f : σ → A) : derivation R (mv_polynomial σ R) A :=
begin
  refine { .. mk_derivationₗ R f, .. },
  refine (leibniz_iff_X (mk_derivationₗ R f)).2 ⟨_, λ s i, _⟩,
  { rw [← C_1, C_apply, mk_derivationₗ_monomial, finsupp.sum_zero_index, smul_zero] },
  { simp only [mk_derivationₗ_monomial, X, monomial_mul, one_smul, one_mul],
    rw [finsupp.sum_add_index];
      [skip, by simp, by { intros, simp only [nat.cast_add, (monomial _).map_add, add_smul] }],
    rw [finsupp.sum_single_index, finsupp.sum_single_index];
      [skip, by simp, by simp],
    rw [finsupp.nat_sub_self, finsupp.nat_add_sub_cancel, nat.cast_one, ← C_apply, C_1, one_smul,
      add_comm, add_right_inj, finsupp.smul_sum],
    refine finset.sum_congr rfl (λ j hj, _), dsimp only,
    rw [smul_smul, monomial_mul, one_mul, add_comm s, finsupp.nat_add_sub_assoc],
    rwa [finsupp.single_le_iff, nat.succ_le_iff, pos_iff_ne_zero, ← finsupp.mem_support_iff] }
end

variable {R}

@[simp] lemma mk_derivation_X (f : σ → A) (i : σ) : mk_derivation R f (X i) = f i :=
begin
  refine (mk_derivationₗ_monomial f _ _).trans _,
  rw [one_smul, finsupp.sum_single_index]; simp
end

variable (R)

def equiv_derivation : (σ → A) ≃ₗ[R] derivation R (mv_polynomial σ R) A :=
linear_equiv.symm $
{ inv_fun := mk_derivation R,
  to_fun := λ D i, D (X i),
  map_add' := λ D₁ D₂, rfl,
  map_smul' := λ c D, rfl,
  left_inv := λ D, derivation_ext $ mk_derivation_X _,
  right_inv := λ f, funext $ mk_derivation_X _ }

end mv_polynomial

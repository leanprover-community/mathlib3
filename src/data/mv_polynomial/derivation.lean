/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.mv_polynomial.supported
import ring_theory.derivation

/-!
# Derivations of multivariate polynomials

In this file we prove that a derivation of `mv_polynomial σ R` is determined by its values on all
monomials `mv_polynomial.X i`. We also provide a constructor `mv_polynomial.mk_derivation` that
builds a derivation from its values on `X i`s and a linear equivalence
`mv_polynomial.equiv_derivation` between `σ → A` and `derivation (mv_polynomial σ R) A`.
-/

namespace mv_polynomial

open_locale big_operators

noncomputable theory

variables {σ R A : Type*} [comm_semiring R] [add_comm_monoid A]
  [module R A] [module (mv_polynomial σ R) A]

section

variable (R)

/-- The derivation on `mv_polynomial σ R` that takes value `f i` on `X i`, as a linear map.
Use `mv_polynomial.mk_derivation` instead. -/
def mk_derivationₗ (f : σ → A) : mv_polynomial σ R →ₗ[R] A :=
finsupp.lsum R $ λ xs : σ →₀ ℕ, (linear_map.ring_lmap_equiv_self R R A).symm $
  xs.sum $ λ i k, monomial (xs - finsupp.single i 1) (k : R) • f i

end

lemma mk_derivationₗ_monomial (f : σ → A) (s : σ →₀ ℕ) (r : R) :
  mk_derivationₗ R f (monomial s r) =
    r • (s.sum $ λ i k, monomial (s - finsupp.single i 1) (k : R) • f i) :=
sum_monomial_eq $ linear_map.map_zero _

lemma mk_derivationₗ_C (f : σ → A) (r : R) : mk_derivationₗ R f (C r) = 0 :=
(mk_derivationₗ_monomial f _ _).trans (smul_zero _)

lemma mk_derivationₗ_X (f : σ → A) (i : σ) : mk_derivationₗ R f (X i) = f i :=
(mk_derivationₗ_monomial f _ _).trans $ by simp

@[simp] lemma derivation_C (D : derivation R (mv_polynomial σ R) A) (a : R) : D (C a) = 0 :=
D.map_algebra_map a

@[simp] lemma derivation_C_mul (D : derivation R (mv_polynomial σ R) A) (a : R)
  (f : mv_polynomial σ R) : D (C a * f) = a • D f :=
by rw [C_mul', D.map_smul]

/-- If two derivations agree on `X i`, `i ∈ s`, then they agree on all polynomials from
`mv_polynomial.supported R s`. -/
lemma derivation_eq_on_supported {D₁ D₂ : derivation R (mv_polynomial σ R) A} {s : set σ}
  (h : set.eq_on (D₁ ∘ X) (D₂ ∘ X) s) {f : mv_polynomial σ R} (hf : f ∈ supported R s) :
  D₁ f = D₂ f :=
derivation.eq_on_adjoin (set.ball_image_iff.2 h) hf

lemma derivation_eq_of_forall_mem_vars {D₁ D₂ : derivation R (mv_polynomial σ R) A}
  {f : mv_polynomial σ R} (h : ∀ i ∈ f.vars, D₁ (X i) = D₂ (X i)) :
  D₁ f = D₂ f :=
derivation_eq_on_supported h f.mem_supported_vars

lemma derivation_eq_zero_of_forall_mem_vars {D : derivation R (mv_polynomial σ R) A}
  {f : mv_polynomial σ R} (h : ∀ i ∈ f.vars, D (X i) = 0) : D f = 0 :=
show D f = (0 : derivation R (mv_polynomial σ R) A) f,
from derivation_eq_of_forall_mem_vars h

@[ext] lemma derivation_ext {D₁ D₂ : derivation R (mv_polynomial σ R) A}
  (h : ∀ i, D₁ (X i) = D₂ (X i)) :
  D₁ = D₂ :=
derivation.ext $ λ f, derivation_eq_of_forall_mem_vars (λ i _, h i)

variables [is_scalar_tower R (mv_polynomial σ R) A]

lemma leibniz_iff_X (D : mv_polynomial σ R →ₗ[R] A) (h₁ : D 1 = 0) :
  (∀ p q, D (p * q) = p • D q + q • D p) ↔
    (∀ s i, D (monomial s 1 * X i) = (monomial s 1 : mv_polynomial σ R) • D (X i) +
      (X i : mv_polynomial σ R) • D (monomial s 1)) :=
begin
  refine ⟨λ H p i, H _ _, λ H, _⟩,
  have hC : ∀ r, D (C r) = 0,
  { intro r, rw [C_eq_smul_one, D.map_smul, h₁, smul_zero] },
  have : ∀ p i, D (p * X i) = p • D (X i) + (X i : mv_polynomial σ R) • D p,
  { intros p i,
    induction p using mv_polynomial.induction_on' with s r p q hp hq,
    { rw [← mul_one r, ← C_mul_monomial, mul_assoc, C_mul', D.map_smul, H, C_mul', smul_assoc,
        smul_add, D.map_smul, smul_comm r (X i)], apply_instance },
    { rw [add_mul, map_add, map_add, hp, hq, add_smul, smul_add, add_add_add_comm] } },
  intros p q,
  induction q using mv_polynomial.induction_on,
  case h_C : c { rw [mul_comm, C_mul', hC, smul_zero, zero_add, D.map_smul,
    C_eq_smul_one, smul_one_smul] },
  case h_add : q₁ q₂ h₁ h₂ { simp only [mul_add, map_add, h₁, h₂, smul_add, add_smul], abel },
  case h_X : q i hq { simp only [this, ← mul_assoc, hq, mul_smul, smul_add, smul_comm (X i),
      add_assoc] }
end

variables (R)

/-- The derivation on `mv_polynomial σ R` that takes value `f i` on `X i`. -/
def mk_derivation (f : σ → A) : derivation R (mv_polynomial σ R) A :=
{ to_linear_map := mk_derivationₗ R f,
  map_one_eq_zero' := mk_derivationₗ_C _ 1,
  leibniz' := (leibniz_iff_X (mk_derivationₗ R f) (mk_derivationₗ_C _ 1)).2 $ λ s i,
    begin
      simp only [mk_derivationₗ_monomial, X, monomial_mul, one_smul, one_mul],
      rw [finsupp.sum_add_index'];
        [skip, by simp, by { intros, simp only [nat.cast_add, (monomial _).map_add, add_smul] }],
      rw [finsupp.sum_single_index, finsupp.sum_single_index]; [skip, by simp, by simp],
      rw [tsub_self, add_tsub_cancel_right, nat.cast_one, ← C_apply, C_1, one_smul,
        add_comm, finsupp.smul_sum],
      refine congr_arg2 (+) rfl (finset.sum_congr rfl (λ j hj, _)), dsimp only,
      rw [smul_smul, monomial_mul, one_mul, add_comm s, add_tsub_assoc_of_le],
      rwa [finsupp.single_le_iff, nat.succ_le_iff, pos_iff_ne_zero, ← finsupp.mem_support_iff]
    end }

@[simp] lemma mk_derivation_X (f : σ → A) (i : σ) : mk_derivation R f (X i) = f i :=
mk_derivationₗ_X f i

lemma mk_derivation_monomial (f : σ → A) (s : σ →₀ ℕ) (r : R) :
  mk_derivation R f (monomial s r) =
    r • (s.sum $ λ i k, monomial (s - finsupp.single i 1) (k : R) • f i) :=
mk_derivationₗ_monomial f s r

/-- `mv_polynomial.mk_derivation` as a linear equivalence. -/
def mk_derivation_equiv : (σ → A) ≃ₗ[R] derivation R (mv_polynomial σ R) A :=
linear_equiv.symm $
{ inv_fun := mk_derivation R,
  to_fun := λ D i, D (X i),
  map_add' := λ D₁ D₂, rfl,
  map_smul' := λ c D, rfl,
  left_inv := λ D, derivation_ext $ mk_derivation_X _ _,
  right_inv := λ f, funext $ mk_derivation_X _ _ }

end mv_polynomial

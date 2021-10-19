/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.coeff

/-!
# Theory of univariate polynomials

The main results are `induction_on` and `as_sum`.
-/

noncomputable theory

open finsupp finset

namespace polynomial
universes u v w x y z
variables {R : Type u} {S : Type v} {T : Type w} {ι : Type x} {k : Type y} {A : Type z}
  {a b : R} {m n : ℕ}

section semiring
variables [semiring R] {p q r : polynomial R}

lemma sum_C_mul_X_eq (p : polynomial R) : p.sum (λn a, C a * X^n) = p :=
begin
  ext n,
  simp only [polynomial.sum, X_pow_eq_monomial, coeff_monomial, mul_one, finset_sum_coeff,
    C_mul_monomial, not_not, mem_support_iff, finset.sum_ite_eq', ite_eq_left_iff],
  exact λ h, h.symm
end

lemma sum_monomial_eq (p : polynomial R) : p.sum (λn a, monomial n a) = p :=
by simp only [monomial_eq_C_mul_X, sum_C_mul_X_eq]

@[elab_as_eliminator] protected lemma induction_on {M : polynomial R → Prop} (p : polynomial R)
  (h_C : ∀a, M (C a))
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_monomial : ∀(n : ℕ) (a : R), M (C a * X^n) → M (C a * X^(n+1))) :
  M p :=
begin
  have A : ∀{n:ℕ} {a}, M (C a * X^n),
  { assume n a,
    induction n with n ih,
    { simp only [pow_zero, mul_one, h_C] },
    { exact h_monomial _ _ ih } },
  have B : ∀ (s : finset ℕ), M (s.sum (λ (n : ℕ), C (p.coeff n) * X ^ n)),
  { apply finset.induction,
    { convert h_C 0, exact C_0.symm },
    { assume n s ns ih, rw sum_insert ns, exact h_add _ _ A ih, } },
  rw [← sum_C_mul_X_eq p, polynomial.sum],
  exact B _
end

/--
To prove something about polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials.
-/
@[elab_as_eliminator] protected lemma induction_on' {M : polynomial R → Prop} (p : polynomial R)
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_monomial : ∀(n : ℕ) (a : R), M (monomial n a)) :
  M p :=
polynomial.induction_on p (h_monomial 0) h_add
(λ n a h, by { rw ← monomial_eq_C_mul_X at ⊢, exact h_monomial _ _ })

section coeff

theorem coeff_mul_monomial (p : polynomial R) (n d : ℕ) (r : R) :
  coeff (p * monomial n r) (d + n) = coeff p d * r :=
by rw [monomial_eq_C_mul_X, ←X_pow_mul, ←mul_assoc, coeff_mul_C, coeff_mul_X_pow]

theorem coeff_monomial_mul (p : polynomial R) (n d : ℕ) (r : R) :
  coeff (monomial n r * p) (d + n) = r * coeff p d :=
by rw [monomial_eq_C_mul_X, mul_assoc, coeff_C_mul, X_pow_mul, coeff_mul_X_pow]

-- This can already be proved by `simp`.
theorem coeff_mul_monomial_zero (p : polynomial R) (d : ℕ) (r : R) :
  coeff (p * monomial 0 r) d = coeff p d * r :=
coeff_mul_monomial p 0 d r

-- This can already be proved by `simp`.
theorem coeff_monomial_zero_mul (p : polynomial R) (d : ℕ) (r : R) :
  coeff (monomial 0 r * p) d = r * coeff p d :=
coeff_monomial_mul p 0 d r

end coeff

open submodule polynomial set
variables {f : polynomial R} {I : submodule (polynomial R) (polynomial R)}

/--  If the coefficients of a polynomial belong to n ideal contains the submodule span of the
coefficients of a polynomial. -/
lemma span_le_of_coeff_mem_C_inverse (cf : ∀ (i : ℕ), f.coeff i ∈ (C ⁻¹' I.carrier)) :
  (span (polynomial R) {g | ∃ i, g = C (f.coeff i)}) ≤ I :=
begin
  refine bInter_subset_of_mem _,
  rintros _ ⟨i, rfl⟩,
  exact set_like.mem_coe.mpr (cf i),
end

lemma mem_span_C_coeff :
  f ∈ span (polynomial R) {g : polynomial R | ∃ i : ℕ, g = (C (coeff f i))} :=
begin
  let p := span (polynomial R) {g : polynomial R | ∃ i : ℕ, g = (C (coeff f i))},
  nth_rewrite 0 (sum_C_mul_X_eq f).symm,
  refine submodule.sum_mem _ (λ n hn, _),
  dsimp,
  have : C (coeff f n) ∈ p, by { apply subset_span, simp },
  have : (monomial n (1 : R)) • C (coeff f n) ∈ p := p.smul_mem _ this,
  convert this using 1,
  simp only [monomial_mul_C, one_mul, smul_eq_mul],
  rw monomial_eq_C_mul_X,
end

lemma exists_coeff_not_mem_C_inverse :
  f ∉ I → ∃ i : ℕ , coeff f i ∉ (C ⁻¹'  I.carrier) :=
imp_of_not_imp_not _ _
  (λ cf, not_not.mpr ((span_le_of_coeff_mem_C_inverse (not_exists_not.mp cf)) mem_span_C_coeff))

end semiring

end polynomial

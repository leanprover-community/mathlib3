/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.coeff
import ring_theory.ideal.basic

/-!
# Induction on polynomials

This file contains lemmas dealing with different flavours of induction on polynomials.
See also `data/polynomial/inductions.lean` (with an `s`!).

The main result is `polynomial.induction_on`.
-/

noncomputable theory

open finsupp finset

namespace polynomial
open_locale polynomial
universes u v w x y z
variables {R : Type u} {S : Type v} {T : Type w} {ι : Type x} {k : Type y} {A : Type z}
  {a b : R} {m n : ℕ}

section semiring
variables [semiring R] {p q r : R[X]}

@[elab_as_eliminator] protected lemma induction_on {M : R[X] → Prop} (p : R[X])
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
@[elab_as_eliminator] protected lemma induction_on' {M : R[X] → Prop} (p : R[X])
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_monomial : ∀(n : ℕ) (a : R), M (monomial n a)) :
  M p :=
polynomial.induction_on p (h_monomial 0) h_add
(λ n a h, by { rw ← monomial_eq_C_mul_X at ⊢, exact h_monomial _ _ })


open submodule polynomial set
variables {f : R[X]} {I : ideal R[X]}

-- TODO: fix whatever this typo from #5693 was supposed to say
/--  If the coefficients of a polynomial belong to n ideal contains the submodule span of the
coefficients of a polynomial. -/
lemma span_le_of_C_coeff_mem (cf : ∀ (i : ℕ), C (f.coeff i) ∈ I) :
  ideal.span {g | ∃ i, g = C (f.coeff i)} ≤ I :=
begin
  simp only [@eq_comm _ _ (C _)] {single_pass := tt},
  exact (ideal.span_le.trans range_subset_iff).mpr cf,
end

lemma mem_span_C_coeff : f ∈ ideal.span {g : R[X] | ∃ i : ℕ, g = C (coeff f i)} :=
begin
  let p := ideal.span {g : R[X] | ∃ i : ℕ, g = C (coeff f i)},
  nth_rewrite 0 (sum_C_mul_X_eq f).symm,
  refine submodule.sum_mem _ (λ n hn, _),
  dsimp,
  have : C (coeff f n) ∈ p, by { apply subset_span, simp },
  have : (monomial n (1 : R)) • C (coeff f n) ∈ p := p.smul_mem _ this,
  convert this using 1,
  simp only [monomial_mul_C, one_mul, smul_eq_mul],
  rw monomial_eq_C_mul_X,
end

lemma exists_C_coeff_not_mem : f ∉ I → ∃ i : ℕ, C (coeff f i) ∉ I :=
not.imp_symm $ λ cf, span_le_of_C_coeff_mem (not_exists_not.mp cf) mem_span_C_coeff

end semiring

end polynomial

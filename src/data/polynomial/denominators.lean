/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.polynomial.erase_lead
/-!
# Denominators of evaluation of polynomials at ratios

Let `i : R → K` be a homomorphism of semirings.  Assume that `K` is commutative.  If `a` and
`b` are elements of `R` such that `i b ∈ K` is invertible, then for any polynomial
`f ∈ polynomial R` the "mathematical" expression `b ^ f.nat_degree * f (a / b) ∈ K` is in
the image of the homomorphism `i`.
-/

open polynomial finset

section clearing_denominators

variables {R K : Type*} [semiring R] [comm_semiring K] {i : R →+* K}
variables {a b : R} {bi : K}
-- TODO: use hypothesis (ub : is_unit (i b)) to work with localizations.

lemma is_integer_eval_zero (N : ℕ) (a b : R) :
  ∃ D : R, i D = i b ^ N * eval (i a * bi) (polynomial.map i 0) :=
⟨0, by simp only [eval_zero, ring_hom.map_zero, mul_zero, map_zero] ⟩

lemma is_integer_eval_C_mul_X_pow (N : ℕ) (a b : R) (bu : bi * i b = 1) :
  ∀ (n : ℕ) (r : R), n ≤ N →
    ∃ D : R,  i D = i b ^ N * eval (i a * bi) (polynomial.map i (C r * X ^ n)) :=
begin
  refine λ n r nN, ⟨r * a ^ n * b ^ (N - n), _⟩,
  rw [C_mul_X_pow_eq_monomial, map_monomial, ← C_mul_X_pow_eq_monomial, eval_mul, eval_pow, eval_C],
  rw [ring_hom.map_mul, ring_hom.map_mul, ring_hom.map_pow, ring_hom.map_pow, eval_X, mul_comm],
  rw [← nat.sub_add_cancel nN] {occs := occurrences.pos [2]},
  rw [pow_add, mul_assoc, mul_comm (i b ^ n), mul_pow, mul_assoc, mul_assoc (i a ^ n), ← mul_pow],
  rw [bu, one_pow, mul_one],
end

lemma is_integer_eval_add (N : ℕ) (a b : R) :
  ∀ (f g : polynomial R),
    (∃ D : R, i D = (i b ^ N * eval (i a * bi) (polynomial.map i f))) →
    (∃ D : R, i D = (i b ^ N * eval (i a * bi) (polynomial.map i g))) →
    (∃ D : R, i D = (i b ^ N * eval (i a * bi) (polynomial.map i (f + g)))) :=
λ f g ⟨Df, Hf⟩ ⟨Dg, Hg⟩,
  ⟨Df + Dg, by rw [ring_hom.map_add, polynomial.map_add, eval_add, mul_add, Hf, Hg] ⟩

lemma exists_integer_eval_div (N : ℕ) (a b : R) {bi : K} (bu : bi * i b = 1) :
  ∀ (f : polynomial R), f.nat_degree ≤ N →
  (∃ D : R, i D = (i b ^ N * eval (i a * bi) (polynomial.map i f))) :=
induction_with_nat_degree_le N (is_integer_eval_zero N a b)
  (λ N_1 r r0, is_integer_eval_C_mul_X_pow N a b bu N_1 r)
  (λ f g fN gN, is_integer_eval_add N a b f g)

/-- If `i : R → K` is a ring homomorphism, `f` is a polynomial with coefficients in `R`,
`a, b` are elements of `R`, with `i b` invertible, then there is a `D ∈ R` such that
`b ^ f.nat_degree * f (a / b)` equals `i D`. -/
theorem is_integer_pow_mul_eval
  (i : R →+* K) (f : polynomial R) (a b : R) (bi : K) (bu : bi * i b = 1) :
  ∃ D : R, i D = (i b ^ f.nat_degree * eval (i a * bi) (polynomial.map i f)) :=
exists_integer_eval_div (f.nat_degree) a b bu f le_rfl

end clearing_denominators

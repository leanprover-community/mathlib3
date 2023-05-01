/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.monoid_algebra.division
import data.mv_polynomial.basic

/-!
# Division of `mv_polynomial` by monomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `mv_polynomial.div_monomial x s`: divides `x` by the monomial `mv_polynomial.monomial 1 s`
* `mv_polynomial.mod_monomial x s`: the remainder upon dividing `x` by the monomial
  `mv_polynomial.monomial 1 s`.

## Main results

* `mv_polynomial.div_monomial_add_mod_monomial`, `mv_polynomial.mod_monomial_add_div_monomial`:
  `div_monomial` and `mod_monomial` are well-behaved as quotient and remainder operators.

## Implementation notes

Where possible, the results in this file should be first proved in the generality of
`add_monoid_algebra`, and then the versions specialized to `mv_polynomial` proved in terms of these.

-/


variables {σ R : Type*} [comm_semiring R]

namespace mv_polynomial

section copied_declarations
/-! Please ensure the declarations in this section are direct translations of `add_monoid_algebra`
results. -/

/-- Divide by `monomial 1 s`, discarding terms not divisible by this. -/
noncomputable def div_monomial (p : mv_polynomial σ R) (s : σ →₀ ℕ) : mv_polynomial σ R :=
add_monoid_algebra.div_of p s

local infix ` /ᵐᵒⁿᵒᵐⁱᵃˡ `:70 := div_monomial

@[simp] lemma coeff_div_monomial (s : σ →₀ ℕ) (x : mv_polynomial σ R) (s' : σ →₀ ℕ) :
  coeff s' (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) = coeff (s + s') x := rfl

@[simp] lemma support_div_monomial (s : σ →₀ ℕ) (x : mv_polynomial σ R)  :
  (x /ᵐᵒⁿᵒᵐⁱᵃˡ s).support = x.support.preimage _ ((add_right_injective s).inj_on _) := rfl

@[simp] lemma zero_div_monomial (s : σ →₀ ℕ) : (0 : mv_polynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
add_monoid_algebra.zero_div_of _

lemma div_monomial_zero (x : mv_polynomial σ R) : x /ᵐᵒⁿᵒᵐⁱᵃˡ 0 = x :=
x.div_of_zero

lemma add_div_monomial (x y : mv_polynomial σ R) (s : σ →₀ ℕ) :
  (x + y) /ᵐᵒⁿᵒᵐⁱᵃˡ s = x /ᵐᵒⁿᵒᵐⁱᵃˡ s + y /ᵐᵒⁿᵒᵐⁱᵃˡ s :=
map_add _ _ _

lemma div_monomial_add (a b : σ →₀ ℕ) (x : mv_polynomial σ R)  :
  x /ᵐᵒⁿᵒᵐⁱᵃˡ (a + b) = (x /ᵐᵒⁿᵒᵐⁱᵃˡ a) /ᵐᵒⁿᵒᵐⁱᵃˡ b :=
x.div_of_add _ _

@[simp] lemma div_monomial_monomial_mul (a : σ →₀ ℕ) (x : mv_polynomial σ R) :
  (monomial a 1 * x) /ᵐᵒⁿᵒᵐⁱᵃˡ a = x :=
x.of'_mul_div_of _

@[simp] lemma div_monomial_mul_monomial (a : σ →₀ ℕ) (x : mv_polynomial σ R) :
  (x * monomial a 1) /ᵐᵒⁿᵒᵐⁱᵃˡ a = x :=
x.mul_of'_div_of _

@[simp] lemma div_monomial_monomial (a : σ →₀ ℕ) :
  (monomial a 1) /ᵐᵒⁿᵒᵐⁱᵃˡ a = (1 : mv_polynomial σ R) :=
add_monoid_algebra.of'_div_of _

/-- The remainder upon division by `monomial 1 s`. -/
noncomputable def mod_monomial (x : mv_polynomial σ R) (s : σ →₀ ℕ) : mv_polynomial σ R :=
x.mod_of s

local infix ` %ᵐᵒⁿᵒᵐⁱᵃˡ `:70 := mod_monomial

@[simp] lemma coeff_mod_monomial_of_not_le {s' s : σ →₀ ℕ} (x : mv_polynomial σ R) (h : ¬s ≤ s') :
  coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s) = coeff s' x :=
x.mod_of_apply_of_not_exists_add s s' begin
  rintro ⟨d, rfl⟩,
  exact h le_self_add,
end

@[simp] lemma coeff_mod_monomial_of_le {s' s : σ →₀ ℕ} (x : mv_polynomial σ R) (h : s ≤ s') :
  coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s) = 0 :=
x.mod_of_apply_of_exists_add _ _ $ exists_add_of_le h

@[simp] lemma monomial_mul_mod_monomial (s : σ →₀ ℕ) (x : mv_polynomial σ R) :
  (monomial s 1 * x) %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
x.of'_mul_mod_of _

@[simp] lemma mul_monomial_mod_monomial (s : σ →₀ ℕ) (x : mv_polynomial σ R):
  (x * monomial s 1) %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
x.mul_of'_mod_of _

@[simp] lemma monomial_mod_monomial (s : σ →₀ ℕ) : (monomial s (1 : R)) %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
add_monoid_algebra.of'_mod_of _

lemma div_monomial_add_mod_monomial (x : mv_polynomial σ R) (s : σ →₀ ℕ) :
  monomial s 1 * (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) + x %ᵐᵒⁿᵒᵐⁱᵃˡ s = x :=
add_monoid_algebra.div_of_add_mod_of x s

lemma mod_monomial_add_div_monomial (x : mv_polynomial σ R) (s : σ →₀ ℕ) :
  x %ᵐᵒⁿᵒᵐⁱᵃˡ s + monomial s 1 * (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) = x :=
add_monoid_algebra.mod_of_add_div_of x s

lemma monomial_one_dvd_iff_mod_monomial_eq_zero {i : σ →₀ ℕ} {x : mv_polynomial σ R} :
  monomial i (1 : R) ∣ x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ i = 0  :=
add_monoid_algebra.of'_dvd_iff_mod_of_eq_zero

end copied_declarations


section X_lemmas

local infix ` /ᵐᵒⁿᵒᵐⁱᵃˡ `:70 := div_monomial
local infix ` %ᵐᵒⁿᵒᵐⁱᵃˡ `:70 := mod_monomial

@[simp] lemma X_mul_div_monomial (i : σ) (x : mv_polynomial σ R) :
   (X i * x) /ᵐᵒⁿᵒᵐⁱᵃˡ (finsupp.single i 1) = x :=
div_monomial_monomial_mul _ _

@[simp] lemma X_div_monomial (i : σ) :
  (X i : mv_polynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ (finsupp.single i 1)  = 1 :=
(div_monomial_monomial (finsupp.single i 1))

@[simp] lemma mul_X_div_monomial (x : mv_polynomial σ R) (i : σ) :
  (x * X i) /ᵐᵒⁿᵒᵐⁱᵃˡ (finsupp.single i 1) = x :=
div_monomial_mul_monomial _ _

@[simp] lemma X_mul_mod_monomial (i : σ) (x : mv_polynomial σ R) :
  (X i * x) %ᵐᵒⁿᵒᵐⁱᵃˡ (finsupp.single i 1)  = 0 :=
monomial_mul_mod_monomial _ _

@[simp] lemma mul_X_mod_monomial (x : mv_polynomial σ R) (i : σ) :
  (x * X i) %ᵐᵒⁿᵒᵐⁱᵃˡ (finsupp.single i 1)  = 0 :=
mul_monomial_mod_monomial _ _

@[simp] lemma mod_monomial_X (i : σ) :
  (X i : mv_polynomial σ R) %ᵐᵒⁿᵒᵐⁱᵃˡ (finsupp.single i 1) = 0 :=
monomial_mod_monomial _

lemma div_monomial_add_mod_monomial_single (x : mv_polynomial σ R) (i : σ) :
  X i * (x /ᵐᵒⁿᵒᵐⁱᵃˡ finsupp.single i 1) + x %ᵐᵒⁿᵒᵐⁱᵃˡ finsupp.single i 1 = x :=
div_monomial_add_mod_monomial _ _

lemma mod_monomial_add_div_monomial_single (x : mv_polynomial σ R) (i : σ) :
  x %ᵐᵒⁿᵒᵐⁱᵃˡ finsupp.single i 1 + X i * (x /ᵐᵒⁿᵒᵐⁱᵃˡ finsupp.single i 1) = x :=
mod_monomial_add_div_monomial _ _

lemma X_dvd_iff_mod_monomial_eq_zero {i : σ} {x : mv_polynomial σ R} :
  X i ∣ x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ finsupp.single i 1 = 0  :=
monomial_one_dvd_iff_mod_monomial_eq_zero

end X_lemmas

/-! ### Some results about dvd (`∣`) on `monomial` and `X` -/

lemma monomial_dvd_monomial {r s : R} {i j : σ →₀ ℕ} :
  monomial i r ∣ monomial j s ↔ (s = 0 ∨ i ≤ j) ∧ r ∣ s :=
begin
  split,
  { rintro ⟨x, hx⟩,
    rw mv_polynomial.ext_iff at hx,
    have hj := hx j,
    have hi := hx i,
    classical,
    simp_rw [coeff_monomial, if_pos] at hj hi,
    simp_rw [coeff_monomial_mul', if_pos] at hi hj,
    split_ifs at hi hj with hi hi,
    { exact ⟨or.inr hi, _, hj⟩ },
    { exact ⟨or.inl hj, hj.symm ▸ dvd_zero _⟩ } },
  { rintro ⟨h | hij, d, rfl⟩,
    { simp_rw [h, monomial_zero, dvd_zero] },
    { refine ⟨monomial (j - i) d, _⟩,
      rw [monomial_mul, add_tsub_cancel_of_le hij] } }
end

@[simp] lemma monomial_one_dvd_monomial_one [nontrivial R] {i j : σ →₀ ℕ} :
  monomial i (1 : R) ∣ monomial j 1 ↔ i ≤ j :=
begin
  rw monomial_dvd_monomial,
  simp_rw [one_ne_zero, false_or, dvd_rfl, and_true],
end

@[simp] lemma X_dvd_X [nontrivial R] {i j : σ} :
  (X i : mv_polynomial σ R) ∣ (X j : mv_polynomial σ R) ↔ i = j :=
begin
  refine monomial_one_dvd_monomial_one.trans _,
  simp_rw [finsupp.single_le_iff, nat.one_le_iff_ne_zero, finsupp.single_apply_ne_zero,
    ne.def, one_ne_zero, not_false_iff, and_true],
end

@[simp] lemma X_dvd_monomial {i : σ} {j : σ →₀ ℕ} {r : R} :
  (X i : mv_polynomial σ R) ∣ monomial j r ↔ (r = 0 ∨ j i ≠ 0) :=
begin
  refine monomial_dvd_monomial.trans _,
  simp_rw [one_dvd, and_true, finsupp.single_le_iff, nat.one_le_iff_ne_zero],
end

end mv_polynomial

/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark.
-/
import data.polynomial
open polynomial finset

/-!
# Polynomials

Eventually, much of data/polynomial.lean should land here.

## Main results

We relate `eval` and the constant coefficient map to `aeval`, so we can use `alg_hom` properties.

We define a `monoid_hom` of type `polynomial R →* R`,
under the assumption that `R` is an integral domain.
- `leading_coeff_hom`
-/

universes u w

noncomputable theory

variables {R : Type u} {α : Type w}

namespace polynomial


section semiring
variables [semiring R]

/-- The second-highest coefficient, or 0 for constants -/
def next_coeff (p : polynomial R) : R :=
if p.nat_degree = 0 then 0 else p.coeff (p.nat_degree - 1)

@[simp]
lemma next_coeff_C_eq_zero (c : R) :
next_coeff (C c) = 0 := by { rw next_coeff, simp }


lemma next_coeff_of_pos_nat_degree (p : polynomial R) (hp : 0 < p.nat_degree) :
  next_coeff p = p.coeff (p.nat_degree - 1) :=
by { rw [next_coeff, if_neg], contrapose! hp, simpa }
end semiring

section ring
variables [ring R]

@[simp]
lemma next_coeff_X_sub_C_eq [nontrivial R]  (c : R) : next_coeff (X - C c) = - c :=
by simp [next_coeff_of_pos_nat_degree]

end ring

section comm_semiring
variables [comm_semiring R]

@[simp] lemma coe_aeval_eq_eval (r : R) :
  (aeval R R r : polynomial R → R) = eval r := rfl

lemma coeff_zero_eq_aeval_zero (p : polynomial R) : p.coeff 0 = aeval R R 0 p :=
by simp [coeff_zero_eq_eval_zero]


lemma pow_comp (p q : polynomial R) (k : ℕ) : (p ^ k).comp q = (p.comp q) ^ k :=
by { unfold comp, rw ← coe_eval₂_ring_hom, apply ring_hom.map_pow }


end comm_semiring

section integral_domain
variable [integral_domain R]

/-- `polynomial.leading_coeff` bundled as a `monoid_hom` when `R` is an `integral_domain`, and thus
  `leading_coeff` is multiplicative -/
def leading_coeff_hom : polynomial R →* R :=
{ to_fun := leading_coeff,
  map_one' := by simp,
  map_mul' := leading_coeff_mul }

@[simp] lemma leading_coeff_hom_apply (p : polynomial R) :
  leading_coeff_hom p = leading_coeff p := rfl

end integral_domain
end polynomial

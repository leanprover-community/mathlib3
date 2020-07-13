/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark.
-/
import data.polynomial
open polynomial finset

/-
# Polynomials
Eventually, much of data/polynomial.lean should land here.
## Main results
- `next_coeff` :
-/

universes u w

variables {R : Type u} {α : Type w}

namespace polynomial

section semiring
variables [semiring R]

/-- The second-highest coefficient, or 0 for constants -/
def next_coeff [semiring R] (p : polynomial R) : R := ite (p.nat_degree = 0) 0 p.coeff (p.nat_degree - 1)

@[simp]
lemma next_coeff_C_eq_zero (c : R) :
next_coeff (C c) = 0 := by {rw next_coeff, simp}

lemma next_coeff_of_pos_nat_degree (p : polynomial R) :
  0 < p.nat_degree → next_coeff p = p.coeff (p.nat_degree - 1) :=
by { intro h, rw next_coeff, rw if_neg, intro contra, rw contra at h, apply lt_irrefl 0 h, }
end semiring

section ring
variables [ring R]

@[simp]
lemma next_coeff_X_sub_C_eq [nontrivial R]  (c : R) : next_coeff (X - C c) = - c :=
by { rw next_coeff_of_pos_nat_degree; simp [nat_degree_X_sub_C] }

end ring

section comm_semiring
variables [comm_semiring R]

lemma pow_comp (p q : polynomial R) (k : ℕ) : (p ^ k).comp q = (p.comp q) ^ k :=
begin
  unfold comp, rw ← coe_eval₂_ring_hom, apply ring_hom.map_pow,
end

/-- `polynomial.eval` bundled as a ring_hom -/
noncomputable def eval_ring_hom : R → (polynomial R →+* R) := eval₂_ring_hom (ring_hom.id R)

@[simp]
lemma coe_eval_ring_hom (r : R) (p : polynomial R) : eval_ring_hom r p = eval r p := rfl

/-- A ring hom returning the constant term -/
noncomputable def coeff_zero_ring_hom : polynomial R →+* R := eval_ring_hom 0

@[simp]
lemma coe_coeff_zero_ring_hom (p : polynomial R) : coeff_zero_ring_hom p = p.coeff 0 :=
by { rw coeff_zero_eq_eval_zero p, refl }


end comm_semiring

section integral_domain

variable [integral_domain R]

/-- `leading_coeff` bundled as a monoid hom-/
noncomputable def leading_coeff_monoid_hom : polynomial R →* R :=
{to_fun := leading_coeff, map_one' := by simp, map_mul' := leading_coeff_mul}

@[simp] lemma coe_leading_coeff_monoid_hom (p : polynomial R) :
  leading_coeff_monoid_hom p = leading_coeff p := rfl

end integral_domain

end polynomial

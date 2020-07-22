/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johan Commelin
-/
import ring_theory.integral_closure
import data.polynomial.field_division

/-!
# Minimal polynomials

This file defines the minimal polynomial of an element x of an A-algebra B,
under the assumption that x is integral over A.

After stating the defining property we specialize to the setting of field extensions
and derive some well-known properties, amongst which the fact that minimal polynomials
are irreducible, and uniquely determined by their defining property.

-/

universes u v w

open_locale classical
open polynomial set function

variables {α : Type u} {β : Type v}

section min_poly_def
variables [comm_ring α] [comm_ring β] [algebra α β]

/-- Let B be an A-algebra, and x an element of B that is integral over A.
The minimal polynomial of x is a monic polynomial of smallest degree that has x as its root. -/
noncomputable def minimal_polynomial {x : β} (hx : is_integral α x) : polynomial α :=
well_founded.min polynomial.degree_lt_wf _ hx

end min_poly_def

namespace minimal_polynomial

section ring
variables [comm_ring α] [comm_ring β] [algebra α β]
variables {x : β} (hx : is_integral α x)

/--A minimal polynomial is monic.-/
lemma monic : monic (minimal_polynomial hx) :=
(well_founded.min_mem degree_lt_wf _ hx).1

/--An element is a root of its minimal polynomial.-/
@[simp] lemma aeval : aeval x (minimal_polynomial hx) = 0 :=
(well_founded.min_mem degree_lt_wf _ hx).2

/--The defining property of the minimal polynomial of an element x:
it is the monic polynomial with smallest degree that has x as its root.-/
lemma min {p : polynomial α} (pmonic : p.monic) (hp : polynomial.aeval x p = 0) :
  degree (minimal_polynomial hx) ≤ degree p :=
le_of_not_lt $ well_founded.not_lt_min degree_lt_wf _ hx ⟨pmonic, hp⟩

end ring

section field
variables [field α] [field β] [algebra α β]
variables {x : β} (hx : is_integral α x)

/--A minimal polynomial is nonzero.-/
lemma ne_zero : (minimal_polynomial hx) ≠ 0 :=
ne_zero_of_monic (monic hx)

/--If an element x is a root of a nonzero polynomial p,
then the degree of p is at least the degree of the minimal polynomial of x.-/
lemma degree_le_of_ne_zero
  {p : polynomial α} (pnz : p ≠ 0) (hp : polynomial.aeval x p = 0) :
  degree (minimal_polynomial hx) ≤ degree p :=
calc degree (minimal_polynomial hx) ≤ degree (p * C (leading_coeff p)⁻¹) :
    min _ (monic_mul_leading_coeff_inv pnz) (by simp [hp])
  ... = degree p : degree_mul_leading_coeff_inv p pnz

/--The minimal polynomial of an element x is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has x as a root,
then this polynomial is equal to the minimal polynomial of x.-/
lemma unique {p : polynomial α} (pmonic : p.monic) (hp : polynomial.aeval x p = 0)
  (pmin : ∀ q : polynomial α, q.monic → polynomial.aeval x q = 0 → degree p ≤ degree q) :
  p = minimal_polynomial hx :=
begin
  symmetry, apply eq_of_sub_eq_zero,
  by_contra hnz,
  have := degree_le_of_ne_zero hx hnz (by simp [hp]),
  contrapose! this,
  apply degree_sub_lt _ (ne_zero hx),
  { rw [(monic hx).leading_coeff, pmonic.leading_coeff] },
  { exact le_antisymm (min hx pmonic hp)
      (pmin (minimal_polynomial hx) (monic hx) (aeval hx)) },
end

/--If an element x is a root of a polynomial p, then the minimal polynomial of x divides p.-/
lemma dvd {p : polynomial α} (hp : polynomial.aeval x p = 0) :
  minimal_polynomial hx ∣ p :=
begin
  rw ← dvd_iff_mod_by_monic_eq_zero (monic hx),
  by_contra hnz,
  have := degree_le_of_ne_zero hx hnz _,
  { contrapose! this,
    exact degree_mod_by_monic_lt _ (monic hx) (ne_zero hx) },
  { rw ← mod_by_monic_add_div p (monic hx) at hp,
    simpa using hp }
end

/--The degree of a minimal polynomial is nonzero.-/
lemma degree_ne_zero : degree (minimal_polynomial hx) ≠ 0 :=
begin
  assume deg_eq_zero,
  have ndeg_eq_zero : nat_degree (minimal_polynomial hx) = 0,
  { simpa using congr_arg nat_degree (eq_C_of_degree_eq_zero deg_eq_zero) },
  have eq_one : minimal_polynomial hx = 1,
  { rw eq_C_of_degree_eq_zero deg_eq_zero, convert C_1,
    simpa [ndeg_eq_zero.symm] using (monic hx).leading_coeff },
  simpa [eq_one, aeval_def] using aeval hx
end

/--A minimal polynomial is not a unit.-/
lemma not_is_unit : ¬ is_unit (minimal_polynomial hx) :=
assume H, degree_ne_zero hx $ degree_eq_zero_of_is_unit H

/--The degree of a minimal polynomial is positive.-/
lemma degree_pos : 0 < degree (minimal_polynomial hx) :=
degree_pos_of_ne_zero_of_nonunit (ne_zero hx) (not_is_unit hx)

/--A minimal polynomial is prime.-/
lemma prime : prime (minimal_polynomial hx) :=
begin
  refine ⟨ne_zero hx, not_is_unit hx, _⟩,
  rintros p q ⟨d, h⟩,
  have :    polynomial.aeval x (p*q) = 0 := by simp [h, aeval hx],
  replace : polynomial.aeval x p = 0 ∨ polynomial.aeval x q = 0 := by simpa,
  cases this; [left, right]; apply dvd; assumption
end

/--A minimal polynomial is irreducible.-/
lemma irreducible : irreducible (minimal_polynomial hx) :=
irreducible_of_prime (prime hx)

/--If L/K is a field extension, and x is an element of L in the image of K,
then the minimal polynomial of x is X - C x.-/
@[simp] protected lemma algebra_map (a : α) (ha : is_integral α (algebra_map α β a)) :
  minimal_polynomial ha = X - C a :=
begin
  refine (unique ha (monic_X_sub_C a) (by simp [aeval_def]) _).symm,
  intros q hq H,
  rw degree_X_sub_C,
  suffices : 0 < degree q,
  { -- This part is annoying and shouldn't be there.
    have q_ne_zero : q ≠ 0,
    { apply polynomial.ne_zero_of_degree_gt this },
    rw degree_eq_nat_degree q_ne_zero at this ⊢,
    rw [← with_bot.coe_zero, with_bot.coe_lt_coe] at this,
    rwa [← with_bot.coe_one, with_bot.coe_le_coe], },
  apply degree_pos_of_root (ne_zero_of_monic hq),
  show is_root q a,
  apply (algebra_map α β).injective,
  rw [(algebra_map α β).map_zero, ← H],
  exact q.hom_eval₂ (ring_hom.id _) (algebra_map α β) _,
end

variable (β)
/--If L/K is a field extension, and x is an element of L in the image of K,
then the minimal polynomial of x is X - C x.-/
lemma algebra_map' (a : α) :
  minimal_polynomial (@is_integral_algebra_map α β _ _ _ a) =
  X - C a :=
minimal_polynomial.algebra_map _ _
variable {β}

/--The minimal polynomial of 0 is X.-/
@[simp] lemma zero {h₀ : is_integral α (0:β)} :
  minimal_polynomial h₀ = X :=
by simpa only [add_zero, polynomial.C_0, sub_eq_add_neg, neg_zero, ring_hom.map_zero]
  using algebra_map' β (0:α)

/--The minimal polynomial of 1 is X - 1.-/
@[simp] lemma one {h₁ : is_integral α (1:β)} :
  minimal_polynomial h₁ = X - 1 :=
by simpa only [ring_hom.map_one, polynomial.C_1, sub_eq_add_neg]
  using algebra_map' β (1:α)

/--If L/K is a field extension and an element y of K is a root of the minimal polynomial
of an element x ∈ L, then y maps to x under the field embedding.-/
lemma root {x : β} (hx : is_integral α x) {y : α}
  (h : is_root (minimal_polynomial hx) y) : algebra_map α β y = x :=
begin
  have ndeg_one : nat_degree (minimal_polynomial hx) = 1,
  { rw ← polynomial.degree_eq_iff_nat_degree_eq_of_pos (nat.zero_lt_one),
    exact degree_eq_one_of_irreducible_of_root (irreducible hx) h },
  have coeff_one : (minimal_polynomial hx).coeff 1 = 1,
  { simpa only [ndeg_one, leading_coeff] using (monic hx).leading_coeff },
  have hy : y = - coeff (minimal_polynomial hx) 0,
  { rw (minimal_polynomial hx).as_sum at h,
    apply eq_neg_of_add_eq_zero,
    simpa only [ndeg_one, coeff_one, C_1, eval_C, eval_X, eval_add, mul_one, one_mul, pow_zero, pow_one,
      is_root.def, finset.sum_range_succ, finset.sum_singleton, finset.range_one] using h, },
  subst y,
  rw [ring_hom.map_neg, neg_eq_iff_add_eq_zero],
  have H := aeval hx,
  rw (minimal_polynomial hx).as_sum at H,
  simpa only [ndeg_one, coeff_one, aeval_def, C_1, eval₂_add, eval₂_C, eval₂_X,
    mul_one, one_mul, pow_one, pow_zero, add_comm,
    finset.sum_range_succ, finset.sum_singleton, finset.range_one] using H,
end

/--The constant coefficient of the minimal polynomial of x is 0
if and only if x = 0.-/
@[simp] lemma coeff_zero_eq_zero : coeff (minimal_polynomial hx) 0 = 0 ↔ x = 0 :=
begin
  split,
  { intro h,
    have zero_root := polynomial.zero_is_root_of_coeff_zero_eq_zero h,
    rw ← root hx zero_root,
    exact ring_hom.map_zero _ },
  { rintro rfl, simp }
end

/--The minimal polynomial of a nonzero element has nonzero constant coefficient.-/
lemma coeff_zero_ne_zero (h : x ≠ 0) : coeff (minimal_polynomial hx) 0 ≠ 0 :=
by { contrapose! h, simpa using h }

end field

end minimal_polynomial

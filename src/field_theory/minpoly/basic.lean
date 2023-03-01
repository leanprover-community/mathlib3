/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johan Commelin
-/
import data.polynomial.field_division
import ring_theory.integral_closure
import ring_theory.polynomial.gauss_lemma

/-!
# Minimal polynomials

This file defines the minimal polynomial of an element `x` of an `A`-algebra `B`,
under the assumption that x is integral over `A`, and derives some basic properties
such as ireducibility under the assumption `B` is a domain.

-/

open_locale classical polynomial
open polynomial set function

variables {A B : Type*}

section min_poly_def
variables (A) [comm_ring A] [ring B] [algebra A B]

/--
Suppose `x : B`, where `B` is an `A`-algebra.

The minimal polynomial `minpoly A x` of `x`
is a monic polynomial with coefficients in `A` of smallest degree that has `x` as its root,
if such exists (`is_integral A x`) or zero otherwise.

For example, if `V` is a `𝕜`-vector space for some field `𝕜` and `f : V →ₗ[𝕜] V` then
the minimal polynomial of `f` is `minpoly 𝕜 f`.
-/
noncomputable def minpoly (x : B) : A[X] :=
if hx : is_integral A x then well_founded.min degree_lt_wf _ hx else 0

end min_poly_def

namespace minpoly

section ring
variables [comm_ring A] [ring B] [algebra A B]
variables {x : B}

/-- A minimal polynomial is monic. -/
lemma monic (hx : is_integral A x) : monic (minpoly A x) :=
by { delta minpoly, rw dif_pos hx, exact (well_founded.min_mem degree_lt_wf _ hx).1 }

/-- A minimal polynomial is nonzero. -/
lemma ne_zero [nontrivial A] (hx : is_integral A x) : minpoly A x ≠ 0 :=
(monic hx).ne_zero

lemma eq_zero (hx : ¬ is_integral A x) : minpoly A x = 0 :=
dif_neg hx

variables (A x)

/-- An element is a root of its minimal polynomial. -/
@[simp] lemma aeval : aeval x (minpoly A x) = 0 :=
begin
  delta minpoly, split_ifs with hx,
  { exact (well_founded.min_mem degree_lt_wf _ hx).2 },
  { exact aeval_zero _ }
end

/-- A minimal polynomial is not `1`. -/
lemma ne_one [nontrivial B] : minpoly A x ≠ 1 :=
begin
  intro h,
  refine (one_ne_zero : (1 : B) ≠ 0) _,
  simpa using congr_arg (polynomial.aeval x) h
end

lemma map_ne_one [nontrivial B] {R : Type*} [semiring R] [nontrivial R] (f : A →+* R) :
  (minpoly A x).map f ≠ 1 :=
begin
  by_cases hx : is_integral A x,
  { exact mt ((monic hx).eq_one_of_map_eq_one f) (ne_one A x) },
  { rw [eq_zero hx, polynomial.map_zero], exact zero_ne_one },
end

/-- A minimal polynomial is not a unit. -/
lemma not_is_unit [nontrivial B] : ¬ is_unit (minpoly A x) :=
begin
  haveI : nontrivial A := (algebra_map A B).domain_nontrivial,
  by_cases hx : is_integral A x,
  { exact mt (monic hx).eq_one_of_is_unit (ne_one A x) },
  { rw [eq_zero hx], exact not_is_unit_zero }
end

lemma mem_range_of_degree_eq_one (hx : (minpoly A x).degree = 1) : x ∈ (algebra_map A B).range :=
begin
  have h : is_integral A x,
  { by_contra h,
    rw [eq_zero h, degree_zero, ←with_bot.coe_one] at hx,
    exact (ne_of_lt (show ⊥ < ↑1, from with_bot.bot_lt_coe 1) hx) },
  have key := minpoly.aeval A x,
  rw [eq_X_add_C_of_degree_eq_one hx, (minpoly.monic h).leading_coeff, C_1, one_mul, aeval_add,
      aeval_C, aeval_X, ←eq_neg_iff_add_eq_zero, ←ring_hom.map_neg] at key,
  exact ⟨-(minpoly A x).coeff 0, key.symm⟩,
end

/-- The defining property of the minimal polynomial of an element `x`:
it is the monic polynomial with smallest degree that has `x` as its root. -/
lemma min {p : A[X]} (pmonic : p.monic) (hp : polynomial.aeval x p = 0) :
  degree (minpoly A x) ≤ degree p :=
begin
  delta minpoly, split_ifs with hx,
  { exact le_of_not_lt (well_founded.not_lt_min degree_lt_wf _ hx ⟨pmonic, hp⟩) },
  { simp only [degree_zero, bot_le] }
end

@[nontriviality] lemma subsingleton [subsingleton B] : minpoly A x = 1 :=
begin
  nontriviality A,
  have := minpoly.min A x monic_one (subsingleton.elim _ _),
  rw degree_one at this,
  cases le_or_lt (minpoly A x).degree 0 with h h,
  { rwa (monic ⟨1, monic_one, by simp⟩ : (minpoly A x).monic).degree_le_zero_iff_eq_one at h },
  { exact (this.not_lt h).elim },
end

end ring

section comm_ring

variables [comm_ring A]

section ring

variables [ring B] [algebra A B] [nontrivial B]
variables {x : B}

/-- The degree of a minimal polynomial, as a natural number, is positive. -/
lemma nat_degree_pos (hx : is_integral A x) : 0 < nat_degree (minpoly A x) :=
begin
  rw pos_iff_ne_zero,
  intro ndeg_eq_zero,
  have eq_one : minpoly A x = 1,
  { rw eq_C_of_nat_degree_eq_zero ndeg_eq_zero, convert C_1,
    simpa only [ndeg_eq_zero.symm] using (monic hx).leading_coeff },
  simpa only [eq_one, alg_hom.map_one, one_ne_zero] using aeval A x
end

/-- The degree of a minimal polynomial is positive. -/
lemma degree_pos (hx : is_integral A x) : 0 < degree (minpoly A x) :=
nat_degree_pos_iff_degree_pos.mp (nat_degree_pos hx)

/-- If `B/A` is an injective ring extension, and `a` is an element of `A`,
then the minimal polynomial of `algebra_map A B a` is `X - C a`. -/
lemma eq_X_sub_C_of_algebra_map_inj
  (a : A) (hf : function.injective (algebra_map A B)) :
  minpoly A (algebra_map A B a) = X - C a :=
begin
  nontriviality A,
  have hdegle : (minpoly A (algebra_map A B a)).nat_degree ≤ 1,
  { apply with_bot.coe_le_coe.1,
    rw [←degree_eq_nat_degree (ne_zero (@is_integral_algebra_map A B _ _ _ a)),
      with_top.coe_one, ←degree_X_sub_C a],
    refine min A (algebra_map A B a) (monic_X_sub_C a) _,
    simp only [aeval_C, aeval_X, alg_hom.map_sub, sub_self] },
  have hdeg : (minpoly A (algebra_map A B a)).degree = 1,
  { apply (degree_eq_iff_nat_degree_eq (ne_zero (@is_integral_algebra_map A B _ _ _ a))).2,
    apply le_antisymm hdegle (nat_degree_pos (@is_integral_algebra_map A B _ _ _ a)) },
  have hrw := eq_X_add_C_of_degree_eq_one hdeg,
  simp only [monic (@is_integral_algebra_map A B _ _ _ a), one_mul,
    monic.leading_coeff, ring_hom.map_one] at hrw,
  have h0 : (minpoly A (algebra_map A B a)).coeff 0 = -a,
  { have hroot := aeval A (algebra_map A B a),
    rw [hrw, add_comm] at hroot,
    simp only [aeval_C, aeval_X, aeval_add] at hroot,
    replace hroot := eq_neg_of_add_eq_zero_left hroot,
    rw [←ring_hom.map_neg _ a] at hroot,
    exact (hf hroot) },
  rw hrw,
  simp only [h0, ring_hom.map_neg, sub_eq_add_neg],
end

end ring

section is_domain

variables [is_domain A] [ring B] [algebra A B]
variables {x : B}

/-- If `a` strictly divides the minimal polynomial of `x`, then `x` cannot be a root for `a`. -/
lemma aeval_ne_zero_of_dvd_not_unit_minpoly {a : A[X]} (hx : is_integral A x)
  (hamonic : a.monic) (hdvd : dvd_not_unit a (minpoly A x)) :
  polynomial.aeval x a ≠ 0 :=
begin
  intro ha,
  refine not_lt_of_ge (minpoly.min A x hamonic ha) _,
  obtain ⟨hzeroa, b, hb_nunit, prod⟩ := hdvd,
  have hbmonic : b.monic,
  { rw monic.def,
    have := monic hx,
    rwa [monic.def, prod, leading_coeff_mul, monic.def.mp hamonic, one_mul] at this },
  have hzerob : b ≠ 0 := hbmonic.ne_zero,
  have degbzero : 0 < b.nat_degree,
  { apply nat.pos_of_ne_zero,
    intro h,
    have h₁ := eq_C_of_nat_degree_eq_zero h,
    rw [←h, ←leading_coeff, monic.def.1 hbmonic, C_1] at h₁,
    rw h₁ at hb_nunit,
    have := is_unit_one,
    contradiction },
  rw [prod, degree_mul, degree_eq_nat_degree hzeroa, degree_eq_nat_degree hzerob],
  exact_mod_cast lt_add_of_pos_right _ degbzero,
end

variables [is_domain B]

/-- A minimal polynomial is irreducible. -/
lemma irreducible (hx : is_integral A x) : irreducible (minpoly A x) :=
begin
  cases irreducible_or_factor (minpoly A x) (not_is_unit A x) with hirr hred,
  { exact hirr },
  exfalso,
  obtain ⟨a, b, ha_nunit, hb_nunit, hab_eq⟩ := hred,
  have coeff_prod : a.leading_coeff * b.leading_coeff = 1,
  { rw [←monic.def.1 (monic hx), ←hab_eq],
    simp only [leading_coeff_mul] },
  have hamonic : (a * C b.leading_coeff).monic,
  { rw monic.def,
    simp only [coeff_prod, leading_coeff_mul, leading_coeff_C] },
  have hbmonic : (b * C a.leading_coeff).monic,
  { rw [monic.def, mul_comm],
    simp only [coeff_prod, leading_coeff_mul, leading_coeff_C] },
  have prod : minpoly A x = (a * C b.leading_coeff) * (b * C a.leading_coeff),
  { symmetry,
    calc a * C b.leading_coeff * (b * C a.leading_coeff)
        = a * b * (C a.leading_coeff * C b.leading_coeff) : by ring
    ... = a * b * (C (a.leading_coeff * b.leading_coeff)) : by simp only [ring_hom.map_mul]
    ... = a * b : by rw [coeff_prod, C_1, mul_one]
    ... = minpoly A x : hab_eq },
  have hzero := aeval A x,
  rw [prod, aeval_mul, mul_eq_zero] at hzero,
  cases hzero,
  { refine aeval_ne_zero_of_dvd_not_unit_minpoly hx hamonic _ hzero,
    exact ⟨hamonic.ne_zero, _, mt is_unit_of_mul_is_unit_left hb_nunit, prod⟩ },
  { refine aeval_ne_zero_of_dvd_not_unit_minpoly hx hbmonic _ hzero,
    rw mul_comm at prod,
    exact ⟨hbmonic.ne_zero, _, mt is_unit_of_mul_is_unit_left ha_nunit, prod⟩ },
end

end is_domain

end comm_ring

end minpoly

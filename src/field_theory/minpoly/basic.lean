/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johan Commelin
-/
import data.polynomial.field_division
import ring_theory.integral_closure

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
if hx : is_integral A x then degree_lt_wf.min _ hx else 0

end min_poly_def

namespace minpoly

section ring
variables [comm_ring A] [ring B] [algebra A B]
variables {x : B}

/-- A minimal polynomial is monic. -/
lemma monic (hx : is_integral A x) : monic (minpoly A x) :=
by { delta minpoly, rw dif_pos hx, exact (degree_lt_wf.min_mem _ hx).1 }

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
  { exact (degree_lt_wf.min_mem _ hx).2 },
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
  { exact le_of_not_lt (degree_lt_wf.not_lt_min _ hx ⟨pmonic, hp⟩) },
  { simp only [degree_zero, bot_le] }
end

lemma unique' {p : A[X]} (hm : p.monic) (hp : polynomial.aeval x p = 0)
  (hl : ∀ q : A[X], degree q < degree p → q = 0 ∨ polynomial.aeval x q ≠ 0) :
  p = minpoly A x :=
begin
  nontriviality A,
  have hx : is_integral A x := ⟨p, hm, hp⟩,
  obtain h | h := hl _ ((minpoly A x).degree_mod_by_monic_lt hm), swap,
  { exact (h $ (aeval_mod_by_monic_eq_self_of_root hm hp).trans $ aeval A x).elim },
  obtain ⟨r, hr⟩ := (dvd_iff_mod_by_monic_eq_zero hm).1 h,
  rw hr, have hlead := congr_arg leading_coeff hr,
  rw [mul_comm, leading_coeff_mul_monic hm, (monic hx).leading_coeff] at hlead,
  have : nat_degree r ≤ 0,
  { have hr0 : r ≠ 0 := by { rintro rfl, exact ne_zero hx (mul_zero p ▸ hr) },
    apply_fun nat_degree at hr,
    rw hm.nat_degree_mul' hr0 at hr,
    apply nat.le_of_add_le_add_left,
    rw add_zero,
    exact hr.symm.trans_le (nat_degree_le_nat_degree $ min A x hm hp) },
  rw [eq_C_of_nat_degree_le_zero this, ← nat.eq_zero_of_le_zero this,
      ← leading_coeff, ← hlead, C_1, mul_one],
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

variables [ring B] [algebra A B]
variables {x : B}

/-- The degree of a minimal polynomial, as a natural number, is positive. -/
lemma nat_degree_pos [nontrivial B] (hx : is_integral A x) : 0 < nat_degree (minpoly A x) :=
begin
  rw pos_iff_ne_zero,
  intro ndeg_eq_zero,
  have eq_one : minpoly A x = 1,
  { rw eq_C_of_nat_degree_eq_zero ndeg_eq_zero, convert C_1,
    simpa only [ndeg_eq_zero.symm] using (monic hx).leading_coeff },
  simpa only [eq_one, alg_hom.map_one, one_ne_zero] using aeval A x
end

/-- The degree of a minimal polynomial is positive. -/
lemma degree_pos [nontrivial B] (hx : is_integral A x) : 0 < degree (minpoly A x) :=
nat_degree_pos_iff_degree_pos.mp (nat_degree_pos hx)

/-- If `B/A` is an injective ring extension, and `a` is an element of `A`,
then the minimal polynomial of `algebra_map A B a` is `X - C a`. -/
lemma eq_X_sub_C_of_algebra_map_inj
  (a : A) (hf : function.injective (algebra_map A B)) :
  minpoly A (algebra_map A B a) = X - C a :=
begin
  nontriviality A,
  refine (unique' A _ (monic_X_sub_C a) _ _).symm,
  { rw [map_sub, aeval_C, aeval_X, sub_self] },
  simp_rw or_iff_not_imp_left,
  intros q hl h0,
  rw [← nat_degree_lt_nat_degree_iff h0, nat_degree_X_sub_C, nat.lt_one_iff] at hl,
  rw eq_C_of_nat_degree_eq_zero hl at h0 ⊢,
  rwa [aeval_C, map_ne_zero_iff _ hf, ← C_ne_zero],
end

end ring

section is_domain

variables [ring B] [algebra A B]
variables {x : B}

/-- If `a` strictly divides the minimal polynomial of `x`, then `x` cannot be a root for `a`. -/
lemma aeval_ne_zero_of_dvd_not_unit_minpoly {a : A[X]} (hx : is_integral A x)
  (hamonic : a.monic) (hdvd : dvd_not_unit a (minpoly A x)) :
  polynomial.aeval x a ≠ 0 :=
begin
  refine λ ha, (min A x hamonic ha).not_lt (degree_lt_degree _),
  obtain ⟨b, c, hu, he⟩ := hdvd,
  have hcm := hamonic.of_mul_monic_left (he.subst $ monic hx),
  rw [he, hamonic.nat_degree_mul hcm],
  apply nat.lt_add_of_zero_lt_left _ _ (lt_of_not_le $ λ h, hu _),
  rw [eq_C_of_nat_degree_le_zero h, ← nat.eq_zero_of_le_zero h,
      ← leading_coeff, hcm.leading_coeff, C_1],
  exact is_unit_one,
end

variables [is_domain A] [is_domain B]

/-- A minimal polynomial is irreducible. -/
lemma irreducible (hx : is_integral A x) : irreducible (minpoly A x) :=
begin
  refine (irreducible_of_monic (monic hx) $ ne_one A x).2 (λ f g hf hg he, _),
  rw [← hf.is_unit_iff, ← hg.is_unit_iff],
  by_contra' h,
  have heval := congr_arg (polynomial.aeval x) he,
  rw [aeval A x, aeval_mul, mul_eq_zero] at heval,
  cases heval,
  { exact aeval_ne_zero_of_dvd_not_unit_minpoly hx hf ⟨hf.ne_zero, g, h.2, he.symm⟩ heval },
  { refine aeval_ne_zero_of_dvd_not_unit_minpoly hx hg ⟨hg.ne_zero, f, h.1, _⟩ heval,
    rw [mul_comm, he] },
end

end is_domain

end comm_ring

end minpoly

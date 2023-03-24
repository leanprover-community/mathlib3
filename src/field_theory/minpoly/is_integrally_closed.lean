/-
Copyright (c) 2019 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Paul Lezeau, Junyan Xu
-/
import data.polynomial.field_division
import ring_theory.adjoin_root
import field_theory.minpoly.field
import ring_theory.polynomial.gauss_lemma

/-!
# Minimal polynomials over a GCD monoid

This file specializes the theory of minpoly to the case of an algebra over a GCD monoid.

## Main results

 * `is_integrally_closed_eq_field_fractions`: For integrally closed domains, the minimal polynomial
    over the ring is the same as the minimal polynomial over the fraction field.

 * `is_integrally_closed_dvd` : For integrally closed domains, the minimal polynomial divides any
    primitive polynomial that has the integral element as root.

 * `is_integrally_closed_unique` : The minimal polynomial of an element `x` is uniquely
    characterized by its defining property: if there is another monic polynomial of minimal degree
    that has `x` as a root, then this polynomial is equal to the minimal polynomial of `x`.

-/

open_locale classical polynomial
open polynomial set function minpoly

namespace minpoly

variables {R S : Type*} [comm_ring R] [comm_ring S] [is_domain R] [algebra R S]

section

variables (K L : Type*) [field K] [algebra R K] [is_fraction_ring R K] [field L] [algebra R L]
 [algebra S L] [algebra K L] [is_scalar_tower R K L] [is_scalar_tower R S L]

variables [is_integrally_closed R]

/-- For integrally closed domains, the minimal polynomial over the ring is the same as the minimal
polynomial over the fraction field. See `minpoly.is_integrally_closed_eq_field_fractions'` if
`S` is already a `K`-algebra. -/
theorem is_integrally_closed_eq_field_fractions [is_domain S] {s : S} (hs : is_integral R s) :
  minpoly K (algebra_map S L s) = (minpoly R s).map (algebra_map R K) :=
begin
  refine (eq_of_irreducible_of_monic _ _ _).symm,
  { exact (polynomial.monic.irreducible_iff_irreducible_map_fraction_map
      (monic hs)).1 (irreducible hs) },
   { rw [aeval_map_algebra_map, aeval_algebra_map_apply, aeval, map_zero] },
  { exact (monic hs).map _ }
end

/-- For integrally closed domains, the minimal polynomial over the ring is the same as the minimal
polynomial over the fraction field. Compared to `minpoly.is_integrally_closed_eq_field_fractions`,
this version is useful if the element is in a ring that is already a `K`-algebra. -/
theorem is_integrally_closed_eq_field_fractions' [is_domain S] [algebra K S] [is_scalar_tower R K S]
  {s : S} (hs : is_integral R s) : minpoly K s = (minpoly R s).map (algebra_map R K) :=
begin
  let L := fraction_ring S,
  rw [← is_integrally_closed_eq_field_fractions K L hs],
  refine minpoly.eq_of_algebra_map_eq (is_fraction_ring.injective S L)
    (is_integral_of_is_scalar_tower hs) rfl
end

end

variables [is_domain S] [no_zero_smul_divisors R S]

variable [is_integrally_closed R]

/-- For integrally closed rings, the minimal polynomial divides any polynomial that has the
  integral element as root. See also `minpoly.dvd` which relaxes the assumptions on `S`
  in exchange for stronger assumptions on `R`. -/
theorem is_integrally_closed_dvd [nontrivial R] {s : S} (hs : is_integral R s) {p : R[X]}
  (hp : polynomial.aeval s p = 0) : minpoly R s ∣ p :=
begin
  let K := fraction_ring R,
    let L := fraction_ring S,
    have : minpoly K (algebra_map S L s) ∣ map (algebra_map R K) (p %ₘ (minpoly R s)),
    { rw [map_mod_by_monic _ (minpoly.monic hs), mod_by_monic_eq_sub_mul_div],
      refine dvd_sub (minpoly.dvd K (algebra_map S L s) _) _,
      rw [← map_aeval_eq_aeval_map, hp, map_zero],
      rw [← is_scalar_tower.algebra_map_eq, ← is_scalar_tower.algebra_map_eq],

      apply dvd_mul_of_dvd_left,
      rw is_integrally_closed_eq_field_fractions K L hs,

      exact monic.map _ (minpoly.monic hs) },
    rw [is_integrally_closed_eq_field_fractions _ _ hs, map_dvd_map (algebra_map R K)
      (is_fraction_ring.injective R K) (minpoly.monic hs)] at this,
    rw [← dvd_iff_mod_by_monic_eq_zero (minpoly.monic hs)],
    refine polynomial.eq_zero_of_dvd_of_degree_lt this
      (degree_mod_by_monic_lt p $ minpoly.monic hs),
      all_goals { apply_instance }
end

theorem is_integrally_closed_dvd_iff [nontrivial R] {s : S} (hs : is_integral R s) (p : R[X]) :
  polynomial.aeval s p = 0 ↔  minpoly R s ∣ p :=
⟨λ hp, is_integrally_closed_dvd hs hp, λ hp, by simpa only [ring_hom.mem_ker, ring_hom.coe_comp,
  coe_eval_ring_hom, coe_map_ring_hom, function.comp_app, eval_map, ← aeval_def] using
    aeval_eq_zero_of_dvd_aeval_eq_zero hp (minpoly.aeval R s)⟩

lemma ker_eval {s : S} (hs : is_integral R s) :
  ((polynomial.aeval s).to_ring_hom : R[X] →+* S).ker = ideal.span ({minpoly R s} : set R[X] ):=
by ext p ; simp_rw [ring_hom.mem_ker, alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom,
  is_integrally_closed_dvd_iff hs, ← ideal.mem_span_singleton]

/-- If an element `x` is a root of a nonzero polynomial `p`, then the degree of `p` is at least the
degree of the minimal polynomial of `x`. See also `minpoly.degree_le_of_ne_zero` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
lemma is_integrally_closed.degree_le_of_ne_zero {s : S} (hs : is_integral R s) {p : R[X]}
  (hp0 : p ≠ 0) (hp : polynomial.aeval s p = 0) : degree (minpoly R s) ≤ degree p :=
begin
  rw [degree_eq_nat_degree (minpoly.ne_zero hs), degree_eq_nat_degree hp0],
  norm_cast,
  exact nat_degree_le_of_dvd ((is_integrally_closed_dvd_iff hs _).mp hp) hp0
end

/-- The minimal polynomial of an element `x` is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has `x` as a root, then this polynomial
is equal to the minimal polynomial of `x`. See also `minpoly.unique` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
lemma is_integrally_closed.minpoly.unique {s : S} {P : R[X]} (hmo : P.monic)
  (hP : polynomial.aeval s P = 0)
  (Pmin : ∀ Q : R[X], Q.monic → polynomial.aeval s Q = 0 → degree P ≤ degree Q) :
  P = minpoly R s :=
begin
  have hs : is_integral R s := ⟨P, hmo, hP⟩,
  symmetry, apply eq_of_sub_eq_zero,
  by_contra hnz,
  have := is_integrally_closed.degree_le_of_ne_zero hs hnz (by simp [hP]),
  contrapose! this,
  refine degree_sub_lt _ (ne_zero hs) _,
  { exact le_antisymm (min R s hmo hP)
      (Pmin (minpoly R s) (monic hs) (aeval R s)) },
  { rw [(monic hs).leading_coeff, hmo.leading_coeff] }
end

theorem prime_of_is_integrally_closed {x : S} (hx : is_integral R x) :
  _root_.prime (minpoly R x) :=
begin
  refine ⟨(minpoly.monic hx).ne_zero, ⟨by by_contra h_contra ;
    exact (ne_of_lt (minpoly.degree_pos hx)) (degree_eq_zero_of_is_unit h_contra).symm,
      λ a b h, or_iff_not_imp_left.mpr (λ h', _)⟩⟩,
  rw ← minpoly.is_integrally_closed_dvd_iff hx at ⊢ h' h,
  rw aeval_mul at h,
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero h' h,
end

section adjoin_root

noncomputable theory

open algebra polynomial adjoin_root

variables {R} {x : S}

lemma to_adjoin.injective (hx : is_integral R x) :
  function.injective (minpoly.to_adjoin R x) :=
begin
  refine (injective_iff_map_eq_zero _).2 (λ P₁ hP₁, _),
  obtain ⟨P, hP⟩ := mk_surjective (minpoly.monic hx) P₁,
  by_cases hPzero : P = 0,
  { simpa [hPzero] using hP.symm },
  rw [← hP, minpoly.to_adjoin_apply', lift_hom_mk,  ← subalgebra.coe_eq_zero,
    aeval_subalgebra_coe, set_like.coe_mk, is_integrally_closed_dvd_iff hx] at hP₁,
  obtain ⟨Q, hQ⟩ := hP₁,
  rw [← hP, hQ, ring_hom.map_mul, mk_self, zero_mul],
end

/-- The algebra isomorphism `adjoin_root (minpoly R x) ≃ₐ[R] adjoin R x` -/
@[simps] def equiv_adjoin (hx : is_integral R x) :
  adjoin_root (minpoly R x) ≃ₐ[R] adjoin R ({x} : set S) :=
alg_equiv.of_bijective (minpoly.to_adjoin R x)
  ⟨minpoly.to_adjoin.injective hx, minpoly.to_adjoin.surjective R x⟩

/-- The `power_basis` of `adjoin R {x}` given by `x`. See `algebra.adjoin.power_basis` for a version
over a field. -/
@[simps] def _root_.algebra.adjoin.power_basis' (hx : is_integral R x) :
  power_basis R (algebra.adjoin R ({x} : set S)) :=
power_basis.map (adjoin_root.power_basis' (minpoly.monic hx)) (minpoly.equiv_adjoin hx)

/-- The power basis given by `x` if `B.gen ∈ adjoin R {x}`. -/
@[simps] noncomputable def _root_.power_basis.of_gen_mem_adjoin' (B : power_basis R S)
  (hint : is_integral R x) (hx : B.gen ∈ adjoin R ({x} : set S)) :
  power_basis R S :=
(algebra.adjoin.power_basis' hint).map $
  (subalgebra.equiv_of_eq _ _ $ power_basis.adjoin_eq_top_of_gen_mem_adjoin hx).trans
  subalgebra.top_equiv

end adjoin_root

end minpoly

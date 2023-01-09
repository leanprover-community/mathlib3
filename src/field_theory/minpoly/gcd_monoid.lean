/-
Copyright (c) 2019 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import data.polynomial.field_division
import ring_theory.adjoin_root
import field_theory.minpoly.field
import ring_theory.polynomial.gauss_lemma

/-!
# Minimal polynomials over a GCD monoid

This file specializes the theory of minpoly to the case of an algebra over a GCD monoid.

## Main results

 * `gcd_domain_eq_field_fractions`: For GCD domains, the minimal polynomial over the ring is the
    same as the minimal polynomial over the fraction field.

 * `gcd_domain_dvd` : For GCD domains, the minimal polynomial divides any primitive polynomial
    that has the integral element as root.

 * `gcd_domain_unique` : The minimal polynomial of an element `x` is uniquely characterized by
    its defining property: if there is another monic polynomial of minimal degree that has `x` as a
    root, then this polynomial is equal to the minimal polynomial of `x`.
-/

open_locale classical polynomial
open polynomial set function minpoly

namespace minpoly

variables {R S : Type*} [comm_ring R] [comm_ring S] [is_domain R] [is_domain S] [algebra R S]

section gcd_domain

variables (K L : Type*) [is_integrally_closed R] [field K] [algebra R K] [is_fraction_ring R K]
  [field L] [algebra S L] [algebra K L] [algebra R L] [is_scalar_tower R K L]
  [is_scalar_tower R S L] {s : S} (hs : is_integral R s)

include hs

/-- For GCD domains, the minimal polynomial over the ring is the same as the minimal polynomial
over the fraction field. See `minpoly.gcd_domain_eq_field_fractions'` if `S` is already a
`K`-algebra. -/
lemma gcd_domain_eq_field_fractions :
  minpoly K (algebra_map S L s) = (minpoly R s).map (algebra_map R K) :=
begin
  refine (eq_of_irreducible_of_monic _ _ _).symm,
  { exact (polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map
      (polynomial.monic.is_primitive (monic hs))).1 (irreducible hs) },
   { rw [aeval_map_algebra_map, aeval_algebra_map_apply, aeval, map_zero] },
  { exact (monic hs).map _ }
end

lemma test {α β : Type} (f : α → β) {a b : α} : a = b → f a = f b :=
begin
  exact congr_arg (λ {a : α}, f a)
end

/- TODO: see if the `no_zero_smul_divisors S L` assumption can be lifted -/
theorem is_integrally_closed.map_minpoly_eq_minpoly_fraction_ring [no_zero_smul_divisors S L] :
  minpoly K (algebra_map S L s) = (map (algebra_map R K) (minpoly R s)) :=
begin
  --the idea of the proof is the following: since the minpoly of `a` over `Frac(R)` divides the
  --minpoly of `a` over `R`, it is itself in `R`. Hence its degree is greater or equal to that of
  --the minpoly of `a` over `R`. But the minpoly of `a` over `Frac(R)` divides the minpoly of a
  --over `R` in `R[X]` so we are done.

  --a few "trivial" preliminary results to set up the proof
  have lem0 : minpoly K (algebra_map S L s) ∣ (map (algebra_map R K) (minpoly R s)),
  { exact (dvd_map_of_is_scalar_tower' K L hs) },

  have lem1 : is_integral K (algebra_map S L s),
  { refine is_integral_map_of_comp_eq_of_is_integral (algebra_map R K) _ _ hs,
    rw [← is_scalar_tower.algebra_map_eq, ← is_scalar_tower.algebra_map_eq] },

  obtain ⟨g, hg⟩ := eq_map_of_dvd (minpoly.monic hs) _ (minpoly.monic lem1) lem0,
  have lem2 : polynomial.aeval s g = 0,
  { have := minpoly.aeval K (algebra_map S L s),
    rw [← hg, ← map_aeval_eq_aeval_map, ← map_zero (algebra_map S L)] at this,
    exact no_zero_smul_divisors.algebra_map_injective S L this,
    rw [← is_scalar_tower.algebra_map_eq, ← is_scalar_tower.algebra_map_eq] },

  have lem3 : g.monic,
  { simpa only [function.injective.monic_map_iff (is_fraction_ring.injective R K), hg]
      using  minpoly.monic lem1 },

  rw [← hg],
  refine congr_arg _ (eq.symm (polynomial.eq_of_monic_of_dvd_of_nat_degree_le lem3
    (minpoly.monic hs) _ _)),
  { rwa [← map_dvd_map _ (is_fraction_ring.injective R K) lem3, hg] },
  { exact nat_degree_le_nat_degree (minpoly.min R s lem3 lem2) },
end

/-- For GCD domains, the minimal polynomial over the ring is the same as the minimal polynomial
over the fraction field. Compared to `minpoly.gcd_domain_eq_field_fractions`, this version is useful
if the element is in a ring that is already a `K`-algebra. -/
lemma gcd_domain_eq_field_fractions' [algebra K S] [is_scalar_tower R K S] :
  minpoly K s = (minpoly R s).map (algebra_map R K) :=
begin
  let L := fraction_ring S,
  rw [← gcd_domain_eq_field_fractions K L hs],
  refine minpoly.eq_of_algebra_map_eq (is_fraction_ring.injective S L)
    (is_integral_of_is_scalar_tower hs) rfl
end

variable [no_zero_smul_divisors R S]


/-- For integrally closed rings, the minimal polynomial divides any polynomial that has the
  integral element as root. See also `minpoly.dvd` which relaxes the assumptions on `S`
  in exchange for stronger assumptions on `R`. -/
theorem is_integrally_closed_dvd [nontrivial R] [is_integrally_closed R] (p : R[X])
  (hs : is_integral R s) : polynomial.aeval s p = 0 ↔ minpoly R s ∣ p :=
begin
  refine ⟨λ hp, _, λ hp, _⟩,

  { have : minpoly (fraction_ring R) (algebra_map S (fraction_ring S) s) ∣
      (map (algebra_map R (fraction_ring R)) (p %ₘ (minpoly R s))),
    { rw [map_mod_by_monic _ (minpoly.monic hs), mod_by_monic_eq_sub_mul_div],
      refine dvd_sub (minpoly.dvd (fraction_ring R) (algebra_map S (fraction_ring S) s) _) _,
      rw [← map_aeval_eq_aeval_map, hp, map_zero],
      rw [← is_scalar_tower.algebra_map_eq, ← is_scalar_tower.algebra_map_eq],

      apply dvd_mul_of_dvd_left,
      rw is_integrally_closed.map_minpoly_eq_minpoly_fraction_ring
        (fraction_ring R) (fraction_ring S) hs,

      exact monic.map _ (minpoly.monic hs) },
    rw [is_integrally_closed.map_minpoly_eq_minpoly_fraction_ring _ _ hs,  map_dvd_map
      (algebra_map R (fraction_ring R)) (is_fraction_ring.injective R (fraction_ring R))
      (minpoly.monic hs)] at this,
    rw [← dvd_iff_mod_by_monic_eq_zero (minpoly.monic hs)],
    refine polynomial.eq_zero_of_dvd_of_degree_lt this
      (degree_mod_by_monic_lt p $ minpoly.monic hs) },

  { simpa only [ring_hom.mem_ker, ring_hom.coe_comp, coe_eval_ring_hom,
      coe_map_ring_hom, function.comp_app, eval_map, ← aeval_def] using
      aeval_eq_zero_of_dvd_aeval_eq_zero hp (minpoly.aeval R s) }
end

lemma ker_eval [is_integrally_closed R] [nontrivial R] {a : S} (ha : is_integral R a) :
    ((polynomial.aeval a).to_ring_hom : R[X] →+* S).ker = ideal.span ({ minpoly R a} : set R[X] ):=
begin
  apply le_antisymm,
  { intros p hp,
    rwa [ring_hom.mem_ker, alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom,
      is_integrally_closed_dvd ha, ← ideal.mem_span_singleton] at hp },
  { intros p hp,
    rwa [ring_hom.mem_ker, alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom,
      is_integrally_closed_dvd ha, ← ideal.mem_span_singleton] }
end

/-- If an element `x` is a root of a nonzero polynomial `p`, then the degree of `p` is at least the
degree of the minimal polynomial of `x`. See also `minpoly.degree_le_of_ne_zero` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
lemma is_integrally_closed.degree_le_of_ne_zero {p : R[X]} (hp0 : p ≠ 0)
   (hp : polynomial.aeval s p = 0) : degree (minpoly R s) ≤ degree p :=
begin
  rw [degree_eq_nat_degree (minpoly.ne_zero hs), degree_eq_nat_degree hp0],
  norm_cast,
  exact nat_degree_le_of_dvd ((is_integrally_closed_dvd _ hs).mp hp) hp0
end

omit hs

/-- The minimal polynomial of an element `x` is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has `x` as a root, then this polynomial
is equal to the minimal polynomial of `x`. See also `minpoly.unique` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
lemma is_integrally_closed.minpoly.unique {P : R[X]} (hmo : P.monic)
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

end gcd_domain

section adjoin_root

noncomputable theory

open algebra polynomial adjoin_root

variables {R} {x : S} [is_integrally_closed R] [no_zero_smul_divisors R S]

lemma to_adjoin.injective (hx : is_integral R x) :
  function.injective (minpoly.to_adjoin R x) :=
begin
  refine (injective_iff_map_eq_zero _).2 (λ P₁ hP₁, _),
  obtain ⟨P, hP⟩ := mk_surjective (minpoly.monic hx) P₁,
  by_cases hPzero : P = 0,
  { simpa [hPzero] using hP.symm },
  rw [← hP, minpoly.to_adjoin_apply', lift_hom_mk,  ← subalgebra.coe_eq_zero,
    aeval_subalgebra_coe, set_like.coe_mk, is_integrally_closed_dvd _ hx] at hP₁,
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
@[simps] def _root_.algebra.adjoin.power_basis' (hx : _root_.is_integral R x) :
  _root_.power_basis R (algebra.adjoin R ({x} : set S)) :=
power_basis.map (adjoin_root.power_basis' (minpoly.monic hx)) (minpoly.equiv_adjoin hx)

/-- The power basis given by `x` if `B.gen ∈ adjoin R {x}`. -/
@[simps] noncomputable def _root_.power_basis.of_gen_mem_adjoin' (B : _root_.power_basis R S)
  (hint : is_integral R x) (hx : B.gen ∈ adjoin R ({x} : set S)) :
  _root_.power_basis R S :=
(algebra.adjoin.power_basis' hint).map $
  (subalgebra.equiv_of_eq _ _ $ power_basis.adjoin_eq_top_of_gen_mem_adjoin hx).trans
  subalgebra.top_equiv

end adjoin_root

end minpoly

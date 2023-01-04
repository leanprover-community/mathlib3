/-
Copyright (c) 2019 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import data.polynomial.field_division
import ring_theory.integral_closure
import ring_theory.polynomial.gauss_lemma
import field_theory.minpoly.field
import ring_theory.adjoin_root

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


section gcd_domain

variables {R S : Type*} (K L : Type*) [comm_ring R] [is_domain R] [normalized_gcd_monoid R]
  [field K] [comm_ring S] [is_domain S] [algebra R K] [is_fraction_ring R K] [algebra R S] [field L]
  [algebra S L] [algebra K L] [algebra R L] [is_scalar_tower R K L] [is_scalar_tower R S L]
  {s : S} (hs : is_integral R s)

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

/-- For GCD domains, the minimal polynomial divides any primitive polynomial that has the integral
element as root. See also `minpoly.dvd` which relaxes the assumptions on `S` in exchange for
stronger assumptions on `R`. -/
lemma gcd_domain_dvd {P : R[X]} (hP : P ≠ 0) (hroot : polynomial.aeval s P = 0) : minpoly R s ∣ P :=
begin
  let K := fraction_ring R,
  let L := fraction_ring S,
  let P₁ := P.prim_part,
  suffices : minpoly R s ∣ P₁,
  { exact dvd_trans this (prim_part_dvd _) },
  apply (is_primitive.dvd_iff_fraction_map_dvd_fraction_map K (monic hs).is_primitive
    P.is_primitive_prim_part).2,
  let y := algebra_map S L s,
  have hy : is_integral R y := hs.algebra_map,
  rw [← gcd_domain_eq_field_fractions K L hs],
  refine dvd _ _ _,
  rw [aeval_map_algebra_map, aeval_algebra_map_apply, aeval_prim_part_eq_zero hP hroot, map_zero]
end

/-- If an element `x` is a root of a nonzero polynomial `p`, then the degree of `p` is at least the
degree of the minimal polynomial of `x`. See also `minpoly.degree_le_of_ne_zero` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
lemma gcd_domain_degree_le_of_ne_zero {p : R[X]} (hp0 : p ≠ 0) (hp : polynomial.aeval s p = 0) :
  degree (minpoly R s) ≤ degree p :=
begin
  rw [degree_eq_nat_degree (minpoly.ne_zero hs), degree_eq_nat_degree hp0],
  norm_cast,
  exact nat_degree_le_of_dvd (gcd_domain_dvd hs hp0 hp) hp0
end

omit hs

/-- The minimal polynomial of an element `x` is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has `x` as a root, then this polynomial
is equal to the minimal polynomial of `x`. See also `minpoly.unique` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
lemma gcd_domain_unique {P : R[X]} (hmo : P.monic) (hP : polynomial.aeval s P = 0)
  (Pmin : ∀ Q : R[X], Q.monic → polynomial.aeval s Q = 0 → degree P ≤ degree Q) :
  P = minpoly R s :=
begin
  have hs : is_integral R s := ⟨P, hmo, hP⟩,
  symmetry, apply eq_of_sub_eq_zero,
  by_contra hnz,
  have := gcd_domain_degree_le_of_ne_zero hs hnz (by simp [hP]),
  contrapose! this,
  refine degree_sub_lt _ (ne_zero hs) _,
  { exact le_antisymm (min R s hmo hP)
      (Pmin (minpoly R s) (monic hs) (aeval R s)) },
  { rw [(monic hs).leading_coeff, hmo.leading_coeff] }
end

end gcd_domain

section adjoin_root

noncomputable theory

variables {R S : Type*} [comm_ring R] [comm_ring S] [algebra R S] (x : S) (R)

open algebra polynomial adjoin_root

/-- The surjective algebra morphism `R[X]/(minpoly R x) → R[x]`.

If `R` is a GCD domain and `x` is integral, this is an isomorphism,
see `adjoin_root.minpoly.equiv_adjoin`. -/
@[simps] def to_adjoin : adjoin_root (minpoly R x) →ₐ[R] adjoin R ({x} : set S) :=
lift_hom _ ⟨x, self_mem_adjoin_singleton R x⟩
  (by simp [← subalgebra.coe_eq_zero, aeval_subalgebra_coe])

variables {R x}

lemma to_adjoin_apply' (a : adjoin_root (minpoly R x)) : to_adjoin R x a =
  lift_hom (minpoly R x) (⟨x, self_mem_adjoin_singleton R x⟩ : adjoin R ({x} : set S))
  (by simp [← subalgebra.coe_eq_zero, aeval_subalgebra_coe]) a := rfl

lemma to_adjoin.apply_X : to_adjoin R x (mk (minpoly R x) X) =
  ⟨x, self_mem_adjoin_singleton R x⟩ :=
by simp

variables (R x)

lemma to_adjoin.surjective : function.surjective (to_adjoin R x) :=
begin
  rw [← range_top_iff_surjective, _root_.eq_top_iff, ← adjoin_adjoin_coe_preimage],
  refine adjoin_le _,
  simp only [alg_hom.coe_range, set.mem_range],
  rintro ⟨y₁, y₂⟩ h,
  refine ⟨mk (minpoly R x) X, by simpa using h.symm⟩
end

variables {R} {x} [is_domain R] [normalized_gcd_monoid R] [is_domain S] [no_zero_smul_divisors R S]

lemma to_adjoin.injective (hx : is_integral R x) :
  function.injective (minpoly.to_adjoin R x) :=
begin
  refine (injective_iff_map_eq_zero _).2 (λ P₁ hP₁, _),
  obtain ⟨P, hP⟩ := mk_surjective (minpoly.monic hx) P₁,
  by_cases hPzero : P = 0,
  { simpa [hPzero] using hP.symm },
  have hPcont : P.content ≠ 0 := λ h, hPzero (content_eq_zero_iff.1 h),
  rw [← hP, minpoly.to_adjoin_apply', lift_hom_mk, ← subalgebra.coe_eq_zero,
    aeval_subalgebra_coe, set_like.coe_mk, P.eq_C_content_mul_prim_part, aeval_mul, aeval_C] at hP₁,
  replace hP₁ := eq_zero_of_ne_zero_of_mul_left_eq_zero
    ((map_ne_zero_iff _ (no_zero_smul_divisors.algebra_map_injective R S)).2 hPcont) hP₁,
  obtain ⟨Q, hQ⟩ := minpoly.gcd_domain_dvd hx P.is_primitive_prim_part.ne_zero hP₁,
  rw [P.eq_C_content_mul_prim_part] at hP,
  simpa [hQ] using hP.symm
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

section temporary

open polynomial localization alg_hom

open_locale polynomial

variables {R S : Type*} [comm_ring R] [comm_ring S]


variables [algebra R S] {a : S} [is_domain S] [is_domain R] {φ : R →+* S} {f : R[X]}
  [no_zero_smul_divisors R S]

theorem algebra_map_minpoly_eq_minpoly [is_integrally_closed R]
  [h : fact (function.injective (algebra_map R S))] (ha : is_integral R a) :
  (map (algebra_map R (fraction_ring R)) (minpoly R a))
    = minpoly (fraction_ring R) (algebra_map S (fraction_ring S) a) :=
begin
  --a few "trivial" preliminary results to set up the proof
  have lem0 : minpoly (fraction_ring R) (algebra_map S (fraction_ring S) a) ∣
    (map (algebra_map R (fraction_ring R)) (minpoly R a)),
  { apply minpoly.dvd (fraction_ring R) (algebra_map S (fraction_ring S) a),
    rw [← map_aeval_eq_aeval_map, minpoly.aeval, map_zero],
    rw [← is_scalar_tower.algebra_map_eq, ← is_scalar_tower.algebra_map_eq] },

  have lem1 : is_integral (fraction_ring R) (algebra_map S (fraction_ring S) a),
  { refine is_integral_map_of_comp_eq_of_is_integral (algebra_map R (fraction_ring R)) _ _ ha,
    rw [← is_scalar_tower.algebra_map_eq, ← is_scalar_tower.algebra_map_eq] },

  obtain ⟨g, hg⟩ := eq_map_of_dvd (minpoly.monic ha) _ (minpoly.monic lem1) lem0,
  have lem2 : aeval a g = 0,
  { have := minpoly.aeval (fraction_ring R) (algebra_map S (fraction_ring S) a),
    rw [← hg, ← map_aeval_eq_aeval_map, ← map_zero (algebra_map S (fraction_ring S))] at this,
    exact is_fraction_ring.injective S (fraction_ring S) this,
    rw [← is_scalar_tower.algebra_map_eq, ← is_scalar_tower.algebra_map_eq] },

  have lem3 : g.monic,
  { suffices : monic (map (algebra_map R (fraction_ring R)) g),
    { rwa ← monic_map_iff_of_injective at this,
      exact is_fraction_ring.injective R (fraction_ring R) },
    rw hg,
    exact minpoly.monic lem1 },

  --the idea of the proof is the following: since the minpoly of `a` over `Frac(R)` divides the
  --minpoly of `a` over `R`, it is itself in `R`. Hence its degree is greater or equal to that of
  --the minpoly of `a` over `R`. But the minpoly of `a` over `Frac(R)` divides the minpoly of a
  --over `R` in `R[X]` so we are done.
  suffices: minpoly R a = g,
  { rw [← hg, this] },
  refine polynomial.eq_of_monic_of_dvd_of_nat_degree_le lem3 (minpoly.monic ha) _ _,

  rwa [← map_dvd_map _ (is_fraction_ring.injective R (fraction_ring R)) lem3, hg],

  exact nat_degree_le_nat_degree (minpoly.min R a lem3 lem2),
end

theorem minpoly.dvd' [h : fact (function.injective (algebra_map R S))] [nontrivial R]
  [is_integrally_closed R] {a : S} (ha : is_integral R a) (p : R[X]) :
  aeval a p = 0 ↔ minpoly R a ∣ p :=
begin
  refine ⟨λ hp, _, λ hp, _⟩,

  { have : minpoly (fraction_ring R) (algebra_map S (fraction_ring S) a) ∣
      (map (algebra_map R (fraction_ring R)) (p %ₘ (minpoly R a))),
    { rw [map_mod_by_monic _ (minpoly.monic ha), mod_by_monic_eq_sub_mul_div],
      refine dvd_sub (minpoly.dvd (fraction_ring R) (algebra_map S (fraction_ring S) a) _) _,
      rw [← map_aeval_eq_aeval_map, hp, map_zero],
      rw [← is_scalar_tower.algebra_map_eq, ← is_scalar_tower.algebra_map_eq],

      apply dvd_mul_of_dvd_left,
      rw algebra_map_minpoly_eq_minpoly ha,

      exact monic.map _ (minpoly.monic ha) },
    rw [← algebra_map_minpoly_eq_minpoly ha, map_dvd_map (algebra_map R (fraction_ring R))
      (is_fraction_ring.injective R (fraction_ring R)) (minpoly.monic ha)] at this,
    rw [← dvd_iff_mod_by_monic_eq_zero (minpoly.monic ha)],
    refine polynomial.eq_zero_of_dvd_of_degree_lt this
      (degree_mod_by_monic_lt p $ minpoly.monic ha) },

  { simpa only [ring_hom.mem_ker, ring_hom.coe_comp, coe_eval_ring_hom,
      coe_map_ring_hom, function.comp_app, eval_map, ← aeval_def] using
      aeval_eq_zero_of_dvd_aeval_eq_zero hp (minpoly.aeval R a) }
end

lemma ker_eval [h : fact (function.injective (algebra_map R S))] [nontrivial R]
  [is_integrally_closed R] (a : S) (ha : is_integral R a) :
    ((aeval a).to_ring_hom : R[X] →+* S).ker = ideal.span ({ minpoly R a} : set R[X] ):=
begin
  apply le_antisymm,
  { intros p hp,
    rwa [ring_hom.mem_ker, to_ring_hom_eq_coe, coe_to_ring_hom, minpoly.dvd' ha,
      ← ideal.mem_span_singleton] at hp },
  { intros p hp,
    rwa [ring_hom.mem_ker, alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom, minpoly.dvd' ha,
      ← ideal.mem_span_singleton] }
end


end temporary

end minpoly

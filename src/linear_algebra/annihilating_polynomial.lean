/-
Copyright (c) 2022 Justin Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Thomas
-/
import data.polynomial
import data.polynomial.ring_division
import data.polynomial.field_division
import ring_theory.principal_ideal_domain
import algebra.module.linear_map
import field_theory.minpoly
import linear_algebra
import ring_theory.ideal.operations
import ring_theory.polynomial_algebra

/-!
# Annihilating Ideal

Given a commutative ring `R` and an `R`-algebra `A`
Every element `a : A` defines
an ideal `polynomial.ann_ideal a ⊆ R[X]`.
Simply put, this is the set of polynomials `p` where
the polynomial evaluation `p(a)` is 0.

## Special case where the ground ring is a field

In the special case that `R` is a field, we use the notation `R = 𝕜`.
Here `𝕜[X]` is a PID, so there is a polynomial `g ∈ polynomial.ann_ideal a`
which generates the ideal. We show that if this generator is
chosen to be monic, then it is the minimal polynomial of `a`,
as defined in `field_theory.minpoly`.

## Special case: endomorphism algebra

Given an `R`-module `M` (`[add_comm_group M] [module R M]`)
there are some common specialiazations which may be more familiar.
* Example 1: `A = M →ₗ[R] M`, the endomorphism algebra of an `R`-module M.
* Example 2: `A = n × n` matrices with entries in `R`.
-/

open_locale polynomial

namespace polynomial

section semiring

variables {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]

variables (R)

/--
The informal notation `p(a)` stand for `polynomial.aeval a p`.
Again informally, the annihilating ideal of `a` is
`{ p ∈ R[X] | p(a) = 0 }`. This is an ideal in `R[X]`.
The formal definition uses the kernel of the aeval map. -/
noncomputable def ann_ideal (a : A) : ideal R[X] :=
(aeval a).to_ring_hom.ker

variables {R}

/-- It is useful to refer to ideal membership sometimes
 and the annihilation condition other times. -/
lemma mem_ann_ideal_iff_aeval_eq_zero (a : A) (p : R[X]) :
  p ∈ ann_ideal R a ↔ aeval a p = 0 :=
iff.rfl

/-- `p ∈ ann_ideal R a` stated using `eval₂`. -/
lemma mem_ann_ideal_of_eval₂_algebra_map_eq_zero (a : A) (p : R[X])
  (h : eval₂ (algebra_map R A) a p = 0) : p ∈ ann_ideal R a :=
begin
  apply (mem_ann_ideal_iff_aeval_eq_zero a p).2,
  rwa aeval_def,
end

end semiring

section field

variables {𝕜 A : Type*} [field 𝕜] [ring A] [algebra 𝕜 A]
variable (𝕜)

open submodule

/-- Since `𝕜[X]` is a principal ideal domain there is a polynomial `g` such that
 `span 𝕜 {g} = ann_ideal a`. This picks some generator.
 We prefer the monic generator of the ideal. -/
noncomputable def ann_ideal_generator (a : A) : 𝕜[X] :=
let g := is_principal.generator $ ann_ideal 𝕜 a
  in (C g.leading_coeff⁻¹) * g

/-- `ann_ideal_generator 𝕜 a` is indeed a generator. -/
lemma span_singleton_ann_ideal_generator (a : A) :
  span 𝕜[X] {ann_ideal_generator 𝕜 a} = ann_ideal 𝕜 a :=
begin
  by_cases (is_principal.generator $ ann_ideal 𝕜 a) = 0,
  { rw ← is_principal.eq_bot_iff_generator_eq_zero at h,
   simp only [ann_ideal_generator, h], simp, rw ← is_principal.eq_bot_iff_generator_eq_zero, },
  { simp only [ann_ideal_generator, ann_ideal, alg_hom.to_ring_hom_eq_coe, ideal.submodule_span_eq],
    rw ideal.span_singleton_mul_left_unit,
    { exact is_principal.span_singleton_generator _ },
    { rw [is_unit_C, is_unit_iff_ne_zero],
      apply inv_ne_zero,
      rw [ne.def, leading_coeff_eq_zero_iff_deg_eq_bot, degree_eq_bot],
      rw [ann_ideal, alg_hom.to_ring_hom_eq_coe] at h,
      apply h, }, },
end

/-- The annihilating ideal generator is a member of the annihilating ideal,
  following submodule.generator_mem -/
lemma ann_ideal_generator_mem (a : A) : ann_ideal_generator 𝕜 a ∈ ann_ideal 𝕜 a :=
let I := ann_ideal 𝕜 a,
    g := submodule.is_principal.generator I in
  I.mul_mem_left (C g.leading_coeff⁻¹) (submodule.is_principal.generator_mem I)

/-- sourced from submodule.mem_iff_eq_smul_generator -/
lemma mem_iff_eq_smul_ann_ideal_generator {p : 𝕜[X]} (a : A) :
  p ∈ ann_ideal 𝕜 a ↔ ∃ s : 𝕜[X], p = s • ann_ideal_generator 𝕜 a :=
by simp_rw [@eq_comm _ p, ← mem_span_singleton, span_singleton_ann_ideal_generator]

/-- sourced from submodule.eq_bot_iff_generator_eq_zero -/
lemma eq_bot_iff_ann_ideal_generator_eq_zero (a : A) :
  ann_ideal 𝕜 a = (⊥ : ideal 𝕜[X]) ↔ ann_ideal_generator 𝕜 a = (0 : 𝕜[X]) :=
begin
  rw ← span_singleton_ann_ideal_generator,
  apply @span_singleton_eq_bot 𝕜[X] 𝕜[X] _ _ _ (ann_ideal_generator 𝕜 a),
end

/-- The generator we chose for the annihilating ideal is monic when the ideal is non-zero. -/
lemma monic_of_ann_ideal_generator (a : A) (hg : (ann_ideal_generator 𝕜 a : 𝕜[X]) ≠ 0) :
  monic (ann_ideal_generator 𝕜 a : 𝕜[X]) :=
begin
  dunfold ann_ideal_generator,
  dsimp *,
  rw mul_comm,
  have hg' : is_principal.generator (ann_ideal 𝕜 a) ≠ 0,
  { unfold ann_ideal_generator at hg, simp at hg, exact hg, },
  apply polynomial.monic_mul_leading_coeff_inv,
  apply hg',
end

/-- We are working toward showing the generator of the annihilating ideal
in the field case is the minimal polynomial. We are going to use a uniqueness
theorem of the minimal polynomial. This is the first condition: it must annihilate
the original element `a : A`. -/
lemma ann_ideal_generator_aeval_eq_zero (a : A) :
  aeval a (ann_ideal_generator 𝕜 a : 𝕜[X]) = 0 :=
begin
  have hg : aeval a (is_principal.generator (ann_ideal 𝕜 a)) = 0,
  { have gen_member := submodule.is_principal.generator_mem (ann_ideal 𝕜 a),
    exact (ring_hom.mem_ker (polynomial.aeval a).to_ring_hom).1 gen_member, },
  rw ann_ideal_generator, simp *,
end

/-- sourced from submodule.is_principal.mem_iff_generator_dvd -/
lemma mem_iff_ann_ideal_generator_dvd (a : A) {x : 𝕜[X]} :
  x ∈ ann_ideal 𝕜 a ↔ ann_ideal_generator 𝕜 a ∣ x :=
(mem_iff_eq_smul_ann_ideal_generator 𝕜 a).trans
 (exists_congr (λ a, by simp only [mul_comm, smul_eq_mul]))

/-- The generator of the annihilating ideal has minimal degree among
 the non-zero members of the annihilating ideal -/
lemma degree_ann_ideal_generator_le_of_mem (a : A) (p : 𝕜[X])
  (hp : p ∈ ann_ideal 𝕜 a) (hpn0 : p ≠ 0) :
  degree (ann_ideal_generator 𝕜 a : 𝕜[X]) ≤ degree p :=
degree_le_of_dvd ((mem_iff_ann_ideal_generator_dvd 𝕜 a).1 hp) hpn0

/-- This is what we have been building to:
The monic generator of the annihilating ideal is the minimal polynomial. -/
lemma minpoly_eq_monic_ann_ideal_generator (a : A) :
  ann_ideal_generator 𝕜 a = minpoly 𝕜 a :=
begin
  by_cases (ann_ideal_generator 𝕜 a) = 0,
  { /- case: generator is zero -/
    rw h, apply eq.symm, apply minpoly.eq_zero, unfold is_integral,
    by_contra hi, cases hi with p hp,
    have hpnz : p ≠ 0, { apply monic.ne_zero hp.left, },
    have hmem : p ∈ ann_ideal 𝕜 a,
    { exact mem_ann_ideal_of_eval₂_algebra_map_eq_zero a p hp.right },
    rw [mem_iff_ann_ideal_generator_dvd 𝕜 a, h] at hmem,
    exact hpnz (eq_zero_of_zero_dvd hmem), },
  { /- case: generator is not zero -/
    /- 3 conditions for a poly being the minpoly -/
    apply minpoly.unique,
  /- 1st condition: the poly is monic -/
  { exact monic_of_ann_ideal_generator 𝕜 a h, },
  /- 2nd condition: the poly annihilates a -/
  { apply ann_ideal_generator_aeval_eq_zero, },
  /- 3rd condition: the poly has minimal degree among annihilators of a -/
  { intros q hqm heval,
    apply degree_ann_ideal_generator_le_of_mem 𝕜 a q _ _,
    exact (mem_ann_ideal_iff_aeval_eq_zero a q).2 heval,
    exact monic.ne_zero hqm, } }
end

end field

end polynomial

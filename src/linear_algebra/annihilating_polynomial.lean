/-
Copyright (c) 2022 Justin Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Thomas
-/
import field_theory.minpoly.field
import ring_theory.principal_ideal_domain

/-!
# Annihilating Ideal

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
there are some common specializations which may be more familiar.
* Example 1: `A = M →ₗ[R] M`, the endomorphism algebra of an `R`-module M.
* Example 2: `A = n × n` matrices with entries in `R`.
-/

open_locale polynomial

namespace polynomial

section semiring

variables {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]

variables (R)

/-- `ann_ideal R a` is the *annihilating ideal* of all `p : R[X]` such that `p(a) = 0`.

The informal notation `p(a)` stand for `polynomial.aeval a p`.
Again informally, the annihilating ideal of `a` is
`{ p ∈ R[X] | p(a) = 0 }`. This is an ideal in `R[X]`.
The formal definition uses the kernel of the aeval map. -/
noncomputable def ann_ideal (a : A) : ideal R[X] :=
((aeval a).to_ring_hom : R[X] →+* A).ker

variables {R}

/-- It is useful to refer to ideal membership sometimes
 and the annihilation condition other times. -/
lemma mem_ann_ideal_iff_aeval_eq_zero {a : A} {p : R[X]} :
  p ∈ ann_ideal R a ↔ aeval a p = 0 :=
iff.rfl

end semiring

section field

variables {𝕜 A : Type*} [field 𝕜] [ring A] [algebra 𝕜 A]
variable (𝕜)

open submodule

/-- `ann_ideal_generator 𝕜 a` is the monic generator of `ann_ideal 𝕜 a`
if one exists, otherwise `0`.

Since `𝕜[X]` is a principal ideal domain there is a polynomial `g` such that
 `span 𝕜 {g} = ann_ideal a`. This picks some generator.
 We prefer the monic generator of the ideal. -/
noncomputable def ann_ideal_generator (a : A) : 𝕜[X] :=
let g := is_principal.generator $ ann_ideal 𝕜 a
  in g * (C g.leading_coeff⁻¹)

section

variables {𝕜}

@[simp] lemma ann_ideal_generator_eq_zero_iff {a : A} :
  ann_ideal_generator 𝕜 a = 0 ↔ ann_ideal 𝕜 a = ⊥ :=
by simp only [ann_ideal_generator, mul_eq_zero, is_principal.eq_bot_iff_generator_eq_zero,
  polynomial.C_eq_zero, inv_eq_zero, polynomial.leading_coeff_eq_zero, or_self]
end

/-- `ann_ideal_generator 𝕜 a` is indeed a generator. -/
@[simp] lemma span_singleton_ann_ideal_generator (a : A) :
  ideal.span {ann_ideal_generator 𝕜 a} = ann_ideal 𝕜 a :=
begin
  by_cases h : ann_ideal_generator 𝕜 a = 0,
  { rw [h, ann_ideal_generator_eq_zero_iff.mp h, set.singleton_zero, ideal.span_zero] },
  { rw [ann_ideal_generator, ideal.span_singleton_mul_right_unit, ideal.span_singleton_generator],
    apply polynomial.is_unit_C.mpr,
    apply is_unit.mk0,
    apply inv_eq_zero.not.mpr,
    apply polynomial.leading_coeff_eq_zero.not.mpr,
    apply (mul_ne_zero_iff.mp h).1 }
end

/-- The annihilating ideal generator is a member of the annihilating ideal. -/
lemma ann_ideal_generator_mem (a : A) : ann_ideal_generator 𝕜 a ∈ ann_ideal 𝕜 a :=
ideal.mul_mem_right _ _ (submodule.is_principal.generator_mem _)

lemma mem_iff_eq_smul_ann_ideal_generator {p : 𝕜[X]} (a : A) :
  p ∈ ann_ideal 𝕜 a ↔ ∃ s : 𝕜[X], p = s • ann_ideal_generator 𝕜 a :=
by simp_rw [@eq_comm _ p, ← mem_span_singleton, ← span_singleton_ann_ideal_generator 𝕜 a,
 ideal.span]

/-- The generator we chose for the annihilating ideal is monic when the ideal is non-zero. -/
lemma monic_ann_ideal_generator (a : A) (hg : ann_ideal_generator 𝕜 a ≠ 0) :
  monic (ann_ideal_generator 𝕜 a) :=
monic_mul_leading_coeff_inv (mul_ne_zero_iff.mp hg).1

/-! We are working toward showing the generator of the annihilating ideal
in the field case is the minimal polynomial. We are going to use a uniqueness
theorem of the minimal polynomial.

This is the first condition: it must annihilate the original element `a : A`. -/
lemma ann_ideal_generator_aeval_eq_zero (a : A) :
  aeval a (ann_ideal_generator 𝕜 a) = 0 :=
mem_ann_ideal_iff_aeval_eq_zero.mp (ann_ideal_generator_mem 𝕜 a)

variables {𝕜}

lemma mem_iff_ann_ideal_generator_dvd {p : 𝕜[X]} {a : A} :
  p ∈ ann_ideal 𝕜 a ↔ ann_ideal_generator 𝕜 a ∣ p :=
by rw [← ideal.mem_span_singleton, span_singleton_ann_ideal_generator]

/-- The generator of the annihilating ideal has minimal degree among
 the non-zero members of the annihilating ideal -/
lemma degree_ann_ideal_generator_le_of_mem (a : A) (p : 𝕜[X])
  (hp : p ∈ ann_ideal 𝕜 a) (hpn0 : p ≠ 0) :
  degree (ann_ideal_generator 𝕜 a) ≤ degree p :=
degree_le_of_dvd (mem_iff_ann_ideal_generator_dvd.1 hp) hpn0

variables (𝕜)

/-- The generator of the annihilating ideal is the minimal polynomial. -/
lemma ann_ideal_generator_eq_minpoly (a : A) :
  ann_ideal_generator 𝕜 a = minpoly 𝕜 a :=
begin
  by_cases h : ann_ideal_generator 𝕜 a = 0,
  { rw [h, minpoly.eq_zero],
    rintro ⟨p, p_monic, (hp : aeval a p = 0)⟩,
    refine p_monic.ne_zero (ideal.mem_bot.mp _),
    simpa only [ann_ideal_generator_eq_zero_iff.mp h]
      using mem_ann_ideal_iff_aeval_eq_zero.mpr hp },
  { exact minpoly.unique _ _
      (monic_ann_ideal_generator _ _ h)
      (ann_ideal_generator_aeval_eq_zero _ _)
      (λ q q_monic hq, (degree_ann_ideal_generator_le_of_mem a q
        (mem_ann_ideal_iff_aeval_eq_zero.mpr hq)
        q_monic.ne_zero)) }
end

/-- If a monic generates the annihilating ideal, it must match our choice
 of the annihilating ideal generator. -/
lemma monic_generator_eq_minpoly (a : A) (p : 𝕜[X])
  (p_monic : p.monic) (p_gen : ideal.span {p} = ann_ideal 𝕜 a) :
  ann_ideal_generator 𝕜 a = p :=
begin
  by_cases h : p = 0,
  { rwa [h, ann_ideal_generator_eq_zero_iff, ← p_gen, ideal.span_singleton_eq_bot.mpr], },
  { rw [← span_singleton_ann_ideal_generator, ideal.span_singleton_eq_span_singleton] at p_gen,
    rw eq_comm,
    apply eq_of_monic_of_associated p_monic _ p_gen,
    { apply monic_ann_ideal_generator _ _ ((associated.ne_zero_iff p_gen).mp h), }, },
end

end field

end polynomial

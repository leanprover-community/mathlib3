/-
Copyright (c) 2022 Justin Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Thomas
-/
import data.polynomial
import ring_theory.principal_ideal_domain
import algebra.module.linear_map
import field_theory.minpoly
import linear_algebra
import ring_theory.ideal.operations
import ring_theory.polynomial_algebra

/-!
# Annihilating Ideal in general case and a specialization where the minimal polynomial generates

Given a commutative ring `A` and an `A`-module `M`
(`[comm_ring A] [add_comm_group M] [module A M]`)
Every `A`-linear endomorphism `u: M →ₗ[A] M` defines
an ideal (`alg_hom.annihilating_ideal u ⊆ A[X]`.
Simply put, this is the set of polynomials `p` where
the endomporphism `p(u): M →ₗ[A] M` is the constant 0.

In the special case that `A` is a field, we use the notation `A = 𝕜`.
Here `𝕜[X]` is a PID, so there is a polynomial `g ∈ alg_hom.annihilating_ideal u`
which generates the ideal. We show that if this generator is
chosen to be monic, then it is the minimal polynomial of `u`,
as defined in `field_theory.minpoly`.
-/

variables {A M B : Type*}

variables [comm_ring A] [add_comm_group M] [module A M]

/-
First we make sense of the informal notation `p(u)`.
Think of `u` as the image of `X` in an algebra map `A[X] → module.End A M`
and extend this to all polynomials `p(X)` using the `A` algebra structure
on `module.End A M` (`= (M →ₗ[A] M)`).  This is given to us by `polynomial.eval`.
Using this definition, we can define the annihilating ideal of `u` to be
`{ p ∈ A[x] | p(u) = 0 }`. This is an ideal in `A[X]`. -/
noncomputable def annihilating_ideal (u: M →ₗ[A] M) : ideal (polynomial A) :=
  ring_hom.ker (polynomial.aeval u).to_ring_hom

/-- It is useful to refer to ideal membership sometimes
 and the annihilation condition other times -/
lemma mem_annihilating_ideal_iff_aeval_0 (u: M →ₗ[A] M) (p: polynomial A)
 : (p ∈ annihilating_ideal u) ↔ (polynomial.aeval u) p = 0 :=
begin
  split,
  intros hp,
  exact (ring_hom.mem_ker (polynomial.aeval u).to_ring_hom).2 hp,
  intros hup0,
  exact (ring_hom.mem_ker (polynomial.aeval u).to_ring_hom).1 hup0,
end

variables {𝕜 V: Type*}
variables [field 𝕜] [add_comm_group V] [module 𝕜 V]

/-- Since `𝕜[x]` is a principal ideal domain there is a polynomial `g` such that
 `span 𝕜 {g} = annihilating_ideal u` -/
noncomputable def annihilating_ideal_generator (u: V →ₗ[𝕜] V) : polynomial 𝕜 :=
  submodule.is_principal.generator (annihilating_ideal u)

/-- We are working toward showing the generator of the annihilating ideal
in the field case is the minimal polynomial. We are going to use a uniqueness
theorem of the minimal polynomial. This is the first condition: it must annihilate
the original endomorphism `u: V →ₗ[𝕜] V`. -/
lemma annihilating_ideal_generator_aeval_0 (u: V →ₗ[𝕜] V) :
  polynomial.aeval u (annihilating_ideal_generator u) = 0 :=
begin
  rw annihilating_ideal_generator,
  have gen_u_member := submodule.is_principal.generator_mem (annihilating_ideal u),
  exact (ring_hom.mem_ker (polynomial.aeval u).to_ring_hom).1 gen_u_member,
end

/-- This is a stepping stone to show the generator has minimal degree -/
lemma mem_iff_generator_dvd (u: V →ₗ[𝕜] V) (p : polynomial 𝕜) :
  p ∈ annihilating_ideal u ↔ annihilating_ideal_generator u ∣ p :=
  submodule.is_principal.mem_iff_generator_dvd (annihilating_ideal u)

/-- We are working toward showing the generator of the annihilating ideal
in the field case is the minimal polynomial. We are going to use a uniqueness
theorem of the minimal polynomial. This is the second condition: it must have minimal
degree among the annihilators of the original endomorphism `u: V →ₗ[𝕜] V`. -/
lemma non_zero_gen_of_non_zero_mem (u: V →ₗ[𝕜] V) (p: polynomial 𝕜) (g: polynomial 𝕜)
  (hp: p ∈ annihilating_ideal u) (hpn0: p ≠ 0) :
  annihilating_ideal_generator u ≠ 0 :=
begin
  by_contradiction hg,
  cases (mem_iff_generator_dvd u p).1 hp with q hq,
  rw [ hg, zero_mul ] at hq,
  exact hpn0 hq,
end

/-- The generator of the annihilating ideal has minimal degree among
 the non-zero members of the annihilating ideal -/
lemma mem_iff_deg_ge_deg_generator (u: V →ₗ[𝕜] V) (p: polynomial 𝕜) (g: polynomial 𝕜)
  (hp: p ∈ annihilating_ideal u) (hpn0: p ≠ 0) :
  polynomial.degree (annihilating_ideal_generator u) ≤ polynomial.degree p :=
begin
  apply polynomial.degree_le_of_dvd hpn0,
  cases (mem_iff_generator_dvd u p).1 hp with q hpgq,
  exact dvd.intro q (eq.symm hpgq),
end

/-- This is what we have been building to:
The monic generator of the annihilating ideal is the minimal polynomial. -/
lemma minpoly_eq_monic_annihilating_ideal_generator (u: V →ₗ[𝕜] V)
  (h: (annihilating_ideal_generator u).monic) :
  annihilating_ideal_generator u = minpoly 𝕜 u :=
begin
  /- 3 conditions for a poly being the minpoly -/
  apply minpoly.unique,
  /- 1st condition: the poly is monic -/
  { apply h, },
  /- 2nd condition: the poly annihilates u -/
  { apply annihilating_ideal_generator_aeval_0, },
  /- 3rd condition: the poly has minimal degree among annihilators of u -/
  { intros q hqm heval,
    apply mem_iff_deg_ge_deg_generator u q _ _ _,
    exact annihilating_ideal_generator u,
    exact (mem_annihilating_ideal_iff_aeval_0 u q).2 heval,
    exact polynomial.monic.ne_zero hqm, }
end

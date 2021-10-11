/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import field_theory.minpoly
import ring_theory.adjoin_root
import ring_theory.ideal.operations
import ring_theory.power_basis
import ring_theory.unique_factorization_domain

/-!
# Kummer-Dedekind theorem

This file proves the Kummer-Dedekind theorem on the splitting of prime ideals in an extension
of the ring of integers.

## Main definitions

 * `conductor`
 * `prime_ideal.above` is a multiset of prime ideals over a given prime ideal

## Main results

 * `map_prime_ideal_eq_prod_above`

## Tags

kummer, dedekind, kummer dedekind, dedekind-kummer, dedekind kummer
-/

open_locale big_operators

variables {R S : Type*} [integral_domain R] [integral_domain S]
-- variables [algebra R K] [is_fraction_ring R K] [algebra S L] [is_fraction_ring S L]
variables [algebra R S]

variables (R)
/-- Let `S / R` be a ring extension and `x : S`, then the conductor of R[x] is the
biggest ideal of `S` contained in `R[x]`. -/
def conductor (x : S) : ideal S :=
{ carrier := {a | ∀ (b : S), a * b ∈ algebra.adjoin R ({x} : set S)},
  zero_mem' := λ b, by simpa only [zero_mul] using subalgebra.zero_mem _,
  add_mem' := λ a b ha hb c, by simpa only [add_mul] using subalgebra.add_mem _ (ha c) (hb c),
  smul_mem' := λ c a ha b, by simpa only [smul_eq_mul, mul_left_comm, mul_assoc] using ha (c * b) }

lemma conductor_ne_bot (x : S) : conductor R x ≠ ⊥ :=
sorry

variables {R}

lemma mem_adjoin_of_mem_conductor {x y : S} (hy : y ∈ conductor R x) :
  y ∈ algebra.adjoin R ({x} : set S) :=
by simpa only [mul_one] using hy 1

lemma conductor_subset_adjoin {x : S} : (conductor R x : set S) ⊆ algebra.adjoin R ({x} : set S) :=
λ y, mem_adjoin_of_mem_conductor

/-- Let `p : ideal R` be prime, then the Kummer-Dedekind theorem states `p` factorizes in an
extension `S / R` as the product of the `ideals_above`, if `p` is coprime to the conductor. -/
noncomputable def ideal.is_prime.ideals_above [is_noetherian_ring R] {x : S} (hx : is_integral R x)
  {p : ideal R} (hp : p.is_prime) :
  multiset (ideal S) :=
(wf_dvd_monoid.exists_factors ((minpoly R x).map (ideal.quotient.mk p))
  ((polynomial.monic_map _ (minpoly.monic hx)).ne_zero)).some.map
  (λ f, p.map (algebra_map R S) ⊔ ideal.span
      {polynomial.aeval x (polynomial.map_surjective _ ideal.quotient.mk_surjective f).some})

lemma alg_equiv.to_ring_equiv_eq_coe {A A' : Type*} [semiring A] [semiring A']
  [algebra R A] [algebra R A'] (e : A ≃ₐ[R] A') : e.to_ring_equiv = ↑e := rfl

/-- Let `α` have minimal polynomial `f` over `R` and `p` be a prime ideal of `R`,
then `R[α] / pR[α] = (R[x] / (f)) / pS = R[x] / (f mod p)` -/
noncomputable def ideal.is_prime.quotient_equiv_polynomial_quotient [is_noetherian_ring R]
  [algebra R S] (pb : power_basis R S)
  {p : ideal R} (hp : p.is_prime) (h : p.map (algebra_map R S) ⊔ conductor R pb.gen = ⊤) :
  (p.map (algebra_map R S)).quotient ≃+* ideal.quotient
    (ideal.span ({(minpoly R pb.gen).map (ideal.quotient.mk p)} : set (polynomial p.quotient))) :=
(ideal.quotient_equiv _ (ideal.map (algebra_map R (adjoin_root (minpoly R pb.gen))) p)
  (adjoin_root.equiv' (minpoly R pb.gen) pb
  (by rw [adjoin_root.aeval_eq, adjoin_root.mk_self])
  (minpoly.aeval _ _)).symm.to_ring_equiv
  (by rw [ideal.map_map, alg_equiv.to_ring_equiv_eq_coe, ← alg_equiv.coe_ring_hom_commutes,
          alg_hom.comp_algebra_map])).trans $
  show (ideal.map (algebra_map R (adjoin_root (minpoly R pb.gen))) p).quotient ≃+*
          (ideal.span {polynomial.map (ideal.quotient.mk p) (minpoly R pb.gen)}).quotient,
  from sorry -- 3rd isomorphism theorem

/-- The factorization of the minimal polynomial of `S` over `R` mod `p` determines how
`S / pS` decomposes as a product of quotients. -/
noncomputable def ideal.is_prime.quotient_equiv_prod_span_irred_factor_minpoly [is_noetherian_ring R]
  [algebra R S] (pb : power_basis R S)
  {p : ideal R} (hp : p.is_prime) (h : p.map (algebra_map R S) ⊔ conductor R pb.gen = ⊤)
  {ι : Type*} [fintype ι] (g : ι → (polynomial R)) (e : ι → ℕ)
  (g_monic : ∀ i, polynomial.monic (g i))
  (g_irr : ∀ i, irreducible (polynomial.map (ideal.quotient.mk p) (g i)))
  (prod_eq : ∏ i, ((g i).map (ideal.quotient.mk p) ^ e i) =
    (minpoly R pb.gen).map (ideal.quotient.mk p)) :
  (p.map (algebra_map R S)).quotient ≃+* Π (i : ι), ideal.quotient
    (ideal.span ({(g i).map (ideal.quotient.mk p) ^ e i} : set (polynomial p.quotient))) :=
let q := λ i, (ideal.span ({(g i).map (ideal.quotient.mk p) ^ e i} : set (polynomial p.quotient))) in
(ideal.is_prime.quotient_equiv_polynomial_quotient pb hp h).trans $
(ideal.quotient_equiv _ (⨅ i, q i) (ring_equiv.refl _) _).trans $
ideal.quotient_inf_ring_equiv_pi_quotient q (λ i j h, (ideal.eq_top_iff_one _).mpr
  (by simp_rw [q, ideal.span, ← submodule.span_union, set.union_singleton, ideal.submodule_span_eq,
      ideal.mem_span_insert, exists_prop, ideal.mem_span_singleton]; squeeze_simp))

/-- **Kummer-Dedekind theorem**: the factorization of the minimal polynomial mod `p`
determines how the prime ideal `p` splits in a monogenic ring extension.

This version allows the user to supply the factorization; see `ideal.is_prime.prod_ideals_above`
for this theorem stated with a (non-canonical) choice of factorization.
-/
theorem ideal.is_prime.prod_span_irred_factor_minpoly [is_noetherian_ring R]
  [algebra R S] (pb : power_basis R S)
  {p : ideal R} (hp : p.is_prime) (h : p.map (algebra_map R S) ⊔ conductor R pb.gen = ⊤)
  (gs : multiset (polynomial R)) (g_monic : ∀ g ∈ gs, polynomial.monic g)
  (g_irr : ∀ g ∈ gs, irreducible (polynomial.map (ideal.quotient.mk p) g))
  (prod_eq : (gs.prod).map (ideal.quotient.mk p) = (minpoly R pb.gen).map (ideal.quotient.mk p)) :
  (gs.map (λ g, p.map (algebra_map R S) ⊔ ideal.span {polynomial.aeval pb.gen g})).prod =
    p.map (algebra_map R S) :=
begin
  let q : polynomial R → ideal S := λ g,
    (p.map (algebra_map R S) ⊔ ideal.span {polynomial.aeval pb.gen g}),
  have : ∀ g ∈ gs, (q g).quotient ≃+* (ideal.span
    ({g.map (ideal.quotient.mk p)} : set (polynomial p.quotient))).quotient,
  { intros g gs, sorry },
  obtain ⟨gi, hgi⟩ : ∃ g, g ∈ gs,
  { refine multiset.exists_mem_of_ne_zero (λ hgs, _),
    rw [hgs, multiset.prod_zero, polynomial.map_one] at prod_eq,
    exact minpoly.map_ne_one _ _ _ prod_eq.symm },
  refine le_antisymm (ideal.multiset_prod_le_inf.trans
    ((multiset.inf_le (multiset.mem_map.mpr ⟨_, hgi, rfl⟩)).trans _)) _,
  { simp only [sup_le_iff, le_refl, true_and, ideal.span_le, set.singleton_subset_iff] }
end

/-- **Kummer-Dedekind theorem**: the factorization of the minimal polynomial mod `p`
determines how the prime ideal `p` splits in a ring extension. -/
theorem ideal.is_prime.prod_ideals_above [is_noetherian_ring R] {x : S} (hx : is_integral R x)
  {p : ideal R} (hp : p.is_prime) (h : p.map (algebra_map R S) ⊔ conductor R x = ⊤) :
  (hp.ideals_above hx).prod = p.map (algebra_map R S) :=
begin
  let p' := p.map (algebra_map R S),
  have : ∀ (y : S), y ∈ p' ⊔ conductor R x,
  { intro x, exact h.symm ▸ submodule.mem_top },
  let R' := p.quotient,
  let S' : subalgebra R S := algebra.adjoin R ({x} : set S),
  let f := minpoly R x,
  let f' : polynomial R' := (minpoly R x).map (ideal.quotient.mk p),
  let m₁ : S' →+* p'.quotient := (ideal.quotient.mk p').comp (algebra_map S' S),
  have hm₁ : function.surjective m₁,
  { intro a, rcases ideal.quotient.mk_surjective a with ⟨a, rfl⟩,
    obtain ⟨y, hy, z, hz, rfl⟩ := submodule.mem_sup.mp (this a),
    have hz' := mem_adjoin_of_mem_conductor hz,
    refine ⟨⟨z, hz'⟩, show ideal.quotient.mk p' z = ideal.quotient.mk p' (y + z), from _⟩,
    simp only [ring_hom.map_add, ideal.quotient.eq_zero_iff_mem.mpr hy, zero_add] },
  have km₁ : ideal.map (algebra_map R ↥S') p = m₁.ker,
  { simp only [m₁, ring_hom.ker_eq_comap_bot, ← ideal.comap_comap, p',
      ← ring_hom.ker_eq_comap_bot (ideal.quotient.mk p'), ideal.mk_ker],
    apply le_antisymm,
    { rw [is_scalar_tower.algebra_map_eq R S' S, ← ideal.map_map],
      exact ideal.le_comap_map },
    rintros ⟨a, haS'⟩ haI,
    obtain ⟨y, hy, z, hz, rfl⟩ := submodule.mem_sup.mp (this a),
    have haI : y + z ∈ ideal.map (algebra_map R S) p := haI,
    have hzp : z ∈ p' := (ideal.add_mem_iff_right _ hy).mp haI,
    sorry /- TODO: don't understand this step - what is (p + F) * (pO ∩ O) ?-/ },
  let e₁ : p'.quotient ≃+* (p.map (algebra_map R S')).quotient :=
    ((ideal.quot_equiv_of_eq km₁).trans (ring_hom.quotient_ker_equiv_of_surjective hm₁)).symm,
  let m₂ : polynomial R →+* (ideal.span ({f'} : set (polynomial R'))).quotient :=
    _,
  have hm₂ : function.surjective m₂ := sorry,
  let e₂ : (p.map (algebra_map R S')).quotient ≃+*
      (ideal.span ({f'} : set (polynomial R'))).quotient :=
    ((ideal.quot_equiv_of_eq _).trans (ring_hom.quotient_ker_equiv_of_surjective _)),
  let e₁₂ := e₁.trans e₂,
  let e₃ := ideal.quotient_inf_ring_equiv_pi_quotient,
  sorry
end

/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import field_theory.minpoly
import ring_theory.adjoin_root
import ring_theory.dedekind_domain
import ring_theory.ideal.operations
import ring_theory.polynomial.basic
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

/-- Let `f` be a polynomial over `R` and `I` an ideal of `R`,
then `(R[x]/(f)) / (I)` is isomorphic to `(R/I)[x] / (f mod p)` -/
noncomputable def adjoin_root.quot_equiv_quot_map
  (f : polynomial R) (I : ideal R) :
  (ideal.map (adjoin_root.of f) I).quotient ≃+*
    (ideal.span ({polynomial.map I^.quotient.mk f} : set (polynomial I.quotient))).quotient :=
begin
  rw [adjoin_root.of, ← ideal.map_map, adjoin_root.mk],
  refine (double_quot.quot_quot_equiv_quot_sup (ideal.span {f}) (I.map polynomial.C)).trans _,
  refine ring_equiv.trans _ (ideal.quotient_equiv (ideal.span {ideal.quotient.mk _ f}) _
    (ideal.polynomial_quotient_equiv_quotient_polynomial I).symm _),
  swap,
  { rw [ideal.map_span, set.image_singleton, ring_equiv.coe_to_ring_hom,
        ideal.polynomial_quotient_equiv_quotient_polynomial_symm_mk I f] },
  rw [← set.image_singleton, ← ideal.map_span, sup_comm],
  exact (double_quot.quot_quot_equiv_quot_sup _ _).symm
end

/-- Let `α` have minimal polynomial `f` over `R` and `I` be an ideal of `R`,
then `R[α] / (I) = (R[x] / (f)) / pS = (R/p)[x] / (f mod p)` -/
noncomputable def power_basis.quotient_equiv_quotient_minpoly_map
  (pb : power_basis R S) (I : ideal R)  :
  (I.map (algebra_map R S)).quotient ≃+* ideal.quotient
    (ideal.span ({(minpoly R pb.gen).map I^.quotient.mk} : set (polynomial I.quotient))) :=
(ideal.quotient_equiv _ (ideal.map (adjoin_root.of (minpoly R pb.gen)) I)
  (adjoin_root.equiv' (minpoly R pb.gen) pb
  (by rw [adjoin_root.aeval_eq, adjoin_root.mk_self])
  (minpoly.aeval _ _)).symm.to_ring_equiv
  (by rw [ideal.map_map, alg_equiv.to_ring_equiv_eq_coe, ← alg_equiv.coe_ring_hom_commutes,
          ← adjoin_root.algebra_map_eq, alg_hom.comp_algebra_map])).trans $
adjoin_root.quot_equiv_quot_map _ _

section

open_locale pointwise

lemma ideal.prod_span {ι : Type*} (s : finset ι) (I : ι → set R) :
  (∏ i in s, ideal.span (I i)) = ideal.span (∏ i in s, I i) :=
begin
  letI := classical.dec_eq ι,
  refine finset.induction_on s _ _,
  { simp },
  { intros _ _ H ih,
    rw [finset.prod_insert H, finset.prod_insert H, ih, ideal.span_mul_span],
    congr' 1,
    ext x,
    simp [set.mem_mul, eq_comm] }
end

lemma ideal.prod_span_singleton {ι : Type*} (s : finset ι) (I : ι → R) :
  (∏ i in s, ideal.span ({I i} : set R)) = ideal.span {∏ i in s, I i} :=
begin
  letI := classical.dec_eq ι,
  refine finset.induction_on s _ _,
  { simp },
  { intros _ _ H ih,
    rw [finset.prod_insert H, finset.prod_insert H, ih, ideal.span_mul_span],
    congr' 1,
    ext x,
    simp [set.mem_mul, eq_comm] }
end

lemma ideal.infi_span_singleton {ι : Type*} [fintype ι] (I : ι → R)
  (hI : ∀ i j (hij : i ≠ j), is_coprime (I i) (I j)):
  (⨅ i, ideal.span ({I i} : set R)) = ideal.span {∏ i, I i} :=
begin
  letI := classical.dec_eq ι,
  ext x,
  simp only [submodule.mem_infi, ideal.mem_span_singleton],
  exact ⟨fintype.prod_dvd_of_coprime hI,
    λ h i, dvd_trans (finset.dvd_prod_of_mem _ (finset.mem_univ _)) h⟩
end

end

/-- The factorization of the minimal polynomial of `S` over `R` mod `p` into coprime divisors
determines how `S / pS` decomposes as a product of quotients. -/
noncomputable def ideal.is_prime.quotient_equiv_prod_span_coprime_factor_minpoly
  (pb : power_basis R S) {p : ideal R} (hp : p.is_prime)
  {ι : Type*} [fintype ι] (g : ι → (polynomial R)) (e : ι → ℕ)
  (g_coprime : ∀ i j (hij : i ≠ j),
    is_coprime ((g i).map p^.quotient.mk) ((g j).map p^.quotient.mk))
  (prod_eq : ∏ i, ((g i).map (ideal.quotient.mk p) ^ e i) =
    (minpoly R pb.gen).map (ideal.quotient.mk p)) :
  (p.map (algebra_map R S)).quotient ≃+* Π (i : ι), ideal.quotient
    (ideal.span ({(g i).map (ideal.quotient.mk p) ^ e i} : set (polynomial p.quotient))) :=
let q := λ i, (ideal.span ({(g i).map (ideal.quotient.mk p) ^ e i} : set (polynomial p.quotient))) in
have q_def : ∀ i, q i = ideal.span ({(g i).map (ideal.quotient.mk p) ^ e i} : set (polynomial p.quotient)) := λ i, rfl,
have infi_q_eq : (⨅ i, q i) = ideal.span {(minpoly R pb.gen).map (ideal.quotient.mk p)},
begin
  simp_rw [q_def, ← prod_eq],
  refine ideal.infi_span_singleton _ (λ i j h, (g_coprime i j h).pow),
end,
(power_basis.quotient_equiv_quotient_minpoly_map pb p).trans $
(ideal.quotient_equiv _ (⨅ i, q i) (ring_equiv.refl _)
  (by rw [← ring_equiv.to_ring_hom_eq_coe, ring_equiv.to_ring_hom_refl, ideal.map_id, infi_q_eq])).trans $
ideal.quotient_inf_ring_equiv_pi_quotient q $ λ i j h, (ideal.eq_top_iff_one _).mpr $
begin
  -- We want to show `q i * q j = 1`, because `g i` and `g j` are coprime.
  simp_rw [q, ideal.span, ← submodule.span_union, set.union_singleton, ideal.submodule_span_eq,
      ideal.mem_span_insert, exists_prop, ideal.mem_span_singleton],
  obtain ⟨a, b, h⟩ := @is_coprime.pow _ _ _ _ (e j) (e i) (g_coprime _ _ h.symm),
  exact ⟨a, b * _, dvd_mul_left _ _, h.symm⟩,
end

.

lemma polynomial.monic.normalize_eq_self {R : Type*} [integral_domain R] [normalized_gcd_monoid R]
  {p : polynomial R} (hp : p.monic) :
  normalize p = p :=
by simp only [polynomial.coe_norm_unit, normalize_apply, hp.leading_coeff, norm_unit_one,
  units.coe_one, polynomial.C.map_one, mul_one]

/-- The factorization of the minimal polynomial of `S` over `R` mod `p` into
monic irreducible polynomials determines how `S / pS` decomposes as a product of quotients. -/
noncomputable def ideal.is_prime.quotient_equiv_prod_span_irred_factor_minpoly
  [is_dedekind_domain R]
  (pb : power_basis R S) {p : ideal R} (hp : p.is_prime)
  {ι : Type*} [fintype ι] (g : ι → (polynomial R)) (e : ι → ℕ)
  (g_irred : ∀ i, irreducible ((g i).map (ideal.quotient.mk p)))
  (g_monic : ∀ i, (g i).monic)
  (g_ne : ∀ i j (h : i ≠ j), ((g i).map (ideal.quotient.mk p)) ≠ ((g j).map (ideal.quotient.mk p)))
  (prod_eq : ∏ i, ((g i).map (ideal.quotient.mk p) ^ e i) =
    (minpoly R pb.gen).map (ideal.quotient.mk p)) :
  (p.map (algebra_map R S)).quotient ≃+* Π (i : ι), ideal.quotient
    (ideal.span ({(g i).map (ideal.quotient.mk p) ^ e i} : set (polynomial p.quotient))) :=
begin
  by_cases hp0 : p = ⊥,
  { unfreezingI { subst hp0 },
    have : polynomial.map (ideal.quotient.mk ⊥) (minpoly R pb.gen) = minpoly _ _ := sorry,
    have : unique ι, { sorry }, -- Since we can't have multiple `g` dividing `minpoly _ _`,
    all_goals { sorry } },
  refine hp.quotient_equiv_prod_span_coprime_factor_minpoly pb g e _ prod_eq,
  intros i j hij,
  haveI : p.is_maximal := is_dedekind_domain.dimension_le_one p hp0 hp,
  letI : field p.quotient := ideal.quotient.field p,
  letI : decidable_eq p.quotient := classical.dec_eq _,
  refine (dvd_or_coprime _ _ (g_irred i)).resolve_left _,
  rintro h,
  refine g_ne i j hij _,
  calc _ = normalize _ : _
     ... = normalize _ : normalize_eq_normalize h ((g_irred i).dvd_symm (g_irred j) h)
     ... = _ : _,
  all_goals { rw polynomial.monic.normalize_eq_self, exact polynomial.monic_map _ (g_monic _) }
end

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

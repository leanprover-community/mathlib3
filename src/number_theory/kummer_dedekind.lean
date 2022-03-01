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
open ideal polynomial

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
  refine (ideal.quot_equiv_of_eq _).trans _,
  swap, { rw [adjoin_root.of, ← ideal.map_map, adjoin_root.mk] },
  refine (double_quot.quot_quot_equiv_quot_sup (ideal.span {f}) (I.map polynomial.C)).trans _,
  refine ring_equiv.trans _ (ideal.quotient_equiv (ideal.span {ideal.quotient.mk _ f}) _
    (ideal.polynomial_quotient_equiv_quotient_polynomial I).symm _),
  swap,
  { rw [ideal.map_span, set.image_singleton, ring_equiv.coe_to_ring_hom,
        ideal.polynomial_quotient_equiv_quotient_polynomial_symm_mk I f] },
  refine (ideal.quot_equiv_of_eq _).trans _,
  swap, { rw sup_comm },
  refine (double_quot.quot_quot_equiv_quot_sup _ _).symm.trans (quot_equiv_of_eq _),
  swap, { rw [← set.image_singleton, ← ideal.map_span] }
end

@[simp] lemma quotient_equiv_mk {R S : Type*} [comm_ring R] [comm_ring S]
  (I : ideal R) (J : ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S)) (x : R) :
  quotient_equiv I J f hIJ (ideal.quotient.mk I x) = ideal.quotient.mk J (f x) :=
@quotient_map_mk _ _ _ _ I J f (by { rw hIJ, exact le_comap_map }) x

@[simp] lemma quotient_equiv_symm {R S : Type*} [comm_ring R] [comm_ring S]
  (I : ideal R) (J : ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S))
  (hJI : I = J.map (f.symm : S →+* R) := by rw [hIJ, map_of_equiv]) :
  (quotient_equiv I J f hIJ).symm = quotient_equiv J I f.symm hJI :=
rfl

-- TODO: split me!
@[simp] lemma adjoin_root.quot_equiv_quot_map_apply
  (f : polynomial R) (I : ideal R) (x : polynomial R) :
  adjoin_root.quot_equiv_quot_map f I (ideal.quotient.mk _ (adjoin_root.mk f x)) =
    ideal.quotient.mk _ (x.map I^.quotient.mk) :=
begin
  unfold adjoin_root.quot_equiv_quot_map double_quot.quot_quot_equiv_quot_sup
    double_quot.quot_quot_to_quot_sup adjoin_root.mk double_quot.quot_left_to_quot_sup
    double_quot.lift_sup_quot_quot_mk double_quot.quot_quot_mk quotient_equiv,
  repeat { rw ring_equiv.trans_apply },
  rw [quot_equiv_of_eq_mk, ring_equiv.of_hom_inv_apply, ideal.quotient.lift_mk, quotient.factor_mk,
      quot_equiv_of_eq_mk, ring_equiv.of_hom_inv_symm_apply, ideal.quotient.lift_mk,
      ring_hom.comp_apply, quot_equiv_of_eq_mk, ring_equiv.coe_mk, ring_hom.to_fun_eq_coe,
      quotient_map_mk, ring_equiv.coe_to_ring_hom,
      polynomial_quotient_equiv_quotient_polynomial_symm_mk]
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

@[simp] lemma power_basis.quotient_equiv_quotient_minpoly_map_apply
  (pb : power_basis R S) (I : ideal R) (x : polynomial R) :
  pb.quotient_equiv_quotient_minpoly_map I (ideal.quotient.mk _ (aeval pb.gen x)) =
    ideal.quotient.mk _ (x.map I^.quotient.mk) :=
begin
  unfold power_basis.quotient_equiv_quotient_minpoly_map,
  rw [ring_equiv.trans_apply, quotient_equiv_mk, alg_equiv.coe_ring_equiv',
    adjoin_root.equiv'_symm_apply, power_basis.lift_aeval, adjoin_root.aeval_eq,
    adjoin_root.quot_equiv_quot_map_apply]
end

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
determines how `S / pS` decomposes as a quotient of products.

See also `ideal.is_prime.quotient_equiv_Pi_span_coprime_factor_minpoly`, which additionally applies
the Chinese remainder theorem. -/
noncomputable def ideal.is_prime.quotient_equiv_prod_span_coprime_factor_minpoly
  (pb : power_basis R S) {p : ideal R} (hp : p.is_prime)
  {ι : Type*} [fintype ι] (g : ι → (polynomial R)) (e : ι → ℕ)
  (prod_eq : ∏ i, ((g i).map (ideal.quotient.mk p) ^ e i) =
    (minpoly R pb.gen).map (ideal.quotient.mk p)) :
  (p.map (algebra_map R S)).quotient ≃+* ideal.quotient
    ∏ (i : ι), (ideal.span ({(g i).map (ideal.quotient.mk p)} : set (polynomial p.quotient)) ^ e i) :=
let q := λ i, ideal.span ({(g i).map (ideal.quotient.mk p)} : set (polynomial p.quotient)) ^ e i in
have q_def : ∀ i, q i = ideal.span ({(g i).map (ideal.quotient.mk p)} : set (polynomial p.quotient)) ^ e i := λ i, rfl,
have prod_q_eq : (∏ i, q i) = ideal.span {(minpoly R pb.gen).map (ideal.quotient.mk p)},
begin
  simp_rw [q_def, ← prod_eq, ideal.span_singleton_pow],
  refine ideal.prod_span_singleton _ _,
end,
(power_basis.quotient_equiv_quotient_minpoly_map pb p).trans $
(ideal.quotient_equiv _ (∏ i, q i) (ring_equiv.refl _)
  (by rw [← ring_equiv.to_ring_hom_eq_coe, ring_equiv.to_ring_hom_refl, ideal.map_id, prod_q_eq]))

/-- The factorization of the minimal polynomial of `S` over `R` mod `p` into coprime divisors
determines how `S / pS` decomposes as a product of quotients. -/
noncomputable def ideal.is_prime.quotient_equiv_Pi_span_coprime_factor_minpoly
  (pb : power_basis R S) {p : ideal R} (hp : p.is_prime)
  {ι : Type*} [fintype ι] (g : ι → (polynomial R)) (e : ι → ℕ)
  (g_coprime : ∀ i j (hij : i ≠ j),
    is_coprime ((g i).map p^.quotient.mk) ((g j).map p^.quotient.mk))
  (prod_eq : ∏ i, ((g i).map (ideal.quotient.mk p) ^ e i) =
    (minpoly R pb.gen).map (ideal.quotient.mk p)) :
  (p.map (algebra_map R S)).quotient ≃+* Π (i : ι), ideal.quotient
    (ideal.span ({(g i).map (ideal.quotient.mk p)} : set (polynomial p.quotient)) ^ e i) :=
let q := λ i, ideal.span ({(g i).map (ideal.quotient.mk p)} : set (polynomial p.quotient)) ^ e i in
have q_def : ∀ i, q i = ideal.span ({(g i).map (ideal.quotient.mk p)} : set (polynomial p.quotient)) ^ e i := λ i, rfl,
have infi_q_eq : (⨅ i, q i) = ideal.span {(minpoly R pb.gen).map (ideal.quotient.mk p)},
begin
  simp_rw [q_def, ← prod_eq, ideal.span_singleton_pow],
  refine ideal.infi_span_singleton _ (λ i j h, (g_coprime i j h).pow),
end,
(power_basis.quotient_equiv_quotient_minpoly_map pb p).trans $
(ideal.quotient_equiv _ (⨅ i, q i) (ring_equiv.refl _)
  (by rw [← ring_equiv.to_ring_hom_eq_coe, ring_equiv.to_ring_hom_refl, ideal.map_id, infi_q_eq])).trans $
ideal.quotient_inf_ring_equiv_pi_quotient q $ λ i j h, (ideal.eq_top_iff_one _).mpr $
begin
  -- We want to show `q i * q j = 1`, because `g i` and `g j` are coprime.
  simp_rw [q, ideal.span_singleton_pow, ideal.span, ← submodule.span_union,
    set.union_singleton, ideal.submodule_span_eq, ideal.mem_span_insert,
    exists_prop, ideal.mem_span_singleton],
  obtain ⟨a, b, h⟩ := @is_coprime.pow _ _ _ _ (e j) (e i) (g_coprime _ _ h.symm),
  exact ⟨a, b * _, dvd_mul_left _ _, h.symm⟩,
end

.

lemma quotient_inf_ring_equiv_pi_quotient_apply
  {ι : Type*} [fintype ι] (f : ι → ideal R)
  (hf : ∀ i j, i ≠ j → f i ⊔ f j = ⊤) (x) (i) :
  quotient_inf_ring_equiv_pi_quotient f hf (ideal.quotient.mk _ x) i =
  ideal.quotient.mk (f i) x :=
by rw [quotient_inf_ring_equiv_pi_quotient, ring_equiv.coe_mk, equiv.to_fun_as_coe,
    equiv.of_bijective_apply, quotient_inf_to_pi_quotient, ideal.quotient.lift_mk,
    pi.ring_hom_apply]

lemma ideal.is_prime.quotient_equiv_prod_span_coprime_factor_minpoly_apply
  (pb : power_basis R S) {p : ideal R} (hp : p.is_prime)
  {ι : Type*} [fintype ι] (g : ι → (polynomial R)) (e : ι → ℕ)
  (prod_eq : ∏ i, ((g i).map (ideal.quotient.mk p) ^ e i) =
    (minpoly R pb.gen).map (ideal.quotient.mk p))
  (x : polynomial R) :
  hp.quotient_equiv_prod_span_coprime_factor_minpoly pb g e prod_eq
    (ideal.quotient.mk _ (aeval pb.gen x)) = ideal.quotient.mk _ (x.map p^.quotient.mk) :=
begin
  rw [ideal.is_prime.quotient_equiv_prod_span_coprime_factor_minpoly,
      ring_equiv.trans_apply, power_basis.quotient_equiv_quotient_minpoly_map_apply,
      quotient_equiv_mk, ring_equiv.refl_apply]
end

lemma ideal.is_prime.quotient_equiv_Pi_span_coprime_factor_minpoly_apply
  (pb : power_basis R S) {p : ideal R} (hp : p.is_prime)
  {ι : Type*} [fintype ι] (g : ι → (polynomial R)) (e : ι → ℕ)
  (g_coprime : ∀ i j (hij : i ≠ j),
    is_coprime ((g i).map p^.quotient.mk) ((g j).map p^.quotient.mk))
  (prod_eq : ∏ i, ((g i).map (ideal.quotient.mk p) ^ e i) =
    (minpoly R pb.gen).map (ideal.quotient.mk p))
  (x : polynomial R) (i : ι) :
  hp.quotient_equiv_Pi_span_coprime_factor_minpoly pb g e g_coprime prod_eq
    (ideal.quotient.mk _ (aeval pb.gen x)) i = ideal.quotient.mk _ (x.map p^.quotient.mk) :=
begin
  rw [ideal.is_prime.quotient_equiv_Pi_span_coprime_factor_minpoly,
      ring_equiv.trans_apply, ring_equiv.trans_apply,
      power_basis.quotient_equiv_quotient_minpoly_map_apply, quotient_equiv_mk,
      quotient_inf_ring_equiv_pi_quotient_apply, ring_equiv.refl_apply]
end

lemma polynomial.monic.normalize_eq_self {R : Type*} [integral_domain R] [normalized_gcd_monoid R]
  {p : polynomial R} (hp : p.monic) :
  normalize p = p :=
by simp only [polynomial.coe_norm_unit, normalize_apply, hp.leading_coeff, norm_unit_one,
  units.coe_one, polynomial.C.map_one, mul_one]

/-- The factorization of the minimal polynomial of `S` over `R` mod `p` into
monic irreducible polynomials determines how `S / pS` decomposes as a product of quotients. -/
noncomputable def ideal.is_prime.quotient_equiv_Pi_span_irred_factor_minpoly
  [is_dedekind_domain R]
  (pb : power_basis R S) {p : ideal R} (hp : p.is_prime)
  (hp0 : p ≠ ⊥) -- this assumption can be dropped but it's easier to do that later
  {ι : Type*} [fintype ι] (g : ι → polynomial R) (e : ι → ℕ)
  (g_irred : ∀ i, irreducible ((g i).map (ideal.quotient.mk p)))
  (g_monic : ∀ i, (g i).monic)
  (g_ne : ∀ i j (h : i ≠ j), ((g i).map (ideal.quotient.mk p)) ≠ ((g j).map (ideal.quotient.mk p)))
  (prod_eq : ∏ i, ((g i).map (ideal.quotient.mk p) ^ e i) =
    (minpoly R pb.gen).map (ideal.quotient.mk p)) :
  (p.map (algebra_map R S)).quotient ≃+* Π (i : ι), ideal.quotient
    (ideal.span ({(g i).map (ideal.quotient.mk p)} : set (polynomial p.quotient)) ^ e i) :=
begin
  refine hp.quotient_equiv_Pi_span_coprime_factor_minpoly pb g e _ prod_eq,
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

.

lemma ideal.is_prime.quotient_equiv_Pi_span_irred_factor_minpoly_apply
  [is_dedekind_domain R]
  (pb : power_basis R S) {p : ideal R} (hp : p.is_prime)
  (hp0 : p ≠ ⊥) -- this assumption can be dropped but it's easier to do that later
  {ι : Type*} [fintype ι] (g : ι → polynomial R) (e : ι → ℕ)
  (g_irred : ∀ i, irreducible ((g i).map (ideal.quotient.mk p)))
  (g_monic : ∀ i, (g i).monic)
  (g_ne : ∀ i j (h : i ≠ j), ((g i).map (ideal.quotient.mk p)) ≠ ((g j).map (ideal.quotient.mk p)))
  (prod_eq : ∏ i, ((g i).map (ideal.quotient.mk p) ^ e i) =
    (minpoly R pb.gen).map (ideal.quotient.mk p))
  (x : polynomial R) (i : ι) :
  hp.quotient_equiv_Pi_span_irred_factor_minpoly pb hp0 g e g_irred g_monic g_ne prod_eq
    (ideal.quotient.mk _ (aeval pb.gen x)) i =
    ideal.quotient.mk _ (x.map p^.quotient.mk) :=
ideal.is_prime.quotient_equiv_Pi_span_coprime_factor_minpoly_apply _ _ _ _ _ _ _ _


lemma ideal.is_prime.irreducible {R : Type*} [integral_domain R] {I : ideal R} (hI0 : I ≠ ⊥)
  (hI : I.is_prime) : irreducible I :=
{ not_unit' := mt ideal.is_unit_iff.mp hI.ne_top,
  is_unit_or_is_unit' := begin
    unfreezingI { rintro J K rfl },
    rw [ideal.is_unit_iff, ideal.is_unit_iff],
    rw [ne.def, ideal.mul_eq_bot, not_or_distrib, ← ne.def, submodule.ne_bot_iff, ← ne.def,
      submodule.ne_bot_iff] at hI0,
    obtain ⟨⟨x, hx, hx0⟩, ⟨y, hy, hy0⟩⟩ := hI0,
    cases hI.mem_or_mem (mul_mem_mul hx hy) with h h,
    revert hx,
    refine submodule.smul_induction_on h _ _ _ _,
    { intros x hx y hy hxy, }
  end }

/-- **Kummer-Dedekind theorem**: the factorization of the minimal polynomial mod `p`
determines how the prime ideal `p` splits in a monogenic ring extension.

This version allows the user to supply the factorization; see `ideal.is_prime.prod_ideals_above`
for this theorem stated with a (non-canonical) choice of factorization.

TODO: generalize this to non-monogenic extensions (using the conductor)
-/
theorem ideal.is_prime.prod_span_irred_factor_minpoly {ι : Type*} [fintype ι]
  [is_dedekind_domain R] [is_dedekind_domain S]
  [algebra R S] (pb : power_basis R S)
  {p : ideal R} (hp : p.is_prime)
  (gs : ι → polynomial R) (e : ι → ℕ) (g_monic : ∀ i, polynomial.monic (gs i))
  (g_irr : ∀ i, irreducible (polynomial.map (ideal.quotient.mk p) (gs i)))
  (g_ne : ∀ i j (h : i ≠ j), ((gs i).map (ideal.quotient.mk p)) ≠ ((gs j).map (ideal.quotient.mk p)))
  (prod_eq : (∏ i, (gs i).map p^.quotient.mk ^ e i) = (minpoly R pb.gen).map (ideal.quotient.mk p)) :
  (∏ (i : ι), (ideal.span {polynomial.aeval pb.gen (gs i)} ⊔ p.map (algebra_map R S)) ^ e i) =
    p.map (algebra_map R S) :=
begin
  by_cases hp0 : p = ⊥,
  { unfreezingI { subst hp0 },
    have : unique ι := sorry, -- because we can't have different divisors of the minpoly
    sorry },
  have hp0' : p.map (algebra_map R S) ≠ ⊥ := sorry,
  haveI : p.is_maximal := is_dedekind_domain.dimension_le_one p hp0 hp,
  letI : field p.quotient := ideal.quotient.field p,
  set ϕ := pb.quotient_equiv_quotient_minpoly_map p,
  -- set φ := hp.quotient_equiv_prod_span_coprime_factor_minpoly pb gs e prod_eq with φ_def,
  have hprod0 : span {polynomial.map p^.quotient.mk (minpoly R pb.gen)} ≠ ⊥ := sorry,

  let q : ι → ideal S := λ i, ideal.span (p.map (algebra_map R S) ∪ {aeval pb.gen (gs i)}),
  have := λ i, simp_ideal_correspondence _ S ϕ.symm (polynomial R) (map_ring_hom p^.quotient.mk)
    (aeval pb.gen).to_ring_hom hprod0 hp0' (ideal.span {gs i}) _ _,
  simp_rw [map_span, set.image_singleton, alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom] at this,
  simp_rw ← this,
  refine prod_eq_of_quot_equiv _ _ _ _ _ _ _ e _,
  { have : irreducible (ideal.span {(gs i).map p^.quotient.mk}) := ideal.is_prime.irreducible _,
    obtain := unique_factorization_monoid.exists_mem_normalized_factors_of_dvd _ this },
  { },
end

/-- **Kummer-Dedekind theorem**: the factorization of the minimal polynomial mod `p`
determines how the prime ideal `p` splits in a ring extension. -/
theorem ideal.is_prime.prod_ideals_above [is_noetherian_ring R] {x : S} (hx : is_integral R x)
  {p : ideal R} (hp : p.is_prime) (h : p.map (algebra_map R S) ⊔ conductor R x = ⊤) :
  (hp.ideals_above hx).prod = p.map (algebra_map R S) :=
begin
end

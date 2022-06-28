/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import field_theory.minpoly
import number_theory.ramification_inertia
import ring_theory.adjoin_root
import ring_theory.dedekind_domain.ideal
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


/-
section move_me

@[simps]
def alg_equiv.of_ring_equiv {R A B : Type*} [comm_semiring R] [semiring A] [semiring B]
  [algebra R A] [algebra R B] (f : A ≃+* B) (hf : ∀ x, f (algebra_map R A x) = algebra_map R B x) :
  A ≃ₐ[R] B :=
{ to_fun := f,
  inv_fun := f.symm,
  commutes' := hf,
  .. f }

@[simp]
lemma alg_equiv.to_ring_equiv_symm {R A B : Type*} [comm_semiring R] [semiring A] [semiring B]
  [algebra R A] [algebra R B] (f : A ≃ₐ[R] B) :
  (f : A ≃+* B).symm = f.symm :=
rfl

@[simp]
lemma ring_equiv.symm_trans_apply {R S T : Type*} [semiring R] [semiring S] [semiring T]
  (f₁ : R ≃+* S) (f₂ : S ≃+* T) (x : T) : (f₁.trans f₂).symm x = f₁.symm (f₂.symm x) :=
rfl

@[simp] lemma double_quot.quot_quot_equiv_quot_sup_quot_quot_algebra_map {R A : Type*}
  [comm_semiring R] [comm_ring A] [algebra R A]
  (I J : ideal A) (x : R) :
  double_quot.quot_quot_equiv_quot_sup I J (algebra_map R _ x) = algebra_map _ _ x :=
rfl

@[simp] lemma double_quot.quot_quot_equiv_comm_mk_mk {R : Type*} [comm_ring R]
  (I J : ideal R) (x : R) :
  double_quot.quot_quot_equiv_comm I J (ideal.quotient.mk _ (ideal.quotient.mk _ x)) =
    algebra_map _ _ x :=
rfl

@[simp] lemma double_quot.quot_quot_equiv_comm_algebra_map {R A : Type*}
  [comm_semiring R] [comm_ring A] [algebra R A]
  (I J : ideal A) (x : R) :
  double_quot.quot_quot_equiv_comm I J (algebra_map R _ x) = algebra_map _ _ x :=
rfl

@[simp] lemma ideal.quot_equiv_of_eq_symm {R : Type*} [comm_ring R] {I J : ideal R} (h : I = J) :
  (ideal.quot_equiv_of_eq h).symm = ideal.quot_equiv_of_eq h.symm :=
by ext; refl

end move_me

variables {R S : Type*} [comm_ring R] [comm_ring S]
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
-/
/-
lemma conductor_subset_adjoin {x : S} : (conductor R x : set S) ⊆ algebra.adjoin R ({x} : set S) :=
λ y, mem_adjoin_of_mem_conductor

/-- Let `f` be a polynomial over `R` and `I` an ideal of `R`,
then `(R[x]/(f)) / (I)` is isomorphic to `(R/I)[x] / (f mod p)` -/
noncomputable def adjoin_root.quot_equiv_quot_map
  (f : polynomial R) (I : ideal R) :
  (_ ⧸ (ideal.map (adjoin_root.of f) I)) ≃ₐ[R]
    _ ⧸ (ideal.span ({polynomial.map I^.quotient.mk f} : set (polynomial (R ⧸ I)))) :=
begin
  refine alg_equiv.of_ring_equiv ((ideal.quot_equiv_of_eq _).trans _) _,
  swap, { rw [adjoin_root.of, ← ideal.map_map, adjoin_root.mk] },
  refine (double_quot.quot_quot_equiv_comm (ideal.span {f}) (I.map polynomial.C)).trans _,
  refine ring_equiv.trans _ (ideal.quotient_equiv (ideal.span {ideal.quotient.mk _ f}) _
    (ideal.polynomial_quotient_equiv_quotient_polynomial I).symm _),
  swap,
  { rw [ideal.map_span, set.image_singleton, ring_equiv.coe_to_ring_hom,
        ideal.polynomial_quotient_equiv_quotient_polynomial_symm_mk I f] },
  refine quot_equiv_of_eq _,
  { rw [← set.image_singleton, ← ideal.map_span] },
  { intros x,
    rw [ring_equiv.trans_apply, ring_equiv.trans_apply, ring_equiv.trans_apply,
        ← ideal.quotient.mk_algebra_map, quot_equiv_of_eq_mk, ideal.quotient.mk_algebra_map,
        double_quot.quot_quot_equiv_comm_algebra_map, ← ideal.quotient.mk_algebra_map,
        quot_equiv_of_eq_mk, ideal.quotient_equiv_apply, ring_hom.to_fun_eq_coe,
        ideal.quotient_map_mk, ring_equiv.coe_to_ring_hom, ← ideal.quotient.mk_algebra_map,
        ideal.polynomial_quotient_equiv_quotient_polynomial_symm_mk,
        ← polynomial.C_eq_algebra_map, polynomial.map_C],
    refl }
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
  unfold adjoin_root.quot_equiv_quot_map,
  rw alg_equiv.of_ring_equiv_apply,
  repeat { rw ring_equiv.trans_apply },
  rw [quot_equiv_of_eq_mk, adjoin_root.mk, double_quot.quot_quot_equiv_comm_mk_mk,
      ← ideal.quotient.mk_algebra_map, quot_equiv_of_eq_mk, ideal.quotient_equiv_apply,
      ring_hom.to_fun_eq_coe, ideal.quotient_map_mk, ring_equiv.coe_to_ring_hom,
      ← ideal.quotient.mk_algebra_map, ideal.polynomial_quotient_equiv_quotient_polynomial_symm_mk],
  refl
end

lemma adjoin_root.quot_equiv_quot_map_symm_apply
  (f : polynomial R) (I : ideal R) (x : polynomial R) :
  (adjoin_root.quot_equiv_quot_map f I).symm (ideal.quotient.mk _ (map (ideal.quotient.mk I) x)) =
    ideal.quotient.mk _ (adjoin_root.mk f x) :=
begin
  unfold adjoin_root.quot_equiv_quot_map,
  rw alg_equiv.of_ring_equiv_symm_apply,
  repeat { rw ring_equiv.symm_trans_apply },
  rw [ideal.quot_equiv_of_eq_symm, ideal.quot_equiv_of_eq_symm, quotient_equiv_symm,
      quotient_equiv_mk, quot_equiv_of_eq_mk, double_quot.quot_quot_equiv_comm_symm,
      ring_equiv.symm_symm, ideal.polynomial_quotient_equiv_quotient_polynomial_map_mk,
      double_quot.quot_quot_equiv_comm_mk_mk, ← ideal.quotient.mk_algebra_map,
      quot_equiv_of_eq_mk],
  refl
end

/-- Let `α` have minimal polynomial `f` over `R` and `I` be an ideal of `R`,
then `R[α] / (I) = (R[x] / (f)) / pS = (R/p)[x] / (f mod p)` -/
noncomputable def power_basis.quotient_equiv_quotient_minpoly_map [is_domain R] [is_domain S]
  (pb : power_basis R S) (I : ideal R)  :
  (S ⧸ I.map (algebra_map R S)) ≃ₐ[R] (polynomial (R ⧸ I)) ⧸
    (ideal.span ({(minpoly R pb.gen).map I^.quotient.mk} : set (polynomial (R ⧸ I)))) :=
alg_equiv.trans
  (alg_equiv.of_ring_equiv
    (ideal.quotient_equiv _ (ideal.map (adjoin_root.of (minpoly R pb.gen)) I)
    (adjoin_root.equiv' (minpoly R pb.gen) pb
    (by rw [adjoin_root.aeval_eq, adjoin_root.mk_self])
    (minpoly.aeval _ _)).symm.to_ring_equiv
    (by rw [ideal.map_map, alg_equiv.to_ring_equiv_eq_coe, ← alg_equiv.coe_ring_hom_commutes,
            ← adjoin_root.algebra_map_eq, alg_hom.comp_algebra_map]))
  (λ x, by rw [← ideal.quotient.mk_algebra_map, ideal.quotient_equiv_apply,
    ring_hom.to_fun_eq_coe, ideal.quotient_map_mk, alg_equiv.to_ring_equiv_eq_coe,
    ring_equiv.coe_to_ring_hom, alg_equiv.coe_ring_equiv, alg_equiv.commutes,
    quotient.mk_algebra_map]))
  (adjoin_root.quot_equiv_quot_map _ _)

@[simp] lemma power_basis.quotient_equiv_quotient_minpoly_map_apply [is_domain R] [is_domain S]
  (pb : power_basis R S) (I : ideal R) (x : polynomial R) :
  pb.quotient_equiv_quotient_minpoly_map I (ideal.quotient.mk _ (aeval pb.gen x)) =
    ideal.quotient.mk _ (x.map I^.quotient.mk) :=
begin
  unfold power_basis.quotient_equiv_quotient_minpoly_map,
  rw [alg_equiv.trans_apply, alg_equiv.of_ring_equiv_apply, quotient_equiv_mk,
    alg_equiv.coe_ring_equiv', adjoin_root.equiv'_symm_apply, power_basis.lift_aeval,
    adjoin_root.aeval_eq, adjoin_root.quot_equiv_quot_map_apply]
end

@[simp] lemma power_basis.quotient_equiv_quotient_minpoly_map_symm_mk [is_domain R] [is_domain S]
  (pb : power_basis R S) (I : ideal R) (x : polynomial R) :
  (pb.quotient_equiv_quotient_minpoly_map I).symm
      (ideal.quotient.mk _ (map (ideal.quotient.mk _) x)) =
    ideal.quotient.mk _ (aeval pb.gen x) :=
begin
  unfold power_basis.quotient_equiv_quotient_minpoly_map,
  simp only [ideal.quotient_equiv_symm_apply, alg_equiv.of_ring_equiv_symm_apply,
    alg_equiv.to_ring_equiv_eq_coe, alg_equiv.symm_trans_apply],
  rw [adjoin_root.quot_equiv_quot_map_symm_apply, ideal.quotient_map_mk,
      ring_equiv.coe_to_ring_hom, alg_equiv.to_ring_equiv_symm, alg_equiv.coe_ring_equiv,
      alg_equiv.symm_symm, adjoin_root.equiv'_apply, adjoin_root.lift_hom_mk]
end
-/


/-- The factorization of the minimal polynomial of `S` over `R` mod `p` into coprime divisors
determines how `S / pS` decomposes as a quotient of products.

See also `ideal.is_prime.quotient_equiv_Pi_span_coprime_factor_minpoly`, which additionally applies
the Chinese remainder theorem. -/
noncomputable def ideal.is_prime.quotient_equiv_prod_span_coprime_factor_minpoly
  [is_domain R] [is_domain S]
  (pb : power_basis R S) {p : ideal R} (hp : p.is_prime)
  {ι : Type*} [fintype ι] (g : ι → (polynomial R)) (e : ι → ℕ)
  (prod_eq : ∏ i, ((g i).map (ideal.quotient.mk p) ^ e i) =
    (minpoly R pb.gen).map (ideal.quotient.mk p)) :
  (S ⧸ p.map (algebra_map R S)) ≃ₐ[R] _ ⧸
    ∏ (i : ι), (ideal.span ({(g i).map (ideal.quotient.mk p)} : set (polynomial (R ⧸ p))) ^ e i) :=
let q := λ i, ideal.span ({(g i).map (ideal.quotient.mk p)} : set (polynomial (R ⧸ p))) ^ e i in
have q_def : ∀ i, q i = ideal.span ({(g i).map (ideal.quotient.mk p)} : set (polynomial (R ⧸ p))) ^ e i := λ i, rfl,
have prod_q_eq : (∏ i, q i) = ideal.span {(minpoly R pb.gen).map (ideal.quotient.mk p)},
begin
  simp_rw [q_def, ← prod_eq, ideal.span_singleton_pow],
  refine ideal.prod_span_singleton _ _,
end,
(power_basis.quotient_equiv_quotient_minpoly_map pb p).trans $
alg_equiv.of_ring_equiv (ideal.quotient_equiv _ (∏ i, q i) (ring_equiv.refl _)
  (by rw [← ring_equiv.to_ring_hom_eq_coe, ring_equiv.to_ring_hom_refl, ideal.map_id, prod_q_eq]))
  (λ x, by rw [ideal.quotient_equiv_apply, ring_hom.to_fun_eq_coe, ideal.quotient_map_algebra_map,
    ring_equiv.coe_to_ring_hom, ring_equiv.refl_apply, ideal.quotient.mk_algebra_map])

open_locale pointwise

-- Helper instance, because of the pi instance bug
-- TODO: why isn't this just `infer_instance`?
noncomputable instance pi.comm_ring' {p : ideal R} {ι : Type*} (g : ι → polynomial R) (e : ι → ℕ) :
  comm_ring (Π (i : ι),
    (polynomial (R ⧸ p) ⧸ (ideal.span ({(g i).map (ideal.quotient.mk p)} : set (polynomial (R ⧸ p))) ^ e i))) :=
@@pi.comm_ring _ (λ i, infer_instance)

/-- The factorization of the minimal polynomial of `S` over `R` mod `p` into coprime divisors
determines how `S / pS` decomposes as a product of quotients. -/
noncomputable def ideal.is_prime.quotient_equiv_Pi_span_coprime_factor_minpoly
  [is_domain R] [is_domain S]
  (pb : power_basis R S) {p : ideal R} (hp : p.is_prime)
  {ι : Type*} [fintype ι] (g : ι → (polynomial R)) (e : ι → ℕ)
  (g_coprime : ∀ i j (hij : i ≠ j),
    is_coprime ((g i).map p^.quotient.mk) ((g j).map p^.quotient.mk))
  (prod_eq : ∏ i, ((g i).map (ideal.quotient.mk p) ^ e i) =
    (minpoly R pb.gen).map (ideal.quotient.mk p)) :
  (S ⧸ p.map (algebra_map R S)) ≃+* Π (i : ι),
    (polynomial (R ⧸ p) ⧸ (ideal.span ({(g i).map (ideal.quotient.mk p)} : set (polynomial (R ⧸ p))) ^ e i)) :=
let q := λ i, ideal.span ({(g i).map (ideal.quotient.mk p)} : set (polynomial (R ⧸ p))) ^ e i in
have q_def : ∀ i, q i = ideal.span ({(g i).map (ideal.quotient.mk p)} : set (polynomial (R ⧸ p))) ^ e i := λ i, rfl,
have infi_q_eq : (⨅ i, q i) = ideal.span {(minpoly R pb.gen).map (ideal.quotient.mk p)},
begin
  simp_rw [q_def, ← prod_eq, ideal.span_singleton_pow],
  refine ideal.infi_span_singleton _ (λ i j h, (g_coprime i j h).pow),
end,
(power_basis.quotient_equiv_quotient_minpoly_map pb p).to_ring_equiv.trans $
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

lemma quotient_inf_ring_equiv_pi_quotient_apply
  {ι : Type*} [fintype ι] (f : ι → ideal R)
  (hf : ∀ i j, i ≠ j → f i ⊔ f j = ⊤) (x) (i) :
  quotient_inf_ring_equiv_pi_quotient f hf (ideal.quotient.mk _ x) i =
  ideal.quotient.mk (f i) x :=
by rw [quotient_inf_ring_equiv_pi_quotient, ring_equiv.coe_mk, equiv.to_fun_as_coe,
    equiv.of_bijective_apply, quotient_inf_to_pi_quotient, ideal.quotient.lift_mk,
    pi.ring_hom_apply]

lemma ideal.is_prime.quotient_equiv_prod_span_coprime_factor_minpoly_apply
  [is_domain R] [is_domain S]
  (pb : power_basis R S) {p : ideal R} (hp : p.is_prime)
  {ι : Type*} [fintype ι] (g : ι → (polynomial R)) (e : ι → ℕ)
  (prod_eq : ∏ i, ((g i).map (ideal.quotient.mk p) ^ e i) =
    (minpoly R pb.gen).map (ideal.quotient.mk p))
  (x : polynomial R) :
  hp.quotient_equiv_prod_span_coprime_factor_minpoly pb g e prod_eq
    (ideal.quotient.mk _ (aeval pb.gen x)) = ideal.quotient.mk _ (x.map p^.quotient.mk) :=
begin
  rw [ideal.is_prime.quotient_equiv_prod_span_coprime_factor_minpoly,
      alg_equiv.trans_apply, alg_equiv.of_ring_equiv_apply,
      power_basis.quotient_equiv_quotient_minpoly_map_apply, quotient_equiv_mk,
      ring_equiv.refl_apply]
end

lemma ideal.is_prime.quotient_equiv_Pi_span_coprime_factor_minpoly_apply
  [is_domain R] [is_domain S]
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
      ring_equiv.trans_apply, ring_equiv.trans_apply, alg_equiv.to_ring_equiv_eq_coe,
      alg_equiv.coe_ring_equiv, power_basis.quotient_equiv_quotient_minpoly_map_apply,
      quotient_equiv_mk, quotient_inf_ring_equiv_pi_quotient_apply, ring_equiv.refl_apply]
end

/-- The factorization of the minimal polynomial of `S` over `R` mod `p` into
monic irreducible polynomials determines how `S / pS` decomposes as a product of quotients. -/
noncomputable def ideal.is_prime.quotient_equiv_Pi_span_irred_factor_minpoly
  [is_domain R] [is_dedekind_domain R] [is_domain S]
  (pb : power_basis R S) {p : ideal R} (hp : p.is_prime)
  (hp0 : p ≠ ⊥) -- this assumption can be dropped but it's easier to do that later
  {ι : Type*} [fintype ι] (g : ι → polynomial R) (e : ι → ℕ)
  (g_irred : ∀ i, irreducible ((g i).map (ideal.quotient.mk p)))
  (g_monic : ∀ i, (g i).monic)
  (g_ne : ∀ i j (h : i ≠ j), ((g i).map (ideal.quotient.mk p)) ≠ ((g j).map (ideal.quotient.mk p)))
  (prod_eq : ∏ i, ((g i).map (ideal.quotient.mk p) ^ e i) =
    (minpoly R pb.gen).map (ideal.quotient.mk p)) :
  S ⧸ (p.map (algebra_map R S)) ≃+* Π (i : ι), _ ⧸
    (ideal.span ({(g i).map (ideal.quotient.mk p)} : set (polynomial (R ⧸ p))) ^ e i) :=
begin
  refine hp.quotient_equiv_Pi_span_coprime_factor_minpoly pb g e _ prod_eq,
  intros i j hij,
  haveI : p.is_maximal := is_dedekind_domain.dimension_le_one p hp0 hp,
  letI : field (R ⧸ p) := ideal.quotient.field p,
  letI : decidable_eq (R ⧸ p) := classical.dec_eq _,
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
  [is_domain R] [is_dedekind_domain R] [is_domain S]
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

section move_me

open unique_factorization_monoid

lemma associated.normalize_eq_normalize {M : Type*} [cancel_comm_monoid_with_zero M]
  [normalization_monoid M] {x y : M} (h : associated x y) :
  normalize x = normalize y :=
normalize_eq_normalize h.dvd h.symm.dvd

lemma irreducible.mem_normalized_factors {M : Type*} [cancel_comm_monoid_with_zero M]
  [unique_factorization_monoid M] [normalization_monoid M] [decidable_eq M]
  {x y : M} (hix : irreducible x) (hnx : normalize x = x) (hy : y ≠ 0) :
  x ∈ normalized_factors y ↔ x ∣ y :=
begin
  refine ⟨dvd_of_mem_normalized_factors, λ h, _⟩,
  obtain ⟨x', hx', hxy⟩ := exists_mem_normalized_factors_of_dvd hy hix h,
  rwa [← hnx, hxy.normalize_eq_normalize, normalize_normalized_factor _ hx'],
end

lemma ideal.irreducible_span_singleton_of_principal_ideal_domain {R : Type*} [comm_ring R]
  [is_domain R] [is_principal_ideal_ring R] (x : R) (hx : irreducible x) :
  irreducible (ideal.span {x} : ideal R) :=
{ not_unit' := by { rw [ideal.is_unit_iff, ideal.span_singleton_eq_top], exact hx.not_unit },
  is_unit_or_is_unit' := begin
    intros I J hIJ,
    obtain ⟨y, rfl⟩ := is_principal_ideal_ring.principal I,
    obtain ⟨z, rfl⟩ := is_principal_ideal_ring.principal J,
    simp only [ideal.submodule_span_eq, ideal.is_unit_iff, span_singleton_eq_top,
      ideal.span_singleton_mul_span_singleton] at hIJ ⊢,
    obtain ⟨x', hx'⟩ := ideal.mem_span_singleton.mp
      (show x ∈ span ({y * z} : set R), from hIJ ▸ ideal.mem_span_singleton.mpr (dvd_refl x)),
    cases hx.is_unit_or_is_unit (hx'.trans (mul_assoc _ _ _)) with hy hz,
    { exact or.inl hy },
    { exact or.inr (is_unit_of_mul_is_unit_left hz) },
end }

@[simp] lemma ideal.quotient.mk_C {R : Type*} [comm_ring R] (x : R) (I : ideal (polynomial R)) :
  ideal.quotient.mk I (C x) = algebra_map R (polynomial R ⧸ I) x :=
by rw [← ideal.quotient.algebra_map_eq, polynomial.C_eq_algebra_map,
       ← is_scalar_tower.algebra_map_apply]

end move_me

/-- **Kummer-Dedekind theorem**: the factorization of the minimal polynomial mod `p`
determines how the prime ideal `p` splits in a monogenic ring extension.

This version allows the user to supply the factorization; see `ideal.is_prime.prod_ideals_above`
for this theorem stated with a (non-canonical) choice of factorization.

TODO: generalize this to non-monogenic extensions (using the conductor)
-/
theorem ideal.is_prime.prod_span_irred_factor_minpoly {ι : Type*} [fintype ι]
  [is_domain R] [is_dedekind_domain R] [is_domain S] [is_dedekind_domain S]
  [algebra R S] (pb : power_basis R S)
  {p : ideal R} (hp : p.is_prime) (hp0' : p.map (algebra_map R S) ≠ ⊥)
  (gs : ι → polynomial R) (e : ι → ℕ) (e_ne : ∀ i, e i ≠ 0) (g_monic : ∀ i, polynomial.monic (gs i))
  (g_irr : ∀ i, irreducible (polynomial.map (ideal.quotient.mk p) (gs i)))
  (g_ne : ∀ i j (h : i ≠ j), ((gs i).map (ideal.quotient.mk p)) ≠ ((gs j).map (ideal.quotient.mk p)))
  (prod_eq : (∏ i, (gs i).map p^.quotient.mk ^ e i) = (minpoly R pb.gen).map (ideal.quotient.mk p)) :
  (∏ (i : ι), (ideal.span {polynomial.aeval pb.gen (gs i)} ⊔ p.map (algebra_map R S)) ^ e i) =
    p.map (algebra_map R S) :=
begin
  have hp0 : p ≠ ⊥,
  { unfreezingI { rintro rfl }, rw ideal.map_bot at hp0', contradiction },
  haveI : p.is_maximal := is_dedekind_domain.dimension_le_one p hp0 hp,
  letI : field (R ⧸ p) := ideal.quotient.field p,
  set ϕ := pb.quotient_equiv_quotient_minpoly_map p,
  have hprod0 : span {polynomial.map p^.quotient.mk (minpoly R pb.gen)} ≠ ⊥,
  { rw [ne.def, ideal.span_singleton_eq_bot, ← prod_eq, finset.prod_eq_zero_iff],
    push_neg,
    intros i _,
    exact pow_ne_zero _ (g_irr i).ne_zero },

  let q : ι → ideal S := λ i, ideal.span (p.map (algebra_map R S) ∪ {aeval pb.gen (gs i)}),
  have := λ i, simp_ideal_correspondence _ S ϕ.symm.to_ring_equiv (polynomial R)
    (map_ring_hom p^.quotient.mk) (aeval pb.gen).to_ring_hom hprod0 hp0' (ideal.span {gs i}) _ _,
  simp_rw [map_span, set.image_singleton, alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom] at this,
  simp_rw ← this,
  refine prod_eq_of_quot_equiv _ _ _ _ _ _ _ e _,
  { simp only [set.mem_set_of_eq, ideal.map_span, set.image_singleton, polynomial.coe_map_ring_hom],
    rw [irreducible.mem_normalized_factors _ (normalize_eq _)],
    simp only [← prod_eq, ← ideal.prod_span_singleton, ← span_singleton_pow],
    refine dvd_trans (dvd_pow_self _ (e_ne i)) (finset.dvd_prod_of_mem _ (finset.mem_univ i)),
    { exact hprod0 },
    { exact ideal.irreducible_span_singleton_of_principal_ideal_domain _ (g_irr i) } },
  { simp only [ideal.span_singleton_pow, ideal.prod_span_singleton, polynomial.coe_map_ring_hom,
      prod_eq] },
  { ext x; simp only [ideal.quotient.mk_algebra_map, polynomial.map_C, alg_hom.coe_to_ring_hom,
     function.comp_app, polynomial.coe_map_ring_hom, ring_hom.coe_comp, polynomial.aeval_C,
     alg_hom.to_ring_hom_eq_coe, ring_equiv.coe_to_ring_hom, polynomial.map_X, polynomial.aeval_X,
     ideal.quotient.mk_C, alg_equiv.to_ring_equiv_eq_coe, alg_equiv.coe_ring_equiv],
    { exact ϕ.symm.commutes x },
    { rw [← polynomial.map_X (ideal.quotient.mk p),
          power_basis.quotient_equiv_quotient_minpoly_map_symm_mk,
          polynomial.aeval_X], } },
end

/-- **Kummer-Dedekind theorem**: the factorization of the minimal polynomial mod `p`
determines how the prime ideal `p` splits in a ring extension. -/
theorem ideal.is_prime.prod_ideals_above [is_noetherian_ring R] {x : S} (hx : is_integral R x)
  {p : ideal R} (hp : p.is_prime) (h : p.map (algebra_map R S) ⊔ conductor R x = ⊤) :
  (hp.ideals_above hx).prod = p.map (algebra_map R S) :=
begin
end

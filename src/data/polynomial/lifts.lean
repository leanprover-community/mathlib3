/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Riccardo Brasca
-/

import data.polynomial.algebra_map
import algebra.algebra.subalgebra
import algebra.polynomial.big_operators
import data.polynomial.erase_lead
import data.polynomial.degree.basic

/-!
Given semirings `R` and `S` with a morphism `f : R →+* S`, we say that a polynomial with
coefficients in `S` lifts if there exist `q : polynomial R` such that `map f p = q`.
We prove various basic results about polynomials that lift, for example that if `p` and `q`
lift then `p + q` lifts. Then, we prove that a polynomial that lifts can always be lifted to a
polynomial of the same degree and that a monic polynomial that lifts can be lifted to a monic
polynomial (of the same degree).

## Main definition

* `lifts R p` : the predicate that says that `p` lifts to `R`.

## Main results

* `lifts_deg_iff_lifts` : A polynomial lifts if and only if it can be lifted to a polynomial
of the same degree.
* `lifts_deg_monic_iff_lifts` : A monic polynomial lifts if and only if it can be lifted to a
monic polynomial of the same degree.
* `lifts_iff` : if `R` is commutative, a polynomial lifts if and only if it is in the image of
`map_alg`, where `map_alg : polynomial R →ₐ[R] polynomial S` is the only `R`-algebra map
that sends `X` to `X`.

## Implementation details
By definition, `p` lifts if and only if it is in the image of `map f`, that is the same
as the image of `ring_hom.of (map f)`. We use the fact that the image is a semiring to prove all the
basic results.

Since we do not assume `R` to be commutative, we cannot say in general that the set of polynomials
that lift is a subalgebra. (By `lift_iff` this is true if `R` is commutative.)

-/

open_locale classical big_operators
noncomputable theory

namespace polynomial
universes u v w

section semiring

variables {R : Type u} [semiring R] {S : Type v} [semiring S] {f : R →+* S}

/-- We say that a polyonmial lifts when there is a polynomial `q` such that `map f q = p`. -/
def lifts (f : R →+* S) (p : polynomial S) : Prop := ∃ (q : polynomial R), map f q = p

lemma lifts_iff (p : polynomial S) : lifts f p ↔ p ∈ ring_hom.srange (ring_hom.of (map f)) :=
  by simp only [lifts, ring_hom.coe_of, ring_hom.mem_srange]

lemma lifts_iff_set_range (p : polynomial S) : lifts f p ↔ p ∈ set.range (map f) :=
  by simp only [lifts, set.mem_range]

lemma lifts_iff_coeff_lifts (p : polynomial S) : lifts f p ↔ ∀ (n : ℕ), p.coeff n ∈ set.range f :=
  by rw [lifts_iff_set_range, mem_map_range]

/-- The polynomial `0` lifts. -/
lemma zero_lifts (f : R →+* S) : lifts f (0 : polynomial S) :=
  by rw [lifts_iff]; exact subsemiring.zero_mem (ring_hom.of (map f)).srange

/-- The polynomial `1` lifts. -/
lemma one_lifts (f : R →+* S) : lifts f (1 : polynomial S) :=
  by rw [lifts_iff]; exact subsemiring.one_mem (ring_hom.of (map f)).srange

/--If `(r : R)`, then `C (algebra_map R S r)` lifts. -/
lemma lifts_C (f : R →+* S) (r : R) : lifts f (C (f r)) :=
  by use C r; rw [map_C]

/-- If `(s : S)` is in the image of `f`, then `C s` lifts. -/
lemma lifts_C' {f : R →+* S} {s : S} (h : s ∈ set.range f) : lifts f (C s) :=
  by obtain ⟨r, rfl⟩ := set.mem_range.1 h; use C r; simp only [map_C]

/-- For any `(n : ℕ)`, the polynomial `(n : polynomial S)` lifts. -/
lemma lifts.nat_mem (f : R →+* S) (n : ℕ) : lifts f (n : polynomial S) :=
  by rw [lifts_iff]; exact subsemiring.coe_nat_mem (ring_hom.of (map f)).srange n

/-- The polynomial `X` lifts. -/
lemma lifts_X (f : R →+* S) : lifts f (X : polynomial S) :=
  by use X; rw [map_X]

/-- The polynomial `X ^ n` lifts. -/
lemma lifts_X_pow (f : R →+* S) (n : ℕ) : lifts f (X ^ n : polynomial S) :=
  by use X ^ n; rw [map_pow, map_X]

/-- If `p` and `q` lift then `p + q` lifts. -/
lemma lifts.add {p q : polynomial S} (hp : lifts f p) (hq : lifts f q) : lifts f (p + q) :=
  by rw lifts_iff at hp hq ⊢; exact subsemiring.add_mem (ring_hom.of (map f)).srange hp hq

/-- If `p` and `q` lift then `p * q` lifts. -/
lemma lifts.mul {p q : polynomial S} (hp : lifts f p) (hq : lifts f q) : lifts f (p * q) :=
  by rw lifts_iff at hp hq ⊢; exact subsemiring.mul_mem (ring_hom.of (map f)).srange hp hq

/-- If `p` lifts and `(n : ℕ)` then `p ^ n` lifts. -/
lemma lifts.pow {p : polynomial S} (n : ℕ) (hp : lifts f p) : lifts f (p ^ n) :=
  by rw lifts_iff at hp ⊢; exact subsemiring.pow_mem (ring_hom.of (map f)).srange hp n

/-- If `p` lifts and `(n : ℕ)` then `n • p` lifts. -/
lemma lifts.nat_smul {p : polynomial S} (n : ℕ) (hp : lifts f p) : lifts f (n • p) :=
  by rw lifts_iff at hp ⊢; exact subsemiring.nsmul_mem (ring_hom.of (map f)).srange hp n

/-- If `p` lifts and `(r : R)` then `r * p` lifts. -/
lemma lifts.base_mul {p : polynomial S} (r : R) (hp : lifts f p) : lifts f (C (f r) * p) :=
  by rw lifts at hp ⊢; obtain ⟨p₁, rfl⟩ := hp; use C r * p₁; rw [map_mul, map_C]

/-- If any element of a list of polynomials lifts, then the product lifts-/
lemma lifts_list_prod {L : list (polynomial S)} :
  (∀ (p : polynomial S), p ∈ L → lifts f p) → lifts f L.prod :=
  by simp_rw [lifts_iff]; exact subsemiring.list_prod_mem (ring_hom.of (map f)).srange

/-- If any element of a list of polynomials lifts, then the sum lifts-/
lemma lifts_list_sum {L : list (polynomial S)} :
  (∀ (p : polynomial S), p ∈ L → lifts f p) → lifts f L.sum :=
  by simp_rw [lifts_iff]; exact subsemiring.list_sum_mem (ring_hom.of (map f)).srange

/-- If any element of a multiset of polynomials lifts, then the sum lifts-/
lemma lifts_multiset_sum {m : multiset (polynomial S)} :
  (∀ (p : polynomial S), p ∈ m → lifts f p) → lifts f m.sum :=
  by simp_rw [lifts_iff]; exact subsemiring.multiset_sum_mem (ring_hom.of (map f)).srange m

/-- If any element of a finset of polynomials lifts, then the sum lifts-/
lemma lifts_sum {ι : Type w} {t : finset ι} {g : ι → (polynomial S)} :
  (∀ (x : ι), x ∈ t → lifts f (g x)) → lifts f (∑ (x : ι) in t, g x) :=
by simp_rw [lifts_iff]; exact subsemiring.sum_mem (ring_hom.of (map f)).srange

/-- If `(s : S)` is in the image of `f`, then `monomial n s` lifts. -/
lemma lifts_monomial {s : S} (n : ℕ) (h : s ∈ set.range f) : lifts f (monomial n s) :=
begin
  obtain ⟨r, rfl⟩ := set.mem_range.1 h,
  use monomial n r,
  simp only [map_monomial],
end

/-- If `p` lifts then `p.erase n` lifts. -/
lemma erase_lifts_of_lifts {p : polynomial S} (n : ℕ) (h : lifts f p) : lifts f (p.erase n) :=
begin
  rw [lifts_iff_set_range, mem_map_range, coeff] at h ⊢,
  intros k,
  by_cases hk : k = n,
  { use 0,
    simp only [hk, ring_hom.map_zero, finsupp.erase_same] },
  obtain ⟨i, hi⟩ := h k,
  use i,
  simp only [hi, hk, finsupp.erase_ne, ne.def, not_false_iff],
end

section lift_deg

lemma lifts_deg_of_monom_lifts {s : S} {n : ℕ} (hl : lifts f (monomial n s)) :
  ∃ (q : polynomial R), map f q = (monomial n s) ∧ q.degree = (monomial n s).degree :=
begin
  by_cases hzero : s = 0,
  { use 0,
    simp only [hzero, degree_zero, eq_self_iff_true, and_self, monomial_zero_right, map_zero] },
  obtain ⟨q, hq⟩ := hl,
  replace hq := (ext_iff.1 hq) n,
  have hcoeff : f (q.coeff n) = s,
  { simp [coeff_monomial] at hq,
    exact hq },
  use (monomial n (q.coeff n)),
  split,
  { simp only [hcoeff, map_monomial] },
  have hqzero : q.coeff n ≠ 0,
  { intro habs,
    simp only [habs, ring_hom.map_zero] at hcoeff,
    exact hzero hcoeff.symm },
  repeat {rw single_eq_C_mul_X},
  simp only [hzero, hqzero, ne.def, not_false_iff, degree_monomial]
end

/-- A polynomial lifts if and only if it can be lifted to a polynomial of the same degree. -/
lemma lifts_deg_of_lifts {p : polynomial S} (hlifts : lifts f p) :
  ∃ (q : polynomial R), map f q = p ∧ q.degree = p.degree :=
begin
  generalize' hd : p.nat_degree = d,
  revert hd p,
  apply nat.strong_induction_on d,
  intros n hn p hlifts hdeg,
  by_cases erase_zero : p.erase_lead = 0,
  { rw [← erase_lead_add_monomial_nat_degree_leading_coeff p, erase_zero, zero_add, leading_coeff],
    exact lifts_deg_of_monom_lifts (lifts_monomial p.nat_degree
    ((lifts_iff_coeff_lifts p).1 hlifts p.nat_degree)) },
  have deg_erase := or.resolve_right (erase_lead_nat_degree_lt_or_erase_lead_eq_zero p) erase_zero,
  have pzero : p ≠ 0,
  { intro habs,
    exfalso,
    rw [habs, erase_lead_zero, eq_self_iff_true, not_true] at erase_zero,
    exact erase_zero },
  have lead_zero : p.coeff p.nat_degree ≠ 0,
  { rw [← leading_coeff, ne.def, leading_coeff_eq_zero]; exact pzero },
  obtain ⟨lead, hlead⟩ := lifts_deg_of_monom_lifts (lifts_monomial p.nat_degree
    ((lifts_iff_coeff_lifts p).1 hlifts p.nat_degree)),
  have deg_lead : lead.degree = p.nat_degree,
  { rw [hlead.2, single_eq_C_mul_X],
    simp only [lead_zero, ne.def, not_false_iff, degree_monomial] },
  rw hdeg at deg_erase,
  obtain ⟨erase, herase⟩ := hn p.erase_lead.nat_degree deg_erase
    (erase_lifts_of_lifts p.nat_degree hlifts) (refl p.erase_lead.nat_degree),
  use erase + lead,
  split,
  { simp only [hlead, herase, map_add],
    nth_rewrite 0 erase_lead_add_monomial_nat_degree_leading_coeff p },
  rw [←hdeg, erase_lead] at deg_erase,
  replace deg_erase := lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 deg_erase),
  rw [← deg_lead, ← herase.2] at deg_erase,
  rw [degree_add_eq_of_degree_lt deg_erase, deg_lead, degree_eq_nat_degree pzero]
end

end lift_deg

section monic

/-- A monic polynomial lifts if and only if it can be lifted to a monic polynomial
of the same degree. -/
lemma lifts_deg_monic_of_lifts [nontrivial S] {p : polynomial S} (hlifts : lifts f p)
  (hmonic : p.monic) : ∃ (q : polynomial R), map f q = p ∧ q.degree = p.degree ∧ q.monic :=
begin
  by_cases Rtrivial : nontrivial R,
  swap,
  { rw not_nontrivial_iff_subsingleton at Rtrivial,
    obtain ⟨q, hq⟩ := lifts_deg_of_lifts hlifts,
    use q,
    exact ⟨hq.1, hq.2, @monic_of_subsingleton _ _ Rtrivial q⟩ },
  by_cases er_zero : p.erase_lead = 0,
  { rw [← erase_lead_add_C_mul_X_pow p, er_zero, zero_add, monic.def.1 hmonic, C_1, one_mul],
    use X ^ p.nat_degree,
    repeat {split},
    { simp only [map_pow, map_X] },
    { rw [@degree_X_pow R _ Rtrivial, degree_X_pow] },
    {exact monic_pow monic_X p.nat_degree } },
  obtain ⟨q, hq⟩ := lifts_deg_of_lifts (erase_lifts_of_lifts p.nat_degree hlifts),
  have deg_er : p.erase_lead.nat_degree < p.nat_degree :=
    or.resolve_right (erase_lead_nat_degree_lt_or_erase_lead_eq_zero p) er_zero,
  replace deg_er := with_bot.coe_lt_coe.2 deg_er,
  rw [← degree_eq_nat_degree er_zero, erase_lead, ← hq.2,
    ← @degree_X_pow R _ Rtrivial p.nat_degree] at deg_er,
  use q + X ^ p.nat_degree,
  repeat {split},
  { simp only [hq, map_add, map_pow, map_X],
    nth_rewrite 3 [← erase_lead_add_C_mul_X_pow p],
    rw [erase_lead, monic.leading_coeff hmonic, C_1, one_mul] },
  { rw [degree_add_eq_of_degree_lt deg_er, @degree_X_pow R _ Rtrivial p.nat_degree,
    degree_eq_nat_degree (monic.ne_zero hmonic)] },
  { rw [monic.def, leading_coeff_add_of_degree_lt deg_er],
    exact monic_pow monic_X p.nat_degree }
end

end monic

end semiring

section comm_semiring

variables {R : Type u} [semiring R] {S : Type v} [comm_semiring S] (f : R →+* S)

/-- If any element of a multiset of polynomials lifts, then the product lifts-/
lemma lifts_multiset_prod {m : multiset (polynomial S)} :
  (∀ (p : polynomial S), p ∈ m → lifts f p) → lifts f m.prod :=
by simp_rw [lifts_iff]; exact subsemiring.multiset_prod_mem (ring_hom.of (map f)).srange m

/-- If any element of a finset of polynomials lifts, then the product lifts-/
lemma lifts_prod {ι : Type w} {t : finset ι} {g : ι → (polynomial S)} :
  (∀ (x : ι), x ∈ t → lifts f (g x)) → lifts f (∏ (x : ι) in t, g x) :=
by simp_rw [lifts_iff]; exact subsemiring.prod_mem (ring_hom.of (map f)).srange

end comm_semiring

section ring

variables {R : Type u} [ring R] {S : Type v} [ring S] (f : R →+* S)

/-- If `p` lifts, then `-p` lifts. -/
lemma lifts.neg {p : polynomial S} (hp : lifts f p) : lifts f (-p) :=
  by rw lifts_iff at hp ⊢; exact subring.neg_mem (ring_hom.range (ring_hom.of (map f))) hp

/-- If `p` and `q` lift then `p - q` lifts. -/
lemma lifts.sub {p q : polynomial S} (hp : lifts f p) (hq : lifts f q) : lifts f (p - q) :=
  by rw lifts_iff at hp hq ⊢; exact subring.sub_mem (ring_hom.range (ring_hom.of (map f))) hp hq

/-- For any `(n : ℤ)`, the polynomial `(n : polynomial S)` lifts. -/
lemma lifts.int (f : R →+* S) (n : ℤ) : lifts f (n : polynomial S) :=
  by rw lifts_iff at ⊢; exact subring.coe_int_mem (ring_hom.range (ring_hom.of (map f))) n

/-- If `p` lifts and `(n : ℤ)` then `n • p` lifts. -/
lemma lifts.int_smul {p : polynomial S} (n : ℤ) (hp : lifts f p) : lifts f (n • p) :=
  by rw lifts_iff at hp ⊢; exact subring.gsmul_mem (ring_hom.range (ring_hom.of (map f))) hp n

end ring

section algebra

variables {R : Type u} [comm_semiring R] {S : Type v} [semiring S] [algebra R S]

/-- The map `polynomial R → polynomial S` as an algebra homomorphism. -/
def map_alg (R : Type u) [comm_semiring R] (S : Type v) [semiring S] [algebra R S] :
  polynomial R →ₐ[R] polynomial S := @aeval _ (polynomial S) _ _ _ (X : polynomial S)

/-- `map_alg` is the morphism induced by `R → S`. -/
lemma map_alg_eq_map (p : polynomial R) : map_alg R S p = map (algebra_map R S) p := by
  simp only [map_alg, aeval_def, eval₂, map, algebra_map_apply, ring_hom.coe_comp]

/-- A polynomial `p` lifts if and only if it is in the image of `map_alg`. -/
lemma lifts_iff_alg (R : Type u) [comm_semiring R] {S : Type v} [semiring S] [algebra R S]
  (p : polynomial S) : lifts (algebra_map R S) p ↔ p ∈ (alg_hom.range (@map_alg R _ S _ _)) :=
  by simp only [lifts, map_alg_eq_map, alg_hom.mem_range]

/-- If `p` lifts and `(r : R)` then `r • p` lifts. -/
lemma lifts.smul {p : polynomial S} (r : R) (hp : lifts (algebra_map R S) p) :
  lifts (algebra_map R S) (r • p) :=
  by rw lifts_iff_alg at hp ⊢; exact subalgebra.smul_mem (map_alg R S).range hp r

end algebra

end polynomial

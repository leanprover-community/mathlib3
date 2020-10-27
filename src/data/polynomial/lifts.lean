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

* `lifts_iff_lifts_deg` : A polynomial lifts if and only if it can be lifted to a polynomial
of the same degree.
* `lifts_iff_lifts_deg_monic` : A monic polynomial lifts if and only if it can be lifted to a
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

/--We say that a polyonmial lifts when there is a polynomial `q` such that `map f q = p`. -/
def lifts (f : R →+* S) (p : polynomial S) : Prop := ∃ (q : polynomial R), map f q = p

lemma lifts_iff (p : polynomial S) : lifts f p ↔ p ∈ ring_hom.srange (ring_hom.of (map f)) :=
  by simp only [lifts, ring_hom.coe_of, ring_hom.mem_srange]

lemma lifts_iff_set_range (p : polynomial S) : lifts f p ↔ p ∈ set.range (map f) :=
  by simp only [lifts, set.mem_range]

/--The polynomial `0` lifts. -/
lemma zero_lifts (f : R →+* S) : lifts f (0 : polynomial S) :=
  by rw [lifts_iff]; exact subsemiring.zero_mem (ring_hom.of (map f)).srange

/--The polynomial `1` lifts. -/
lemma one_lifts (f : R →+* S) : lifts f (1 : polynomial S) :=
  by rw [lifts_iff]; exact subsemiring.one_mem (ring_hom.of (map f)).srange

/--If `(r : R)`, then `C (algebra_map R S r)` lifts. -/
lemma lifts_of_C (f : R →+* S) (r : R) : lifts f (C (f r)) :=
  by use C r; rw [map_C]

/--For any `(n : ℕ)`, the polynomial `(n : polynomial S)` lifts. -/
lemma lifts.nat_mem (f : R →+* S) (n : ℕ) : lifts f (n : polynomial S) :=
  by rw [lifts_iff]; exact subsemiring.coe_nat_mem (ring_hom.of (map f)).srange n

/--The polynomial `X` lifts. -/
lemma X_lifts (f : R →+* S) : lifts f (X : polynomial S) :=
  by use X; rw [map_X]

/--The polynomial `X ^ n` lifts. -/
lemma X_pow_lifts (f : R →+* S) (n : ℕ) : lifts f (X ^ n : polynomial S) :=
  by use X ^ n; rw [map_pow, map_X]

/--If `p` and `q` lift then `p + q` lifts. -/
lemma lifts_add_mem {p q : polynomial S} (hp : lifts f p) (hq : lifts f q) : lifts f (p + q) :=
  by rw lifts_iff at hp hq ⊢; exact subsemiring.add_mem (ring_hom.of (map f)).srange hp hq

/--If `p` and `q` lift then `p * q` lifts. -/
lemma lifts_mul_mem {p q : polynomial S} (hp : lifts f p) (hq : lifts f q) : lifts f (p * q) :=
  by rw lifts_iff at hp hq ⊢; exact subsemiring.mul_mem (ring_hom.of (map f)).srange hp hq

/--If `p` lifts and `(n : ℕ)` then `p ^ n` lifts. -/
lemma lifts.pow_mem {p : polynomial S} (n : ℕ) (hp : lifts f p) : lifts f (p ^ n) :=
  by rw lifts_iff at hp ⊢; exact subsemiring.pow_mem (ring_hom.of (map f)).srange hp n

/--If `p` lifts and `(n : ℕ)` then `n • p` lifts. -/
lemma lifts.nat_smul_mem {p : polynomial S} (n : ℕ) (hp : lifts f p) : lifts f (n • p) :=
  by rw lifts_iff at hp ⊢; exact subsemiring.nsmul_mem (ring_hom.of (map f)).srange hp n

/--If `p` lifts and `(r : R)` then `r * p` lifts. -/
lemma lifts.base_mul_mem {p : polynomial S} (r : R) (hp : lifts f p) : lifts f (C (f r) * p) :=
  by rw lifts at hp ⊢; obtain ⟨p₁, rfl⟩ := hp; use C r * p₁; rw [map_mul, map_C]

/--If any element of a list of polynomials lifts, then the product lifts-/
lemma lifts_list_prod_mem {L : list (polynomial S)} :
  (∀ (p : polynomial S), p ∈ L → lifts f p) → lifts f L.prod :=
  by simp_rw [lifts_iff]; exact subsemiring.list_prod_mem (ring_hom.of (map f)).srange

/--If any element of a list of polynomials lifts, then the sum lifts-/
lemma lifts_list_sum_mem {L : list (polynomial S)} :
  (∀ (p : polynomial S), p ∈ L → lifts f p) → lifts f L.sum :=
  by simp_rw [lifts_iff]; exact subsemiring.list_sum_mem (ring_hom.of (map f)).srange

/--If any element of a multiset of polynomials lifts, then the sum lifts-/
lemma lifts_multiset_sum_mem {m : multiset (polynomial S)} :
  (∀ (p : polynomial S), p ∈ m → lifts f p) → lifts f m.sum :=
  by simp_rw [lifts_iff]; exact subsemiring.multiset_sum_mem (ring_hom.of (map f)).srange m

/--If any element of a finset of polynomials lifts, then the sum lifts-/
lemma lifts_sum_mem {ι : Type w} {t : finset ι} {g : ι → (polynomial S)} :
  (∀ (x : ι), x ∈ t → lifts f (g x)) → lifts f (∑ (x : ι) in t, g x) :=
by simp_rw [lifts_iff]; exact subsemiring.sum_mem (ring_hom.of (map f)).srange

/--If `p` lifts then is leading monomial lifts. -/
lemma lead_monom_lifts_of_lifts {p : polynomial S} (h : lifts f p) :
  lifts f ((C p.leading_coeff) * polynomial.X ^ p.nat_degree) :=
begin
  obtain ⟨q, hq⟩ := h,
  rw leading_coeff,
  use (C (q.coeff p.nat_degree)) * polynomial.X ^ p.nat_degree,
  nth_rewrite 2 ←hq,
  simp only [map_C, coeff_map, map_pow, map_X, map_mul]
end

/--If `p` lifts then `p.erase_lead` lifts. -/
lemma erase_lead_lifts_of_lifts {p : polynomial S} (h : lifts f p) : lifts f p.erase_lead :=
begin
  cases erase_lead_nat_degree_lt_or_erase_lead_eq_zero p with hdeg hzero,
  { obtain ⟨q, hq⟩ := h,
    have hcoeff : ∀ n ∈ p.erase_lead.support, f (q.coeff n) = p.erase_lead.coeff n,
    { intros n hn,
      rw [erase_lead_coeff_of_ne n (ne_nat_degree_of_mem_erase_lead_support hn), ← hq, coeff_map] },
    use (∑ (i : ℕ) in p.erase_lead.support, (C (q.coeff i)) * polynomial.X ^ i),
    simp [map_sum, map_C, map_pow, map_X, map_mul],
    conv_lhs { apply_congr,
               skip,
               simp only [hcoeff, H] },
    nth_rewrite 1 [as_sum_support p.erase_lead] },
  { use 0; simp only [hzero, map_zero] },
end

section lift_deg

/--`lifts_deg f p` means that `p` can be lifted to a polynomial of the same degree. -/
def lifts_deg (f : R →+* S) (p : polynomial S) : Prop :=
  ∃ (q : polynomial R), map f q = p ∧ q.degree = p.degree

lemma lifts_deg_of_supp_le_one {p : polynomial S} (hs : p.support.card < 2) (hl : lifts f p) :
  lifts_deg f p :=
begin
  have h : p.support.card = 0 ∨ p.support.card = 1 := by omega,
  cases h with h0 h1,
  { simp only [finsupp.support_eq_empty, finset.card_eq_zero] at h0,
    use 0,
    simp only [h0, degree_zero, eq_self_iff_true, and_self, map_zero] },
  have hzero : p ≠ 0 := by rw [←nonempty_support_iff, ←finset.card_pos, h1]; exact zero_lt_one,
  replace hs := C_mul_X_pow_eq_self (le_of_eq h1),
  rw [← hs, lifts_deg],
  obtain ⟨q, hq⟩ := hl,
  use (C(q.coeff p.nat_degree) * X ^ p.nat_degree),
  have hcoeff : f (q.coeff p.nat_degree ) = p.coeff p.nat_degree,
  { rw [← hq, coeff_map] },
  split,
  { simp only [leading_coeff, hcoeff, map_C, map_pow, map_X, map_mul] },
  have pcoeff : p.leading_coeff ≠ 0 := by intro ha; exact hzero (leading_coeff_eq_zero.1 ha),
  have qcoeff : q.coeff p.nat_degree ≠ 0,
  { intro habs,
    rw [habs, ←leading_coeff, ring_hom.map_zero] at hcoeff,
    exact pcoeff hcoeff.symm },
  simp only [qcoeff, pcoeff, ne.def, not_false_iff, degree_monomial]
end

/--A polynomial lifts if and only if it can be lifted to a polynomial of the same degree. -/
lemma lifts_iff_lifts_deg (f : R →+* S) (p : polynomial S) : lifts_deg f p ↔ lifts f p :=
begin
  split,
  { intro h; obtain ⟨q, hq⟩ := h; use q; exact hq.1 },
  generalize' hd : p.nat_degree = d,
  revert hd p,
  apply nat.strong_induction_on d,
  intros n hn p hdeg hlifts,
  by_cases hsuppcard : 2 ≤ p.support.card,
  swap,
  { rw [not_le] at hsuppcard; exact lifts_deg_of_supp_le_one hsuppcard hlifts },
  obtain ⟨lead, hlead⟩ := lifts_deg_of_supp_le_one (lt_of_le_of_lt
    (@card_support_C_mul_X_pow_le_one S _ p.leading_coeff p.nat_degree) one_lt_two)
    (lead_monom_lifts_of_lifts hlifts),
  have pzero : p ≠ 0,
  { rw [← nonempty_support_iff, ← finset.card_pos]; exact lt_of_lt_of_le zero_lt_two hsuppcard },
  have lead_zero : p.leading_coeff ≠ 0,
  { rw [ne.def, leading_coeff_eq_zero]; exact pzero },
  have deg_lead : lead.degree = p.nat_degree,
  { rw [hlead.2, degree_monomial p.nat_degree lead_zero] },
  have deg_erase := erase_lead_nat_degree_lt hsuppcard,
  rw hdeg at deg_erase,
  obtain ⟨erase, herase⟩ := hn p.erase_lead.nat_degree deg_erase p.erase_lead
    (refl p.erase_lead.nat_degree) (erase_lead_lifts_of_lifts hlifts),
  use erase + lead,
  split,
  { simp only [hlead, herase, map_add]; nth_rewrite 3 ← erase_lead_add_C_mul_X_pow p },
  rw [←hdeg] at deg_erase,
  replace deg_erase := lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 deg_erase),
  rw [← deg_lead, ← herase.2] at deg_erase,
  rw [degree_add_eq_of_degree_lt deg_erase, deg_lead, degree_eq_nat_degree pzero]
end

end lift_deg

section monic

/--`lifts_deg_monic f p` means that `p` can be lifted to a monic polynomial of the same degree. -/
def lifts_deg_monic (f : R →+* S) (p : polynomial S) : Prop :=
  ∃ (q : polynomial R), map f q = p ∧ q.degree = p.degree ∧ q.monic

/--A monic polynomial lifts if and only if it can be lifted to a monic polynomial
of the same degree. -/
lemma lifts_iff_lifts_deg_monic {f : R →+* S} [nontrivial S] (p : polynomial S) (hmonic : p.monic) :
  lifts_deg_monic f p ↔ lifts f p :=
begin
  split,
  { intro h; obtain ⟨q, hq⟩ := h; use q; exact hq.1 },
  intro hlifts,
  by_cases Rtrivial : nontrivial R,
  swap,
  { rw not_nontrivial_iff_subsingleton at Rtrivial,
    obtain ⟨q, hq⟩ := (lifts_iff_lifts_deg f p).2 hlifts,
    use q,
    exact ⟨hq.1, hq.2, @monic_of_subsingleton _ _ Rtrivial q⟩ },
  by_cases er_zero : p.erase_lead = 0,
  { rw [← erase_lead_add_C_mul_X_pow p, er_zero, zero_add, monic.def.1 hmonic, C_1, one_mul],
    use X ^ p.nat_degree,
    repeat {split},
    { simp only [map_pow, map_X] },
    { rw [@degree_X_pow R _ Rtrivial, degree_X_pow] },
    {exact monic_pow monic_X p.nat_degree } },
  obtain ⟨q, hq⟩ := (lifts_iff_lifts_deg f p.erase_lead).2 (erase_lead_lifts_of_lifts hlifts),
  have deg_er : p.erase_lead.nat_degree < p.nat_degree :=
    or.resolve_right (erase_lead_nat_degree_lt_or_erase_lead_eq_zero p) er_zero,
  replace deg_er := with_bot.coe_lt_coe.2 deg_er,
  rw [← degree_eq_nat_degree er_zero, ← hq.2, ← @degree_X_pow R _ Rtrivial p.nat_degree] at deg_er,
  use q + X ^ p.nat_degree,
  repeat {split},
  { simp only [hq, map_add, map_pow, map_X],
    nth_rewrite 2 [← erase_lead_add_C_mul_X_pow p],
    rw [monic.leading_coeff hmonic, C_1, one_mul] },
  { rw [degree_add_eq_of_degree_lt deg_er, @degree_X_pow R _ Rtrivial p.nat_degree,
    degree_eq_nat_degree (monic.ne_zero hmonic)] },
  { rw [monic.def, leading_coeff_add_of_degree_lt deg_er],
    exact monic_pow monic_X p.nat_degree },
end

end monic

end semiring

section comm_semiring

variables {R : Type u} [semiring R] {S : Type v} [comm_semiring S] (f : R →+* S)

/--If any element of a multiset of polynomials lifts, then the product lifts-/
lemma lifts_multiset_prod_mem {m : multiset (polynomial S)} :
  (∀ (p : polynomial S), p ∈ m → lifts f p) → lifts f m.prod :=
by simp_rw [lifts_iff]; exact subsemiring.multiset_prod_mem (ring_hom.of (map f)).srange m

/--If any element of a finset of polynomials lifts, then the product lifts-/
lemma lifts_prod_mem {ι : Type w} {t : finset ι} {g : ι → (polynomial S)} :
  (∀ (x : ι), x ∈ t → lifts f (g x)) → lifts f (∏ (x : ι) in t, g x) :=
by simp_rw [lifts_iff]; exact subsemiring.prod_mem (ring_hom.of (map f)).srange

end comm_semiring

section ring

variables {R : Type u} [ring R] {S : Type v} [ring S] (f : R →+* S)

/--If `p` lifts, then `-p` lifts. -/
lemma lifts.neg_mem {p : polynomial S} (hp : lifts f p) : lifts f (-p) :=
  by rw lifts_iff at hp ⊢; exact subring.neg_mem (ring_hom.range (ring_hom.of (map f))) hp

/--If `p` and `q` lift then `p - q` lifts. -/
lemma lifts_sub_mem {p q : polynomial S} (hp : lifts f p) (hq : lifts f q) : lifts f (p - q) :=
  by rw lifts_iff at hp hq ⊢; exact subring.sub_mem (ring_hom.range (ring_hom.of (map f))) hp hq

/--For any `(n : ℤ)`, the polynomial `(n : polynomial S)` lifts. -/
lemma lifts.int_mem (f : R →+* S) (n : ℤ) : lifts f (n : polynomial S) :=
  by rw lifts_iff at ⊢; exact subring.coe_int_mem (ring_hom.range (ring_hom.of (map f))) n

/--If `p` lifts and `(n : ℤ)` then `n • p` lifts. -/
lemma lifts.int_smul_mem {p : polynomial S} (n : ℤ) (hp : lifts f p) : lifts f (n • p) :=
  by rw lifts_iff at hp ⊢; exact subring.gsmul_mem (ring_hom.range (ring_hom.of (map f))) hp n

end ring

section algebra

variables {R : Type u} [comm_semiring R] {S : Type v} [semiring S] [algebra R S]

/--The map `polynomial R → polynomial S` as an algebra homomorphism. -/
def map_alg (R : Type u) [comm_semiring R] (S : Type v) [semiring S] [algebra R S] :
  polynomial R →ₐ[R] polynomial S := @aeval _ (polynomial S) _ _ _ (X : polynomial S)

/--`map_alg` is the morphism induced by `R → S`. -/
lemma map_alg_eq_map (p : polynomial R) : map_alg R S p = map (algebra_map R S) p := by
  simp only [map_alg, aeval_def, eval₂, map, algebra_map_apply, ring_hom.coe_comp]

/--A polynomial `p` lifts if and only if it is in the image of `map_alg`. -/
lemma lifts_iff_alg (R : Type u) [comm_semiring R] {S : Type v} [semiring S] [algebra R S]
  (p : polynomial S) : lifts (algebra_map R S) p ↔ p ∈ (alg_hom.range (@map_alg R _ S _ _)) :=
  by simp only [lifts, map_alg_eq_map, alg_hom.mem_range]

/--If `p` lifts and `(r : R)` then `r • p` lifts. -/
lemma lifts.smul_mem {p : polynomial S} (r : R) (hp : lifts (algebra_map R S) p) :
  lifts (algebra_map R S) (r • p) :=
  by rw lifts_iff_alg at hp ⊢; exact subalgebra.smul_mem (map_alg R S).range hp r

end algebra

end polynomial

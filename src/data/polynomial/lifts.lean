/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import data.polynomial.algebra_map
import data.polynomial.monic

/-!
# Polynomials that lift

Given semirings `R` and `S` with a morphism `f : R →+* S`, we define a subsemiring `lifts` of
`S[X]` by the image of `ring_hom.of (map f)`.
Then, we prove that a polynomial that lifts can always be lifted to a polynomial of the same degree
and that a monic polynomial that lifts can be lifted to a monic polynomial (of the same degree).

## Main definition

* `lifts (f : R →+* S)` : the subsemiring of polynomials that lift.

## Main results

* `lifts_and_degree_eq` : A polynomial lifts if and only if it can be lifted to a polynomial
of the same degree.
* `lifts_and_degree_eq_and_monic` : A monic polynomial lifts if and only if it can be lifted to a
monic polynomial of the same degree.
* `lifts_iff_alg` : if `R` is commutative, a polynomial lifts if and only if it is in the image of
`map_alg`, where `map_alg : R[X] →ₐ[R] S[X]` is the only `R`-algebra map
that sends `X` to `X`.

## Implementation details

In general `R` and `S` are semiring, so `lifts` is a semiring. In the case of rings, see
`lifts_iff_lifts_ring`.

Since we do not assume `R` to be commutative, we cannot say in general that the set of polynomials
that lift is a subalgebra. (By `lift_iff` this is true if `R` is commutative.)

-/

open_locale classical big_operators polynomial
noncomputable theory

namespace polynomial
universes u v w

section semiring

variables {R : Type u} [semiring R] {S : Type v} [semiring S] {f : R →+* S}

/-- We define the subsemiring of polynomials that lifts as the image of `ring_hom.of (map f)`. -/
def lifts (f : R →+* S) : subsemiring S[X] := ring_hom.srange (map_ring_hom f)

lemma mem_lifts (p : S[X]) : p ∈ lifts f ↔ ∃ (q : R[X]), map f q = p :=
by simp only [coe_map_ring_hom, lifts, ring_hom.mem_srange]

lemma lifts_iff_set_range (p : S[X]) : p ∈ lifts f ↔ p ∈ set.range (map f) :=
by simp only [coe_map_ring_hom, lifts, set.mem_range, ring_hom.mem_srange]

lemma lifts_iff_ring_hom_srange (p : S[X]) : p ∈ lifts f ↔ p ∈ (map_ring_hom f).srange :=
by simp only [coe_map_ring_hom, lifts, set.mem_range, ring_hom.mem_srange]

lemma lifts_iff_coeff_lifts (p : S[X]) : p ∈ lifts f ↔ ∀ (n : ℕ), p.coeff n ∈ set.range f :=
by { rw [lifts_iff_ring_hom_srange, mem_map_srange f], refl }

/--If `(r : R)`, then `C (f r)` lifts. -/
lemma C_mem_lifts (f : R →+* S) (r : R) : (C (f r)) ∈ lifts f :=
⟨C r, by simp only [coe_map_ring_hom, map_C, set.mem_univ, subsemiring.coe_top, eq_self_iff_true,
  and_self]⟩

/-- If `(s : S)` is in the image of `f`, then `C s` lifts. -/
lemma C'_mem_lifts {f : R →+* S} {s : S} (h : s ∈ set.range f) : (C s) ∈ lifts f :=
begin
  obtain ⟨r, rfl⟩ := set.mem_range.1 h,
  use C r,
  simp only [coe_map_ring_hom, map_C, set.mem_univ, subsemiring.coe_top, eq_self_iff_true,
    and_self]
end

/-- The polynomial `X` lifts. -/
lemma X_mem_lifts (f : R →+* S) : (X : S[X]) ∈ lifts f :=
⟨X, by simp only [coe_map_ring_hom, set.mem_univ, subsemiring.coe_top, eq_self_iff_true, map_X,
  and_self]⟩

/-- The polynomial `X ^ n` lifts. -/
lemma X_pow_mem_lifts (f : R →+* S) (n : ℕ) : (X ^ n : S[X]) ∈ lifts f :=
⟨X ^ n, by simp only [coe_map_ring_hom, map_pow, set.mem_univ, subsemiring.coe_top,
  eq_self_iff_true, map_X, and_self]⟩

/-- If `p` lifts and `(r : R)` then `r * p` lifts. -/
lemma base_mul_mem_lifts {p : S[X]} (r : R) (hp : p ∈ lifts f) : C (f r) * p ∈ lifts f :=
begin
  simp only [lifts, ring_hom.mem_srange] at hp ⊢,
  obtain ⟨p₁, rfl⟩ := hp,
  use C r * p₁,
  simp only [coe_map_ring_hom, map_C, map_mul]
end

/-- If `(s : S)` is in the image of `f`, then `monomial n s` lifts. -/
lemma monomial_mem_lifts {s : S} (n : ℕ) (h : s ∈ set.range f) : (monomial n s) ∈ lifts f :=
begin
  obtain ⟨r, rfl⟩ := set.mem_range.1 h,
  use monomial n r,
  simp only [coe_map_ring_hom, set.mem_univ, map_monomial, subsemiring.coe_top, eq_self_iff_true,
    and_self],
end

/-- If `p` lifts then `p.erase n` lifts. -/
lemma erase_mem_lifts {p : S[X]} (n : ℕ) (h : p ∈ lifts f) : p.erase n ∈ lifts f :=
begin
  rw [lifts_iff_ring_hom_srange, mem_map_srange] at h ⊢,
  intros k,
  by_cases hk : k = n,
  { use 0,
    simp only [hk, ring_hom.map_zero, erase_same] },
  obtain ⟨i, hi⟩ := h k,
  use i,
  simp only [hi, hk, erase_ne, ne.def, not_false_iff],
end

section lift_deg

lemma monomial_mem_lifts_and_degree_eq {s : S} {n : ℕ} (hl : monomial n s ∈ lifts f) :
  ∃ (q : R[X]), map f q = (monomial n s) ∧ q.degree = (monomial n s).degree :=
begin
  by_cases hzero : s = 0,
  { use 0,
    simp only [hzero, degree_zero, eq_self_iff_true, and_self, monomial_zero_right,
               polynomial.map_zero] },
  rw lifts_iff_set_range at hl,
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
  repeat {rw ← C_mul_X_pow_eq_monomial},
  simp only [hzero, hqzero, ne.def, not_false_iff, degree_C_mul_X_pow],
end

/-- A polynomial lifts if and only if it can be lifted to a polynomial of the same degree. -/
lemma mem_lifts_and_degree_eq {p : S[X]} (hlifts : p ∈ lifts f) :
  ∃ (q : R[X]), map f q = p ∧ q.degree = p.degree :=
begin
  generalize' hd : p.nat_degree = d,
  revert hd p,
  apply nat.strong_induction_on d,
  intros n hn p hlifts hdeg,
  by_cases erase_zero : p.erase_lead = 0,
  { rw [← erase_lead_add_monomial_nat_degree_leading_coeff p, erase_zero, zero_add, leading_coeff],
    exact monomial_mem_lifts_and_degree_eq (monomial_mem_lifts p.nat_degree
    ((lifts_iff_coeff_lifts p).1 hlifts p.nat_degree)) },
  have deg_erase := or.resolve_right (erase_lead_nat_degree_lt_or_erase_lead_eq_zero p) erase_zero,
  have pzero : p ≠ 0,
  { intro habs,
    exfalso,
    rw [habs, erase_lead_zero, eq_self_iff_true, not_true] at erase_zero,
    exact erase_zero },
  have lead_zero : p.coeff p.nat_degree ≠ 0,
  { rw [← leading_coeff, ne.def, leading_coeff_eq_zero]; exact pzero },
  obtain ⟨lead, hlead⟩ := monomial_mem_lifts_and_degree_eq (monomial_mem_lifts p.nat_degree
    ((lifts_iff_coeff_lifts p).1 hlifts p.nat_degree)),
  have deg_lead : lead.degree = p.nat_degree,
  { rw [hlead.2, ← C_mul_X_pow_eq_monomial, degree_C_mul_X_pow p.nat_degree lead_zero] },
  rw hdeg at deg_erase,
  obtain ⟨erase, herase⟩ := hn p.erase_lead.nat_degree deg_erase
    (erase_mem_lifts p.nat_degree hlifts) (refl p.erase_lead.nat_degree),
  use erase + lead,
  split,
  { simp only [hlead, herase, polynomial.map_add],
    nth_rewrite 0 erase_lead_add_monomial_nat_degree_leading_coeff p },
  rw [←hdeg, erase_lead] at deg_erase,
  replace deg_erase := lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 deg_erase),
  rw [← deg_lead, ← herase.2] at deg_erase,
  rw [degree_add_eq_right_of_degree_lt deg_erase, deg_lead, degree_eq_nat_degree pzero]
end

end lift_deg

section monic

/-- A monic polynomial lifts if and only if it can be lifted to a monic polynomial
of the same degree. -/
lemma lifts_and_degree_eq_and_monic [nontrivial S] {p : S[X]} (hlifts : p ∈ lifts f)
  (hp : p.monic) : ∃ (q : R[X]), map f q = p ∧ q.degree = p.degree ∧ q.monic :=
begin
  casesI subsingleton_or_nontrivial R with hR hR,
  { obtain ⟨q, hq⟩ := mem_lifts_and_degree_eq hlifts,
    exact ⟨q, hq.1, hq.2, monic_of_subsingleton _⟩ },
  have H : erase p.nat_degree p + X ^ p.nat_degree = p,
  { simpa only [hp.leading_coeff, C_1, one_mul, erase_lead] using erase_lead_add_C_mul_X_pow p },
  by_cases h0 : erase p.nat_degree p = 0,
  { rw [← H, h0, zero_add],
    refine ⟨X ^ p.nat_degree, _, _, monic_X_pow p.nat_degree⟩,
    { rw [polynomial.map_pow, map_X] },
    { rw [degree_X_pow, degree_X_pow] } },
  obtain ⟨q, hq⟩ := mem_lifts_and_degree_eq (erase_mem_lifts p.nat_degree hlifts),
  have hdeg : q.degree < (X ^ p.nat_degree).degree,
  { rw [@degree_X_pow R, hq.2, degree_eq_nat_degree h0, with_bot.coe_lt_coe],
    exact or.resolve_right (erase_lead_nat_degree_lt_or_erase_lead_eq_zero p) h0, },
  refine ⟨q + X ^ p.nat_degree, _, _, (monic_X_pow _).add_of_right hdeg⟩,
  { rw [polynomial.map_add, hq.1, polynomial.map_pow, map_X, H], },
  { rw [degree_add_eq_right_of_degree_lt hdeg, degree_X_pow, degree_eq_nat_degree hp.ne_zero] }
end

lemma lifts_and_nat_degree_eq_and_monic {p : S[X]} (hlifts : p ∈ lifts f)
  (hp : p.monic) : ∃ (q : R[X]), map f q = p ∧ q.nat_degree = p.nat_degree ∧ q.monic :=
begin
  casesI subsingleton_or_nontrivial S with hR hR,
  { obtain (rfl : p = 1) := subsingleton.elim _ _,
    refine ⟨1, subsingleton.elim _ _, by simp, by simp⟩ },
  obtain ⟨p', h₁, h₂, h₃⟩ := lifts_and_degree_eq_and_monic hlifts hp,
  exact ⟨p', h₁, nat_degree_eq_of_degree_eq h₂, h₃⟩
end

end monic

end semiring

section ring

variables {R : Type u} [ring R] {S : Type v} [ring S] (f : R →+* S)

/-- The subring of polynomials that lift. -/
def lifts_ring (f : R →+* S) : subring S[X] := ring_hom.range (map_ring_hom f)

/-- If `R` and `S` are rings, `p` is in the subring of polynomials that lift if and only if it is in
the subsemiring of polynomials that lift. -/
lemma lifts_iff_lifts_ring (p : S[X]) : p ∈ lifts f ↔ p ∈ lifts_ring f :=
by simp only [lifts, lifts_ring, ring_hom.mem_range, ring_hom.mem_srange]

end ring

section algebra

variables {R : Type u} [comm_semiring R] {S : Type v} [semiring S] [algebra R S]

/-- The map `R[X] → S[X]` as an algebra homomorphism. -/
def map_alg (R : Type u) [comm_semiring R] (S : Type v) [semiring S] [algebra R S] :
  R[X] →ₐ[R] S[X] := @aeval _ S[X] _ _ _ (X : S[X])

/-- `map_alg` is the morphism induced by `R → S`. -/
lemma map_alg_eq_map (p : R[X]) : map_alg R S p = map (algebra_map R S) p :=
by simp only [map_alg, aeval_def, eval₂, map, algebra_map_apply, ring_hom.coe_comp]

/-- A polynomial `p` lifts if and only if it is in the image of `map_alg`. -/
lemma mem_lifts_iff_mem_alg (R : Type u) [comm_semiring R] {S : Type v} [semiring S] [algebra R S]
  (p : S[X]) :p ∈ lifts (algebra_map R S) ↔ p ∈ (alg_hom.range (@map_alg R _ S _ _)) :=
by simp only [coe_map_ring_hom, lifts, map_alg_eq_map, alg_hom.mem_range,
  ring_hom.mem_srange]

/-- If `p` lifts and `(r : R)` then `r • p` lifts. -/
lemma smul_mem_lifts {p : S[X]} (r : R) (hp : p ∈ lifts (algebra_map R S)) :
  r • p ∈ lifts (algebra_map R S) :=
by { rw mem_lifts_iff_mem_alg at hp ⊢, exact subalgebra.smul_mem (map_alg R S).range hp r }

end algebra

end polynomial

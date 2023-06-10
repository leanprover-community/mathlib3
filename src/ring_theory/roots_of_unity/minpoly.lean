/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin
-/

import ring_theory.roots_of_unity.basic
import field_theory.minpoly.is_integrally_closed

/-!
# Minimal polynomial of roots of unity

We gather several results about minimal polynomial of root of unity.

## Main results

* `is_primitive_root.totient_le_degree_minpoly`: The degree of the minimal polynomial of a `n`-th
  primitive root of unity is at least `totient n`.

-/

open minpoly polynomial

open_locale polynomial

namespace is_primitive_root

section comm_ring
variables {n : ℕ} {K : Type*} [comm_ring K] {μ : K} (h : is_primitive_root μ n) (hpos : 0 < n)

include n μ h hpos

/--`μ` is integral over `ℤ`. -/
lemma is_integral : is_integral ℤ μ :=
begin
  use (X ^ n - 1),
  split,
  { exact (monic_X_pow_sub_C 1 (ne_of_lt hpos).symm) },
  { simp only [((is_primitive_root.iff_def μ n).mp h).left, eval₂_one, eval₂_X_pow, eval₂_sub,
      sub_self] }
end

section is_domain

variables [is_domain K] [char_zero K]

omit hpos

/--The minimal polynomial of a root of unity `μ` divides `X ^ n - 1`. -/
lemma minpoly_dvd_X_pow_sub_one : minpoly ℤ μ ∣ X ^ n - 1 :=
begin
  rcases n.eq_zero_or_pos with rfl | hpos,
  { simp },
  letI : is_integrally_closed ℤ := gcd_monoid.to_is_integrally_closed,
  apply minpoly.is_integrally_closed_dvd (is_integral h hpos),
  simp only [((is_primitive_root.iff_def μ n).mp h).left, aeval_X_pow, eq_int_cast,
  int.cast_one, aeval_one, alg_hom.map_sub, sub_self]
end

/-- The reduction modulo `p` of the minimal polynomial of a root of unity `μ` is separable. -/
lemma separable_minpoly_mod {p : ℕ} [fact p.prime] (hdiv : ¬p ∣ n) :
  separable (map (int.cast_ring_hom (zmod p)) (minpoly ℤ μ)) :=
begin
  have hdvd : (map (int.cast_ring_hom (zmod p))
    (minpoly ℤ μ)) ∣ X ^ n - 1,
  { simpa [polynomial.map_pow, map_X, polynomial.map_one, polynomial.map_sub] using
      ring_hom.map_dvd (map_ring_hom (int.cast_ring_hom (zmod p)))
        (minpoly_dvd_X_pow_sub_one h) },
  refine separable.of_dvd (separable_X_pow_sub_C 1 _ one_ne_zero) hdvd,
  by_contra hzero,
  exact hdiv ((zmod.nat_coe_zmod_eq_zero_iff_dvd n p).1 hzero)
end

/-- The reduction modulo `p` of the minimal polynomial of a root of unity `μ` is squarefree. -/
lemma squarefree_minpoly_mod {p : ℕ} [fact p.prime] (hdiv : ¬ p ∣ n) :
  squarefree (map (int.cast_ring_hom (zmod p)) (minpoly ℤ μ)) :=
(separable_minpoly_mod h hdiv).squarefree

/- Let `P` be the minimal polynomial of a root of unity `μ` and `Q` be the minimal polynomial of
`μ ^ p`, where `p` is a natural number that does not divide `n`. Then `P` divides `expand ℤ p Q`. -/
lemma minpoly_dvd_expand {p : ℕ} (hdiv : ¬ p ∣ n) : minpoly ℤ μ ∣ expand ℤ p (minpoly ℤ (μ ^ p)) :=
begin
  rcases n.eq_zero_or_pos with rfl | hpos,
  { simp * at *, },
  letI : is_integrally_closed ℤ := gcd_monoid.to_is_integrally_closed,
  refine minpoly.is_integrally_closed_dvd (h.is_integral hpos) _,
  { rw [aeval_def, coe_expand, ← comp, eval₂_eq_eval_map, map_comp, polynomial.map_pow, map_X,
        eval_comp, eval_pow, eval_X, ← eval₂_eq_eval_map, ← aeval_def],
    exact minpoly.aeval _ _ }
end

/- Let `P` be the minimal polynomial of a root of unity `μ` and `Q` be the minimal polynomial of
`μ ^ p`, where `p` is a prime that does not divide `n`. Then `P` divides `Q ^ p` modulo `p`. -/
lemma minpoly_dvd_pow_mod {p : ℕ} [hprime : fact p.prime] (hdiv : ¬ p ∣ n) :
  map (int.cast_ring_hom (zmod p)) (minpoly ℤ μ) ∣
  map (int.cast_ring_hom (zmod p)) (minpoly ℤ (μ ^ p)) ^ p :=
begin
  set Q := minpoly ℤ (μ ^ p),
  have hfrob : map (int.cast_ring_hom (zmod p)) Q ^ p =
    map (int.cast_ring_hom (zmod p)) (expand ℤ p Q),
  by rw [← zmod.expand_card, map_expand],
  rw [hfrob],
  apply ring_hom.map_dvd (map_ring_hom (int.cast_ring_hom (zmod p))),
  exact minpoly_dvd_expand h hdiv
end

/- Let `P` be the minimal polynomial of a root of unity `μ` and `Q` be the minimal polynomial of
`μ ^ p`, where `p` is a prime that does not divide `n`. Then `P` divides `Q` modulo `p`. -/
lemma minpoly_dvd_mod_p {p : ℕ} [hprime : fact p.prime] (hdiv : ¬ p ∣ n) :
  map (int.cast_ring_hom (zmod p)) (minpoly ℤ μ) ∣
  map (int.cast_ring_hom (zmod p)) (minpoly ℤ (μ ^ p)) :=
(unique_factorization_monoid.dvd_pow_iff_dvd_of_squarefree (squarefree_minpoly_mod h
  hdiv) hprime.1.ne_zero).1 (minpoly_dvd_pow_mod h hdiv)

/-- If `p` is a prime that does not divide `n`,
then the minimal polynomials of a primitive `n`-th root of unity `μ`
and of `μ ^ p` are the same. -/
lemma minpoly_eq_pow {p : ℕ} [hprime : fact p.prime] (hdiv : ¬ p ∣ n) :
  minpoly ℤ μ = minpoly ℤ (μ ^ p) :=
begin
  classical,
  by_cases hn : n = 0, { simp * at *, },
  have hpos := nat.pos_of_ne_zero hn,
  by_contra hdiff,
  set P := minpoly ℤ μ,
  set Q := minpoly ℤ (μ ^ p),
  have Pmonic : P.monic := minpoly.monic (h.is_integral hpos),
  have Qmonic : Q.monic := minpoly.monic ((h.pow_of_prime hprime.1 hdiv).is_integral hpos),
  have Pirr : irreducible P := minpoly.irreducible (h.is_integral hpos),
  have Qirr : irreducible Q :=
    minpoly.irreducible ((h.pow_of_prime hprime.1 hdiv).is_integral hpos),
  have PQprim : is_primitive (P * Q) := Pmonic.is_primitive.mul Qmonic.is_primitive,
  have prod : P * Q ∣ X ^ n - 1,
  { rw [(is_primitive.int.dvd_iff_map_cast_dvd_map_cast (P * Q) (X ^ n - 1) PQprim
      (monic_X_pow_sub_C (1 : ℤ) (ne_of_gt hpos)).is_primitive), polynomial.map_mul],
    refine is_coprime.mul_dvd _ _ _,
    { have aux := is_primitive.int.irreducible_iff_irreducible_map_cast Pmonic.is_primitive,
      refine (dvd_or_coprime _ _ (aux.1 Pirr)).resolve_left _,
      rw map_dvd_map (int.cast_ring_hom ℚ) int.cast_injective Pmonic,
      intro hdiv,
      refine hdiff (eq_of_monic_of_associated Pmonic Qmonic _),
      exact associated_of_dvd_dvd hdiv (Pirr.dvd_symm Qirr hdiv) },
    { apply (map_dvd_map (int.cast_ring_hom ℚ) int.cast_injective Pmonic).2,
      exact minpoly_dvd_X_pow_sub_one h },
    { apply (map_dvd_map (int.cast_ring_hom ℚ) int.cast_injective Qmonic).2,
      exact minpoly_dvd_X_pow_sub_one (pow_of_prime h hprime.1 hdiv) } },
  replace prod := ring_hom.map_dvd ((map_ring_hom (int.cast_ring_hom (zmod p)))) prod,
  rw [coe_map_ring_hom, polynomial.map_mul, polynomial.map_sub,
      polynomial.map_one, polynomial.map_pow, map_X] at prod,
  obtain ⟨R, hR⟩ := minpoly_dvd_mod_p h hdiv,
  rw [hR, ← mul_assoc, ← polynomial.map_mul, ← sq, polynomial.map_pow] at prod,
  have habs : map (int.cast_ring_hom (zmod p)) P ^ 2 ∣ map (int.cast_ring_hom (zmod p)) P ^ 2 * R,
  { use R },
  replace habs := lt_of_lt_of_le (part_enat.coe_lt_coe.2 one_lt_two)
    (multiplicity.le_multiplicity_of_pow_dvd (dvd_trans habs prod)),
  have hfree : squarefree (X ^ n - 1 : (zmod p)[X]),
  { exact (separable_X_pow_sub_C 1
          (λ h, hdiv $ (zmod.nat_coe_zmod_eq_zero_iff_dvd n p).1 h) one_ne_zero).squarefree },
  cases (multiplicity.squarefree_iff_multiplicity_le_one (X ^ n - 1)).1 hfree
    (map (int.cast_ring_hom (zmod p)) P) with hle hunit,
  { rw nat.cast_one at habs, exact hle.not_lt habs },
  { replace hunit := degree_eq_zero_of_is_unit hunit,
    rw degree_map_eq_of_leading_coeff_ne_zero (int.cast_ring_hom (zmod p)) _ at hunit,
    { exact (minpoly.degree_pos (is_integral h hpos)).ne' hunit },
    simp only [Pmonic, eq_int_cast, monic.leading_coeff, int.cast_one, ne.def,
      not_false_iff, one_ne_zero] }
end

/-- If `m : ℕ` is coprime with `n`,
then the minimal polynomials of a primitive `n`-th root of unity `μ`
and of `μ ^ m` are the same. -/
lemma minpoly_eq_pow_coprime {m : ℕ} (hcop : nat.coprime m n) :
  minpoly ℤ μ = minpoly ℤ (μ ^ m) :=
begin
  revert n hcop,
  refine unique_factorization_monoid.induction_on_prime m _ _ _,
  { intros n hn h,
    congr,
    simpa [(nat.coprime_zero_left n).mp hn] using h },
  { intros u hunit n hcop h,
    congr,
    simp [nat.is_unit_iff.mp hunit] },
  { intros a p ha hprime hind n hcop h,
    rw hind (nat.coprime.coprime_mul_left hcop) h, clear hind,
    replace hprime := hprime.nat_prime,
    have hdiv := (nat.prime.coprime_iff_not_dvd hprime).1 (nat.coprime.coprime_mul_right hcop),
    haveI := fact.mk hprime,
    rw [minpoly_eq_pow (h.pow_of_coprime a (nat.coprime.coprime_mul_left hcop)) hdiv],
    congr' 1,
    ring_exp }
end

/-- If `m : ℕ` is coprime with `n`,
then the minimal polynomial of a primitive `n`-th root of unity `μ`
has `μ ^ m` as root. -/
lemma pow_is_root_minpoly {m : ℕ} (hcop : nat.coprime m n) :
  is_root (map (int.cast_ring_hom K) (minpoly ℤ μ)) (μ ^ m) :=
by simpa [minpoly_eq_pow_coprime h hcop, eval_map, aeval_def (μ ^ m) _]
  using minpoly.aeval ℤ (μ ^ m)

/-- `primitive_roots n K` is a subset of the roots of the minimal polynomial of a primitive
`n`-th root of unity `μ`. -/
lemma is_roots_of_minpoly [decidable_eq K] : primitive_roots n K ⊆ (map (int.cast_ring_hom K)
  (minpoly ℤ μ)).roots.to_finset :=
begin
  by_cases hn : n = 0, { simp * at *, },
  have hpos := nat.pos_of_ne_zero hn,
  intros x hx,
  obtain ⟨m, hle, hcop, rfl⟩ := (is_primitive_root_iff h hpos).1 ((mem_primitive_roots hpos).1 hx),
  simpa [multiset.mem_to_finset,
    mem_roots (map_monic_ne_zero $ minpoly.monic $ is_integral h hpos)]
    using pow_is_root_minpoly h hcop
end

/-- The degree of the minimal polynomial of `μ` is at least `totient n`. -/
lemma totient_le_degree_minpoly : nat.totient n ≤ (minpoly ℤ μ).nat_degree :=
begin
  classical,
  let P : ℤ[X] := minpoly ℤ μ,-- minimal polynomial of `μ`
  let P_K : K[X] := map (int.cast_ring_hom K) P, -- minimal polynomial of `μ` sent to `K[X]`
  calc
  n.totient = (primitive_roots n K).card : h.card_primitive_roots.symm
        ... ≤ P_K.roots.to_finset.card : finset.card_le_of_subset (is_roots_of_minpoly h)
        ... ≤ P_K.roots.card : multiset.to_finset_card_le _
        ... ≤ P_K.nat_degree : card_roots' _
        ... ≤ P.nat_degree : nat_degree_map_le _ _
end

end is_domain

end comm_ring

end is_primitive_root

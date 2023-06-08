/-
Copyright (c) Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Sidharth Hariharan
-/
import data.polynomial.div
import data.zmod.basic
import logic.function.basic
import ring_theory.localization.fraction_ring
import tactic.field_simp
import tactic.linear_combination

/-!

# Partial fractions

These results were formalised by the Xena Project, at the suggestion
of Patrick Massot.


# The main theorem

* `div_eq_quo_add_sum_rem_div`: General partial fraction decomposition theorem for polynomials over
  an integral domain R :
  If f, g₁, g₂, ..., gₙ ∈ R[X] and the gᵢs are all monic and pairwise coprime, then ∃ q, r₁, ..., rₙ
  ∈ R[X] such that f / g₁g₂...gₙ = q + r₁/g₁ + ... + rₙ/gₙ and for all i, deg(rᵢ) < deg(gᵢ).

* The result is formalized here in slightly more generality, using finsets. That is, if ι is an
  arbitrary index type, g denotes a map from ι to R[X], and if s is an arbitrary finite subset of ι,
  with g i monic for all i ∈ s and for all i,j ∈ s, i ≠ j → g i is coprime to g j, then we have
  ∃ q ∈ R[X] , r : ι → R[X] such that ∀ i ∈ s, deg(r i) < deg(g i) and
  f / ∏ g i = q + ∑ (r i) / (g i), where the product and sum are over s.

* The proof is done by proving the two-denominator case and then performing finset induction for an
  arbitrary (finite) number of denominators.

## Scope for Expansion

* Proving uniqueness of the decomposition

-/


variables (R : Type) [comm_ring R] [is_domain R]

open_locale polynomial

open polynomial

variables (K : Type) [field K] [algebra R[X] K] [is_fraction_ring R[X] K]

/--
Let R be an integral domain and f, g₁, g₂ ∈ R[X]. Let g₁ and g₂ be monic and coprime.
Then, ∃ q, r₁, r₂ ∈ R[X] such that f / g₁g₂ = q + r₁/g₁ + r₂/g₂ and deg(r₁) < deg(g₁) and
deg(r₂) < deg(g₂).
-/
lemma div_eq_quo_add_rem_div_add_rem_div (f : R[X]) {g₁ g₂ : R[X]}
  (hg₁ : g₁.monic) (hg₂ : g₂.monic) (hcoprime : is_coprime g₁ g₂) :
  ∃ q r₁ r₂ : R[X], r₁.degree < g₁.degree ∧ r₂.degree < g₂.degree ∧
  (↑f : K) / (↑g₁ * ↑g₂) = ↑q + ↑r₁ / ↑g₁ + ↑r₂ / ↑g₂ :=
begin
  rcases hcoprime with ⟨c, d, hcd⟩,
  refine ⟨(f * d) /ₘ g₁ + (f * c) /ₘ g₂, (f * d) %ₘ g₁, (f * c) %ₘ g₂,
    (degree_mod_by_monic_lt _ hg₁), (degree_mod_by_monic_lt _ hg₂), _⟩,
  have hg₁' : (↑g₁ : K) ≠ 0,
  { norm_cast, exact hg₁.ne_zero_of_ne zero_ne_one, },
  have hg₂' : (↑g₂ : K) ≠ 0,
  { norm_cast, exact hg₂.ne_zero_of_ne zero_ne_one, },
  have hfc := mod_by_monic_add_div (f * c) hg₂,
  have hfd := mod_by_monic_add_div (f * d) hg₁,
  field_simp,
  norm_cast,
  linear_combination (-1) * f * hcd + (-1) * g₁ * hfc + (-1) * g₂ * hfd,
end

open_locale big_operators classical

/--
Let R be an integral domain and f ∈ R[X]. Let s be a finite index set.
Then, a fraction of the form f / ∏ (g i) can be rewritten as q + ∑ (r i) / (g i), where
deg(r i) < deg(g i), provided that the g i are monic and pairwise coprime.
-/
lemma div_eq_quo_add_sum_rem_div (f : R[X]) {ι : Type*} {g : ι → R[X]} {s : finset ι}
  (hg : ∀ i ∈ s, (g i).monic)
  (hcop : set.pairwise ↑s (λ i j, is_coprime (g i) (g j))) :
  ∃ (q : R[X]) (r : ι → R[X]), (∀ i ∈ s, (r i).degree < (g i).degree) ∧
  (↑f : K) / ∏ i in s, ↑(g i) = ↑q + ∑ i in s, ↑(r i) / ↑(g i) :=
begin
  induction s using finset.induction_on with a b hab Hind f generalizing f,
  { refine ⟨f, (λ (i : ι), (0 : R[X])), λ i, _, by simp⟩,
    rintro ⟨⟩, },
  obtain ⟨q₀, r₁, r₂, hdeg₁, hdeg₂, (hf : (↑f : K) / _ = _)⟩ :=
    div_eq_quo_add_rem_div_add_rem_div R K f
    (_ : monic (g a))
    (_ : monic ∏ (i : ι) in b, (g i))
    _,
  { obtain ⟨q, r, hrdeg, IH⟩ := Hind (λ i hi, hg i (finset.mem_insert_of_mem hi))
      (set.pairwise.mono ( finset.coe_subset.2 $ λ i hi, finset.mem_insert_of_mem hi) hcop) r₂,
    refine ⟨q₀ + q, λ i, if i = a then r₁ else r i, _, _⟩,
    { intro i,
      split_ifs with h1,
      { cases h1,
        intro _,
        exact hdeg₁, },
      { intro hi,
        exact hrdeg i (finset.mem_of_mem_insert_of_ne hi h1), }, },
    norm_cast at ⊢ hf IH,
    rw [finset.prod_insert hab, hf, IH, finset.sum_insert hab, if_pos rfl],
    transitivity (↑(q₀ + q : R[X]) : K) + (↑r₁ / ↑(g a) + ∑ (i : ι) in b, ↑(r i) / ↑(g i)),
    { push_cast, ring, },
    congr' 2,
    refine finset.sum_congr rfl (λ x hxb, _),
    rw if_neg,
    rintro rfl,
    exact hab hxb },
  { exact hg a (b.mem_insert_self a), },
  { exact monic_prod_of_monic _ _ (λ i hi, hg i (finset.mem_insert_of_mem hi)), },
  { refine is_coprime.prod_right (λ i hi, hcop (finset.mem_coe.2 (b.mem_insert_self a))
     (finset.mem_coe.2 (finset.mem_insert_of_mem hi)) _),
    rintro rfl,
    exact hab hi, },
end

.

-- Useful in the uniqueness proof. TODO: Generalize!
lemma finset.sum_prod_div_with_coeffs {ι : Type*} {s : finset ι}
  (g r : ι → R[X]) (hg : ∀ (n : ι), n ∈ s → (g n).monic ) :
  ∑ n in s, ↑(r n) * (∏ k in s, ↑(g k)) / ↑ (g n) =
  ∑ n in s, ↑ (r n) * (∏ k in s.erase n, (↑ (g k) : K) ) :=
begin
  apply finset.sum_congr,
  { refl, },
  { intros x hx,
    rw div_eq_iff _,
    { norm_cast,
      simp only,
      rw mul_assoc,
      apply congr_arg (λ (p : R[X]), (r x) * p),
      rw s.prod_erase_mul _,
      exact hx, },
    { norm_cast,
      exact (hg x hx).ne_zero, } }
end

-- Dividing by a term in a product inside a sum: full generality
lemma finset.sum_prod_div' {ι : Type*} {s : finset ι}
  (g : ι → R[X]) (hg : ∀ (n : ι), n ∈ s → (g n).monic ) :
  ∑ n in s, ((∏ k in s, ↑ (g k)) / ↑ (g n)) = ∑ n in s, (∏ k in s.erase n, (↑ (g k) : K) ) :=
begin
  have H := finset.sum_prod_div_with_coeffs R K g (λ x, (1 : R[X])) hg,
  simp only [algebra_map.coe_one, one_mul, mul_assoc] at H,
  exact H,
end

.

-- Possibly an unnecessary proof? But couldn't find anything of this particular form in the library.
example (f g : R[X]) (hfg : f.degree < g.degree) (hgf : g ∣ f) (hg : g.monic) : f = 0 :=
begin
  cases (exists_eq_mul_left_of_dvd hgf) with q hq,
  -- rw ← degree_eq_bot,
  -- have hgd : g.degree ≥ 0 := zero_le_degree_iff.mpr hg.ne_zero,

  by_contra hf0,
  have hgqn0 : g ≠ 0 ∧ q ≠ 0,
  { by_contra H,
    push_neg at H,
    cases em (g = 0) with hA hB,
    { rw hA at hq,
      rw mul_zero at hq,
      contradiction, },
    { rw H hB at hq,
      rw zero_mul at hq,
      contradiction, } },
  have hdeg : f.degree = q.degree + g.degree,
  { rw hq,
    exact degree_mul},
  have hgf : f.degree ≥ g.degree,
  { --have hA := zero_le_degree_iff.mpr (hgqn0.left),
    have hB := zero_le_degree_iff.mpr (hgqn0.right),

    sorry },
  have : ¬(f.degree < g.degree ∧ f.degree ≥ g.degree),
  { simp only [not_and, not_le, imp_self] },

  -- cases g.degree with n hn,
  -- { exfalso,
  --   simp [with_bot.not_lt_none] at hfg,
  --   exact hfg },
  -- { have : f.degree ≥ some n,
  --   {
  --     sorry },
  --   sorry }
  sorry
end

example (a b : with_bot ℕ) (ha : a ≥ 0) (hb : b ≥ 0) : ¬(a < b ∧ a ≥ b) :=
begin
  simp only [not_and, not_le, imp_self],
end

example (f : R[X]) : f = 0 ↔ f.degree = ⊥ := degree_eq_bot.symm

example (a b : ℕ) (hab : a + b < b) : a < 0 :=
begin
  linarith,
end

example (a b c : with_bot ℕ) (hc : c ≠ ⊥) (h : a = b + c) : a ≥ b :=
begin
  norm_num,
  sorry
end

.

lemma zero_eq_quo_add_sum_rem_div_zero {ι : Type*} (s : finset ι) {g : ι → R[X]}
  (hg : ∀ i ∈ s, (g i).monic) (hcop : (s : set ι).pairwise (λ i j, is_coprime (g i) (g j)))
  (q : R[X]) (r : ι → R[X]) (hdeg : ∀ i, (r i).degree < (g i).degree)
  (hsum : (0 : K) = ↑q + ∑ i in s, ↑(r i) / ↑(g i)) : q = 0 ∧ ∀ i ∈ s, r i = 0 :=
begin
  have hsum' := hsum,  -- creating a copy for use towards the end
  have hzero : (0 : K) = (0 : K) / (∏ i in s, ↑(g i)) := by rw [zero_div],
  rw [hzero, div_eq_iff _] at hsum,
  { simp only [add_mul, finset.sum_mul] at hsum,
    have hsumproddiv := finset.sum_prod_div_with_coeffs R K g r hg,
    field_simp at hsum,
    rw hsumproddiv at hsum,
    norm_cast at hsum,
    have hgdvd : ∀ j ∈ s, (g j) ∣ 0 := λ j hj, (dvd_zero (g j)),
    rw hsum at hgdvd,
    have hgr : ∀ j ∈ s, (g j) ∣ (r j),
    { intros j hjs,
      specialize hgdvd j hjs,
      have hgdvdprod : (g j) ∣ q * (∏ i in s, ↑(g i)) :=
        dvd_mul_of_dvd_right (finset.dvd_prod_of_mem g hjs) q,
      have hgdsum : (g j) ∣ ∑ (i : ι) in s, r i * ∏ (k : ι) in s.erase i, g k :=
        (dvd_add_right (hgdvdprod)).mp hgdvd,
      have hsplitsum := (finset.sum_erase_add s (λ i, r i * ∏ (k : ι) in s.erase i, g k) hjs).symm,
      simp_rw hsplitsum at hgdsum,
      have hdsplit := (dvd_add_right _).mp hgdsum,
      { refine is_coprime.dvd_of_dvd_mul_right _ hdsplit,
        apply is_coprime.prod_right,
        intros i hi,
        exact hcop hjs (finset.mem_of_mem_erase hi) (finset.ne_of_mem_erase hi).symm, },
      { apply finset.dvd_sum,
        intros x hx,
        exact dvd_mul_of_dvd_right (
          finset.dvd_prod_of_mem g (
            finset.mem_erase_of_ne_of_mem (ne.symm (finset.ne_of_mem_erase hx)) hjs
          )
        ) (r x), } },
    have hrzero : ∀ (i : ι), i ∈ s → r i = 0,  -- so it can be used to show that q = 0
    { intros i his,
      specialize hgr i his,
      specialize hdeg i,
      sorry },
    split,
    { have hsumfracszero : ∑ i in s, ↑(r i ) / ↑(g i) = (0 : K),
      { refine finset.sum_eq_zero (λi hi, _),
        rw [(hrzero i hi), algebra_map.coe_zero, zero_div] },
      rw [hsumfracszero, add_zero] at hsum',
      norm_cast at hsum',
      exact hsum'.symm, },
    { exact hrzero }, },
  { norm_cast,
    exact (monic_prod_of_monic s g (λ i hi, hg i hi)).ne_zero, },
end

example (a b c : ℤ) : a ∣ b → a ∣ (b + c) → a ∣ c := λ h1 h2, (dvd_add_right h1).mp h2

example {ι : Type*} {s : finset ι} (f : ι → K) (hf : ∀ (i : ι), i ∈ s → f i = 0) :
  ∑ i in s, f i = 0 :=
begin
  refine finset.sum_eq_zero hf,
end

example (s : finset ℤ) (a : ℤ → ℤ) (b : ℤ) (hb : ∀ i : ℤ, i ∈ s → b ∣ (a i)) : b ∣ ∑ i in s, a i :=
begin
  exact finset.dvd_sum hb,
end

example (a b c : ℤ) (habc : a ∣ b * c) (hac : is_coprime a c) : a ∣ b :=
begin
  exact is_coprime.dvd_of_dvd_mul_right hac habc,
end

example (p q : R[X]) (hdiv : p ∣ q) (hdeg : q.degree < p.degree) : q = 0 :=
begin
  cases (exists_eq_mul_right_of_dvd hdiv) with d hd,
  have hdd : q.degree = p.degree + d.degree,
  { rw [← degree_mul ,hd],},
  rw ← degree_eq_bot,
  rw hdd at hdeg ⊢,
  by_contra hC,
  have hgz : p.degree + d.degree ≥ 0,
  {
    sorry },
  sorry
end

.

#check finsupp

-- Will eventually extend the zero case
lemma div_eq_quo_add_sum_rem_div_unique' {f : R[X]} {ι : Type*} (s : finset ι) {g : ι → R[X]}
  (hg : ∀ i ∈ s, (g i).monic) (hcop : (s : set ι).pairwise (λ i j, is_coprime (g i) (g j)))
  (q q' : R[X]) (r r' : ι → R[X]) (hdeg : ∀ i, (r i).degree < (g i).degree)
  (hdeg' : ∀ i, (r' i).degree < (g i).degree)
  (hf : (↑f : K) / ∏ i in s, ↑(g i) = ↑q + ∑ i in s, ↑(r i) / ↑(g i))
  (hf' : (↑f : K) / ∏ i in s, ↑(g i) = ↑q' + ∑ i in s, ↑(r' i) / ↑(g i)) :
    q = q' ∧ ∀ i ∈ s, r i = r' i :=
begin
  have hsub : (0 : K) = (↑q + ∑ (i : ι) in s, ↑(r i) / ↑(g i)) - (↑q' + ∑ (i : ι) in s, ↑(r' i) / ↑(g i)),
  { rw [← hf, ← hf', sub_self] },
  have hsub' : (0 : K) = ↑(q - q') + ∑ (i : ι) in s, ↑((r i) - (r' i)) / ↑(g i),
  { 
    sorry, },
  have hzerocase := zero_eq_quo_add_sum_rem_div_zero R K s hg hcop (q - q') (λ i, r i - r' i)
    (λ i, (lt_of_le_of_lt (degree_sub_le (r i) (r' i)) (max_lt (hdeg i) (hdeg' i)))) hsub',
  { split,
    { rw ← sub_eq_zero,
      exact hzerocase.1 },
    { intros i hi,
      rw ← sub_eq_zero,
      exact hzerocase.2 i hi } },
end

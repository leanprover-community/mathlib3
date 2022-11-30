/-
Copyright (c) 2022 The Xena Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Sidharth Hariharan
-/
import ring_theory.localization.fraction_ring -- field of fractions
import data.polynomial.div -- theory of division and remainder for monic polynomials
import tactic.field_simp
import tactic
import data.zmod.basic
import logic.function.basic
/-

# Partial fractions

These results were formalised by the Xena Project, at the suggestion
of Patrick Massot.


## The main theorems

* General partial fraction decomposition theorem for polynomials over an integral domain R :
  if f, g₁, g₂, ..., gₙ ∈ R[X] and the gᵢs are all monic and pairwise coprime, then ∃ q, r₁, ..., rₙ
  ∈ R[X] such that f / g₁g₂...gₙ = q + r₁/g₁ + ... + rₙ/gₙ and for all i, deg(rᵢ) < deg(gᵢ).#check

* The result is formalized here in slightly more generality, using finsets.

* The proof is done by proving the two-denominator case and then performing finset induction for an
  arbitrary (finite) number of denominators.

## Scope for Expansion

* Proving uniqueness of the decomposition

-/


-- Let `R` be an integral domain
variables (R : Type) [comm_ring R] [is_domain R]

open_locale polynomial

open polynomial

-- Let K be the field of fractions of R[X].
variables (K : Type) [field K] [algebra R[X] K]  [is_fraction_ring R[X] K]

section one_denominator

namespace polynomial

variables (f : R[X]) {g : R[X]}

lemma div_eq_quo_add_rem_div (hg : g.monic) : ∃ q r : R[X], r.degree < g.degree ∧
  (↑f : K) / ↑g = ↑q + ↑r / ↑g :=
begin
  refine ⟨f /ₘ g, f %ₘ g, _, _⟩,
  { exact degree_mod_by_monic_lt _ hg, },
  { have hg' : (↑g : K) ≠ 0 := by exact_mod_cast (monic.ne_zero hg),
    field_simp [hg'],
    norm_cast,
    rw [add_comm, mul_comm, mod_by_monic_add_div _ hg], },
end

end polynomial

end one_denominator

.

section two_denominators

lemma div_eq_quo_add_rem_div_add_rem_div {f g₁ g₂ : R[X]}
  (hg₁ : g₁.monic) (hg₂ : g₂.monic) (hcoprime : is_coprime g₁ g₂ ) :
  ∃ q r₁ r₂ : R[X], r₁.degree < g₁.degree ∧ r₂.degree < g₂.degree ∧
  (↑f : K) / (↑g₁ * ↑g₂) = ↑q + ↑r₁ / ↑g₁ + ↑r₂ / ↑g₂ :=
begin
  rcases hcoprime with ⟨ c, d, hcd ⟩,
  refine ⟨ (f*d) /ₘ g₁ + (f*c) /ₘ g₂ , (f*d) %ₘ g₁ , (f*c) %ₘ g₂ ,
    (degree_mod_by_monic_lt _ hg₁) , (degree_mod_by_monic_lt _ hg₂) , _⟩,
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

end two_denominators

.

section n_denominators

example (ι : Type) (s : finset ι) (a : ι) : a ∈ (s : set ι) ↔ a ∈ s := finset.mem_coe

open_locale big_operators classical

lemma div_eq_quo_add_sum_rem_div (f : R[X]) {ι : Type*} {g : ι → R[X]} (s : finset ι)
  (hg : ∀ i ∈ s, (g i).monic)
  (hcop : set.pairwise ↑s (λ i j, is_coprime (g i) (g j))) :
  ∃ (q : R[X]) (r : ι → R[X]), (∀ i ∈ s, (r i).degree < (g i).degree) ∧
  (↑f : K) / ∏ i in s, ↑(g i) = ↑q + ∑ i in s, ↑(r i) / ↑(g i) :=
begin
  induction s using finset.induction_on with a b hab Hind f generalizing f,
  { refine ⟨f, (λ (i : ι), (0 : R[X])), λ i, _, by simp⟩,
    rintro ⟨⟩, },
  { obtain ⟨q₀, r₁, r₂, hdeg₁, hdeg₂, (hf : (↑f : K) / _ = _)⟩ :=
      div_eq_quo_add_rem_div_add_rem_div R K
      (_ : monic (g a))
      (_ : monic ∏ (i : ι) in b, (g i))
      _,
    { obtain ⟨q, r, hrdeg, IH⟩ := Hind (λ i hi, hg i (finset.mem_insert_of_mem hi))
        (set.pairwise.mono (show (b : set ι) ⊆ (insert a b : finset ι),
          from finset.coe_subset.2 $ λ i hi, finset.mem_insert_of_mem hi) hcop) r₂,
      refine ⟨q₀ + q, λ i, if i = a then r₁ else r i, _, _⟩,
      { intro i,
        split_ifs with h1,
        { cases h1,
          intro _,
          exact hdeg₁, },
        { intro hi,
          refine hrdeg i (finset.mem_of_mem_insert_of_ne hi h1), }, },
      norm_cast at ⊢ hf IH,
      rw [finset.prod_insert hab, hf, IH, finset.sum_insert hab, if_pos rfl],
      transitivity (↑(q₀ + q : R[X]) : K) + (↑r₁ / ↑(g a) + ∑ (i : ι) in b, ↑(r i) / ↑(g i)),
      { push_cast, ring, },
      congr' 2,
      refine finset.sum_congr rfl (λ x hxb, _),
      have hxa : ¬(x = a),
      { rintro rfl,
        exact hab hxb, },
      rw if_neg hxa, },
    { exact hg a (b.mem_insert_self a), },
    { refine monic_prod_of_monic _ _ (λ i hi, hg i (finset.mem_insert_of_mem hi)), },
    { refine is_coprime.prod_right (λ i hi, hcop (finset.mem_coe.2 (b.mem_insert_self a))
       (finset.mem_coe.2 (finset.mem_insert_of_mem hi)) _),
      rintro rfl,
      exact hab hi, }, },
end

end n_denominators

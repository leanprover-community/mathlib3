/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark.
-/
import data.polynomial
import algebra.polynomial.big_operators
open polynomial finset

/-
# Polynomials
Here we have utility lemmas for polynomials.
For results that are useful for programming, see data/polynomial.lean
## Main results
- `card_pred_coeff_prod_X_sub_C` : yields that the trace is a coefficient of the characteristic polynomial
-/

noncomputable theory
open_locale big_operators

universes u w

variables {R : Type u} {α : Type w}

namespace polynomial

variables [comm_ring R]

@[simp]
lemma monic_degree_one {p : polynomial R} (hp : p.monic) :
p.nat_degree = 0 ↔ p = 1 :=
begin
  split; intro h,
  swap, { rw h, exact nat_degree_one },
  have h' := h,
  rw polynomial.nat_degree_eq_zero_iff_degree_le_zero at h,
  rw polynomial.degree_le_zero_iff at h,
  rw h, rw ← h',
  rw ← leading_coeff,
  rw polynomial.monic.leading_coeff hp,
  simp,
end

lemma monic.nat_degree_mul_eq [nontrivial R] {p q : polynomial R} (hp : p.monic) (hq : q.monic) :
(p * q).nat_degree = p.nat_degree + q.nat_degree :=
by { apply nat_degree_mul_eq', rw [hp.leading_coeff, hq.leading_coeff], simp }

/-- The second-highest coefficient, or 0 for constants -/
def next_coeff (p : polynomial R) : R := ite (p.nat_degree = 0) 0 p.coeff (p.nat_degree - 1)

lemma next_coeff_mul_monic {p q : polynomial R} (hp : monic p) (hq : monic q) :
next_coeff (p * q) = next_coeff p + next_coeff q :=
begin
  classical,
  by_cases h : nontrivial R, swap,
  { rw nontrivial_iff at h, push_neg at h, apply h, },
  letI := h,
  have := monic.nat_degree_mul_eq hp hq,
  dsimp [next_coeff], rw this, simp [hp, hq], clear this,
  split_ifs; try {tauto <|> simp *},
  rename h_2 hp0, rename h_3 hq0, clear h_1,
  rw ← monic_degree_one at hp0 hq0, any_goals {assumption},
  rw coeff_mul,
  transitivity ∑ (x : ℕ × ℕ) in _, ite (x.fst = p.nat_degree ∨ x.snd = q.nat_degree) (p.coeff x.fst * q.coeff x.snd) 0,
  { apply sum_congr rfl,
    intros x hx, split_ifs with hx1, refl,
    simp only [nat.mem_antidiagonal] at hx,
    push_neg at hx1, cases hx1 with hxp hxq,
    by_cases h_deg : x.fst < p.nat_degree,
    { suffices : q.coeff x.snd = 0, simp [this],
      apply coeff_eq_zero_of_nat_degree_lt, omega },
    suffices : p.coeff x.fst = 0, simp [this],
    apply coeff_eq_zero_of_nat_degree_lt, omega,
  },
  rw sum_ite, simp,
  have : filter (λ (x : ℕ × ℕ), x.fst = p.nat_degree ∨ x.snd = q.nat_degree) (nat.antidiagonal (p.nat_degree + q.nat_degree - 1))
    = {(p.nat_degree - 1, q.nat_degree),(p.nat_degree, q.nat_degree - 1)},
  { ext, rw mem_filter, simp only [mem_insert, mem_singleton, nat.mem_antidiagonal],
    split; intro ha,
    { rcases ha with ⟨ha, _ | _ ⟩,
      { right, ext, assumption, omega, },
      left, ext, omega, assumption },
    split, cases ha; { rw ha, ring, omega },
    cases ha; { rw ha, simp }},
  rw [this, sum_insert, sum_singleton],
  iterate 2 { rw [← leading_coeff, monic.leading_coeff] };
  { assumption <|> simp },
  rw mem_singleton,
  suffices : p.nat_degree - 1 ≠ p.nat_degree, simp [this],
  omega,
end

@[simp]
lemma next_coeff_C_eq_zero (c : R) :
next_coeff (C c) = 0 := by {rw next_coeff, simp}

lemma next_coeff_of_pos_nat_degree (p : polynomial R) :
  0 < p.nat_degree → next_coeff p = p.coeff (p.nat_degree - 1) :=
by { intro h, rw next_coeff, rw if_neg, intro contra, rw contra at h, apply lt_irrefl 0 h, }

@[simp]
lemma next_coeff_X_sub_C_eq_neg_C [nontrivial R] (c : R) : next_coeff (X - C c) = - c :=
by { rw next_coeff_of_pos_nat_degree; simp [nat_degree_X_sub_C] }

lemma next_coeff_prod_monic
  (s : finset α) (f : α → polynomial R) (h : ∀ a : α, a ∈ s → monic (f a)) :
next_coeff (s.prod f) = s.sum (λ (a : α), next_coeff (f a)) :=
begin
  classical,
  revert h, apply finset.induction_on s,
  { simp only [finset.not_mem_empty, forall_prop_of_true, forall_prop_of_false, finset.sum_empty,
  finset.prod_empty, not_false_iff, forall_true_iff],
  rw ← C_1, rw next_coeff_C_eq_zero },
  { intros a s ha hs monic,
    rw finset.prod_insert ha,
    rw finset.sum_insert ha,
    rw next_coeff_mul_monic (monic a (finset.mem_insert_self a s)), swap,
    { apply monic_prod_monic, intros b bs,
      apply monic, apply finset.mem_insert_of_mem bs },
    { refine congr rfl (hs _),
      intros b bs, apply monic, apply finset.mem_insert_of_mem bs }}
end

--sort of a special case of Vieta?
lemma card_pred_coeff_prod_X_sub_C' [nontrivial R] {s : finset α} (f : α → R) :
next_coeff ∏ i in s, (X - C (f i)) = -s.sum f :=
by { rw next_coeff_prod_monic; { simp [monic_X_sub_C] } }

lemma card_pred_coeff_prod_X_sub_C [nontrivial R] (s : finset α) (f : α → R) (hs : 0 < s.card) :
(∏ i in s, (X - C (f i))).coeff (s.card - 1) = -s.sum f :=
begin
  convert card_pred_coeff_prod_X_sub_C' (by assumption),
  rw next_coeff, split_ifs,
  { rw nat_degree_prod_eq_of_monic at h,
    swap, { intros, apply monic_X_sub_C },
    rw sum_eq_zero_iff at h,
    simp_rw nat_degree_X_sub_C at h, contrapose! h, norm_num,
    exact multiset.card_pos_iff_exists_mem.mp hs },
  congr, rw nat_degree_prod_eq_of_monic; { simp [nat_degree_X_sub_C, monic_X_sub_C] },
end

lemma pow_comp (p q : polynomial R) (k : ℕ) : (p ^ k).comp q = (p.comp q) ^ k :=
begin
  unfold comp, rw ← coe_eval₂_ring_hom, apply ring_hom.map_pow,
end


end polynomial

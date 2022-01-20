/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import data.fintype.basic
import data.int.parity
import algebra.big_operators.order
import tactic.ring
import tactic.noncomm_ring

/-!
# IMO 1998 Q2
In a competition, there are `a` contestants and `b` judges, where `b ≥ 3` is an odd integer. Each
judge rates each contestant as either "pass" or "fail". Suppose `k` is a number such that, for any
two judges, their ratings coincide for at most `k` contestants. Prove that `k / a ≥ (b - 1) / (2b)`.

## Solution
The problem asks us to think about triples consisting of a contestant and two judges whose ratings
agree for that contestant. We thus consider the subset `A ⊆ C × JJ` of all such incidences of
agreement, where `C` and `J` are the sets of contestants and judges, and `JJ = J × J − {(j, j)}`. We
have natural maps: `left : A → C` and `right: A → JJ`. We count the elements of `A` in two ways: as
the sum of the cardinalities of the fibres of `left` and as the sum of the cardinalities of the
fibres of `right`. We obtain an upper bound on the cardinality of `A` from the count for `right`,
and a lower bound from the count for `left`. These two bounds combine to the required result.

First consider the map `right : A → JJ`. Since the size of any fibre over a point in JJ is bounded
by `k` and since `|JJ| = b^2 - b`, we obtain the upper bound: `|A| ≤ k(b^2−b)`.

Now consider the map `left : A → C`. The fibre over a given contestant `c ∈ C` is the set of
ordered pairs of (distinct) judges who agree about `c`. We seek to bound the cardinality of this
fibre from below. Minimum agreement for a contestant occurs when the judges' ratings are split as
evenly as possible. Since `b` is odd, this occurs when they are divided into groups of size
`(b−1)/2` and `(b+1)/2`. This corresponds to a fibre of cardinality `(b-1)^2/2` and so we obtain
the lower bound: `a(b-1)^2/2 ≤ |A|`.

Rearranging gives the result.
-/

open_locale classical
noncomputable theory

/-- An ordered pair of judges. -/
abbreviation judge_pair (J : Type*) := J × J

/-- A triple consisting of contestant together with an ordered pair of judges. -/
abbreviation agreed_triple (C J : Type*) := C × (judge_pair J)

variables {C J : Type*} (r : C → J → Prop)

/-- The first judge from an ordered pair of judges. -/
abbreviation judge_pair.judge₁ : judge_pair J → J := prod.fst

/-- The second judge from an ordered pair of judges. -/
abbreviation judge_pair.judge₂ : judge_pair J → J := prod.snd

/-- The proposition that the judges in an ordered pair are distinct. -/
abbreviation judge_pair.distinct (p : judge_pair J) := p.judge₁ ≠ p.judge₂

/-- The proposition that the judges in an ordered pair agree about a contestant's rating. -/
abbreviation judge_pair.agree (p : judge_pair J) (c : C) := r c p.judge₁ ↔ r c p.judge₂

/-- The contestant from the triple consisting of a contestant and an ordered pair of judges. -/
abbreviation agreed_triple.contestant : agreed_triple C J → C := prod.fst

/-- The ordered pair of judges from the triple consisting of a contestant and an ordered pair of
judges. -/
abbreviation agreed_triple.judge_pair : agreed_triple C J → judge_pair J := prod.snd

@[simp] lemma judge_pair.agree_iff_same_rating (p : judge_pair J) (c : C) :
  p.agree r c ↔ (r c p.judge₁ ↔ r c p.judge₂) := iff.rfl

/-- The set of contestants on which two judges agree. -/
def agreed_contestants [fintype C] (p : judge_pair J) : finset C :=
finset.univ.filter (λ c, p.agree r c)

section

variables [fintype J] [fintype C]

/-- All incidences of agreement. -/
def A : finset (agreed_triple C J) := finset.univ.filter (λ (a : agreed_triple C J),
  a.judge_pair.agree r a.contestant ∧ a.judge_pair.distinct)

lemma A_maps_to_off_diag_judge_pair (a : agreed_triple C J) :
  a ∈ A r → a.judge_pair ∈ finset.off_diag (@finset.univ J _) :=
by simp [A, finset.mem_off_diag]

lemma A_fibre_over_contestant (c : C) :
  finset.univ.filter (λ (p : judge_pair J), p.agree r c ∧ p.distinct) =
  ((A r).filter (λ (a : agreed_triple C J), a.contestant = c)).image prod.snd :=
begin
  ext p,
  simp only [A, finset.mem_univ, finset.mem_filter, finset.mem_image, true_and, exists_prop],
  split,
  { rintros ⟨h₁, h₂⟩, refine ⟨(c, p), _⟩, finish, },
  { intros h, finish, },
end

lemma A_fibre_over_contestant_card (c : C) :
  (finset.univ.filter (λ (p : judge_pair J), p.agree r c ∧ p.distinct)).card =
  ((A r).filter (λ (a : agreed_triple C J), a.contestant = c)).card :=
by { rw A_fibre_over_contestant r, apply finset.card_image_of_inj_on, tidy, }

lemma A_fibre_over_judge_pair {p : judge_pair J} (h : p.distinct) :
  agreed_contestants r p =
  ((A r).filter(λ (a : agreed_triple C J), a.judge_pair = p)).image agreed_triple.contestant :=
begin
  dunfold A agreed_contestants, ext c, split; intros h,
  { rw finset.mem_image, refine ⟨⟨c, p⟩, _⟩, finish, },
  { finish, },
end

lemma A_fibre_over_judge_pair_card {p : judge_pair J} (h : p.distinct) :
  (agreed_contestants r p).card =
  ((A r).filter(λ (a : agreed_triple C J), a.judge_pair = p)).card :=
by { rw A_fibre_over_judge_pair r h, apply finset.card_image_of_inj_on, tidy, }

lemma A_card_upper_bound
  {k : ℕ} (hk : ∀ (p : judge_pair J), p.distinct → (agreed_contestants r p).card ≤ k) :
  (A r).card ≤ k * ((fintype.card J) * (fintype.card J) - (fintype.card J)) :=
begin
  change _ ≤ k * ((finset.card _ ) * (finset.card _ ) - (finset.card _ )),
  rw ← finset.off_diag_card,
  apply finset.card_le_mul_card_image_of_maps_to (A_maps_to_off_diag_judge_pair r),
  intros p hp,
  have hp' : p.distinct, { simp [finset.mem_off_diag] at hp, exact hp, },
  rw ← A_fibre_over_judge_pair_card r hp', apply hk, exact hp',
end

end

lemma add_sq_add_sq_sub {α : Type*} [ring α] (x y : α) :
  (x + y) * (x + y) + (x - y) * (x - y) = 2*x*x + 2*y*y :=
by noncomm_ring

lemma norm_bound_of_odd_sum {x y z : ℤ} (h : x + y = 2*z + 1) :
  2*z*z + 2*z + 1 ≤ x*x + y*y :=
begin
  suffices : 4*z*z + 4*z + 1 + 1 ≤ 2*x*x + 2*y*y,
  { rw ← mul_le_mul_left (@zero_lt_two _ _ int.nontrivial), convert this; ring, },
  have h' : (x + y) * (x + y) = 4*z*z + 4*z + 1, { rw h, ring, },
  rw [← add_sq_add_sq_sub, h', add_le_add_iff_left],
  suffices : 0 < (x - y) * (x - y), { apply int.add_one_le_of_lt this, },
  rw [mul_self_pos, sub_ne_zero], apply int.ne_of_odd_add ⟨z, h⟩,
end

section

variables [fintype J]

lemma judge_pairs_card_lower_bound {z : ℕ} (hJ : fintype.card J = 2*z + 1) (c : C) :
  2*z*z + 2*z + 1 ≤ (finset.univ.filter (λ (p : judge_pair J), p.agree r c)).card :=
begin
  let x := (finset.univ.filter (λ j, r c j)).card,
  let y := (finset.univ.filter (λ j, ¬ r c j)).card,
  have h : (finset.univ.filter (λ (p : judge_pair J), p.agree r c)).card = x*x + y*y,
  { simp [← finset.filter_product_card], },
  rw h, apply int.le_of_coe_nat_le_coe_nat, simp only [int.coe_nat_add, int.coe_nat_mul],
  apply norm_bound_of_odd_sum,
  suffices : x + y = 2*z + 1, { simp [← int.coe_nat_add, this], },
  rw [finset.filter_card_add_filter_neg_card_eq_card, ← hJ], refl,
end

lemma distinct_judge_pairs_card_lower_bound {z : ℕ} (hJ : fintype.card J = 2*z + 1) (c : C) :
  2*z*z ≤ (finset.univ.filter (λ (p : judge_pair J), p.agree r c ∧ p.distinct)).card :=
begin
  let s := finset.univ.filter (λ (p : judge_pair J), p.agree r c),
  let t := finset.univ.filter (λ (p : judge_pair J), p.distinct),
  have hs : 2*z*z + 2*z + 1 ≤ s.card, { exact judge_pairs_card_lower_bound r hJ c, },
  have hst : s \ t = finset.univ.diag,
  { ext p, split; intros,
    { finish, },
    { suffices : p.judge₁ = p.judge₂, { simp [this], }, finish, }, },
  have hst' : (s \ t).card = 2*z + 1, { rw [hst, finset.diag_card, ← hJ], refl, },
  rw [finset.filter_and, ← finset.sdiff_sdiff_self_left s t, finset.card_sdiff],
  { rw hst', rw add_assoc at hs, apply le_tsub_of_add_le_right hs, },
  { apply finset.sdiff_subset, },
end

lemma A_card_lower_bound [fintype C] {z : ℕ} (hJ : fintype.card J = 2*z + 1) :
  2*z*z * (fintype.card C) ≤ (A r).card :=
begin
  have h : ∀ a, a ∈ A r → prod.fst a ∈ @finset.univ C _, { intros, apply finset.mem_univ, },
  apply finset.mul_card_image_le_card_of_maps_to h,
  intros c hc,
  rw ← A_fibre_over_contestant_card,
  apply distinct_judge_pairs_card_lower_bound r hJ,
end

end

local notation x `/` y := (x : ℚ) / y

lemma clear_denominators {a b k : ℕ} (ha : 0 < a) (hb : 0 < b) :
  (b - 1) / (2 * b) ≤ k / a ↔ (b - 1) * a ≤ k * (2 * b) :=
by rw div_le_div_iff; norm_cast; simp [ha, hb]

theorem imo1998_q2 [fintype J] [fintype C]
  (a b k : ℕ) (hC : fintype.card C = a) (hJ : fintype.card J = b) (ha : 0 < a) (hb : odd b)
  (hk : ∀ (p : judge_pair J), p.distinct → (agreed_contestants r p).card ≤ k) :
  (b - 1) / (2 * b) ≤ k / a :=
begin
  rw clear_denominators ha (nat.odd_gt_zero hb),
  obtain ⟨z, hz⟩ := hb, rw hz at hJ, rw hz,
  have h := le_trans (A_card_lower_bound r hJ) (A_card_upper_bound r hk),
  rw [hC, hJ] at h,
  -- We are now essentially done; we just need to bash `h` into exactly the right shape.
  have hl : k * ((2 * z + 1) * (2 * z + 1) - (2 * z + 1)) = (k * (2 * (2 * z + 1))) * z,
  { simp only [add_mul, two_mul, mul_comm, mul_assoc], finish, },
  have hr : 2 * z * z * a = 2 * z * a * z, { ring, },
  rw [hl, hr] at h,
  cases z,
  { simp, },
  { exact le_of_mul_le_mul_right h z.succ_pos, },
end

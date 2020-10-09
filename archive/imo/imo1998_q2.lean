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
two judges, their rating coincide for at most `k` contestants. Prove that `k / a ≥ (b - 1) / (2b)`.

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

local notation x `/` y := (x : ℚ) / y

variables {C J : Type*} (r : C → J → Prop)

/-- The set of contestants on which two judges agree. -/
def same_rating [fintype C] (j₁ j₂ : J) : finset C := finset.univ.filter (λ c, r c j₁ = r c j₂)

section

variables [fintype J] [fintype C]

/-- All incidences of agreement. -/
def A : finset (C × J × J) :=
finset.univ.filter (λ (a : C × J × J), r a.1 a.2.1 = r a.1 a.2.2 ∧ a.2.1 ≠ a.2.2)

lemma A_snd_mem (a : C × J × J) : a ∈ A r → a.2 ∈ finset.off_diag (@finset.univ J _) :=
by simp [A, finset.mem_off_diag]

lemma A_fst_fibre (c : C) :
  finset.univ.filter (λ (x : J × J), r c x.1 = r c x.2 ∧ x.1 ≠ x.2) =
  ((A r).filter (λ (x : C × J × J), x.1 = c)).image prod.snd :=
begin
  ext x,
  simp only [A, finset.mem_univ, finset.mem_filter, finset.mem_image, true_and, exists_prop],
  split,
  { rintros ⟨h₁, h₂⟩, refine ⟨(c, x), _⟩, finish, },
  { intros h, finish, },
end

lemma A_fst_fibre_card (c : C) :
  (finset.univ.filter (λ (x : J × J), r c x.1 = r c x.2 ∧ x.1 ≠ x.2)).card =
  ((A r).filter (λ (x : C × J × J), x.1 = c)).card :=
by { rw A_fst_fibre r, apply finset.card_image_of_inj_on, tidy, }

lemma A_snd_fibre {j₁ j₂ : J} (hj : j₁ ≠ j₂) :
  same_rating r j₁ j₂ = ((A r).filter(λ (x : C × J × J), x.2 = (j₁, j₂))).image prod.fst :=
by { dunfold A same_rating, ext, split; finish, }

lemma A_snd_fibre_card {j₁ j₂ : J} (hj : j₁ ≠ j₂) :
  (same_rating r j₁ j₂).card = ((A r).filter(λ (x : C × J × J), x.2 = (j₁, j₂))).card :=
by { rw A_snd_fibre r hj, apply finset.card_image_of_inj_on, tidy, }

lemma agreement_upper_bound {k : ℕ} (hk : ∀ j₁ j₂, j₁ ≠ j₂ → (same_rating r j₁ j₂).card ≤ k) :
  (A r).card ≤ k * ((fintype.card J) * (fintype.card J) - (fintype.card J)) :=
begin
  change _ ≤ k * ((finset.card _ ) * (finset.card _ ) - (finset.card _ )),
  rw ← finset.off_diag_card,
  apply finset.card_le_mul_card_image_of_maps_to (A_snd_mem r),
  rintros ⟨j₁, j₂⟩ hj,
  have hj' : j₁ ≠ j₂, { simp [finset.mem_off_diag] at hj, exact hj, },
  rw ← A_snd_fibre_card r hj', apply hk, exact hj',
end

end

lemma add_sq_add_sq_sub {α : Type*} [ring α] (x y : α) :
  (x + y) * (x + y) + (x - y) * (x - y) = 2*x*x + 2*y*y :=
by noncomm_ring

lemma norm_bound_of_odd_sum {x y z : ℤ} (h : x + y = 2*z + 1) :
  2*z*z + 2*z + 1 ≤ x*x + y*y :=
begin
  suffices : 4*z*z + 4*z + 1 + 1 ≤ 2*x*x + 2*y*y,
  { rw ← mul_le_mul_left zero_lt_two, convert this; ring, },
  have h' : (x + y) * (x + y) = 4*z*z + 4*z + 1, { rw h, ring, },
  rw [← add_sq_add_sq_sub, h', add_le_add_iff_left],
  suffices : 0 < (x - y) * (x - y), { apply int.add_one_le_of_lt this, },
  apply mul_self_pos, rw sub_ne_zero, apply int.ne_of_odd_sum ⟨z, h⟩,
end

section

variables [fintype J]

lemma agreement_lower_bound {z : ℕ} (hJ : fintype.card J = 2*z + 1) (c : C) :
  2*z*z + 2*z + 1 ≤ (finset.univ.filter (λ (x : J × J), r c x.1 = r c x.2)).card :=
begin
  let x := (finset.univ.filter (λ j, r c j)).card,
  let y := (finset.univ.filter (λ j, ¬ r c j)).card,
  have h : (finset.univ.filter (λ (x : J × J), r c x.1 = r c x.2)).card = x*x + y*y,
  { simp [← finset.filter_product_card], },
  rw h, apply int.le_of_coe_nat_le_coe_nat, simp only [int.coe_nat_add, int.coe_nat_mul],
  apply norm_bound_of_odd_sum,
  suffices : x + y = 2*z + 1, { simp [← int.coe_nat_add, this], },
  rw [finset.filter_card_add_filter_neg_card_eq_card, ← hJ], refl,
end

lemma agreement_lower_bound' {z : ℕ} (hJ : fintype.card J = 2*z + 1) (c : C) :
  2*z*z ≤ (finset.univ.filter (λ (x : J × J), r c x.1 = r c x.2 ∧ x.1 ≠ x.2)).card :=
begin
  let s := finset.univ.filter (λ (x : J × J), r c x.1 = r c x.2),
  let t := finset.univ.filter (λ (x : J × J), x.1 ≠ x.2),
  have hs : 2*z*z + 2*z + 1 ≤ s.card, { exact agreement_lower_bound r hJ c, },
  have hst : s \ t = finset.univ.diag, { ext, split; intros; finish, },
  have hst' : (s \ t).card = 2*z + 1, { rw [hst, finset.diag_card, ← hJ], refl, },
  rw [finset.filter_and, finset.inter_eq_sdiff_sdiff s t, finset.card_sdiff],
  { rw hst', rw add_assoc at hs, apply nat.le_sub_right_of_add_le hs, },
  { apply finset.sdiff_subset_self, },
end

lemma agreement_lower_bound'' [fintype C] {z : ℕ} (hJ : fintype.card J = 2*z + 1) :
  2*z*z * (fintype.card C) ≤ (A r).card :=
begin
  have A_fst_mem : ∀ a, a ∈ A r → prod.fst a ∈ @finset.univ C _, { intros, apply finset.mem_univ, },
  apply finset.mul_card_image_le_card_of_maps_to A_fst_mem,
  intros c hc,
  rw ← A_fst_fibre_card,
  apply agreement_lower_bound' r hJ,
end

end

lemma clear_denominators {a b k : ℕ} (ha : 0 < a) (hb : 0 < b) :
  (b - 1) / (2 * b) ≤ k / a ↔ (b - 1) * a ≤ k * (2 * b) :=
begin
  rw div_le_div_iff,
  { convert nat.cast_le; finish, },
  { simp only [hb, zero_lt_mul_right, zero_lt_bit0, nat.cast_pos, zero_lt_one], },
  { simp only [ha, nat.cast_pos], },
end

theorem imo1998_q2 [fintype J] [fintype C]
  (a b k : ℕ) (hC : fintype.card C = a) (hJ : fintype.card J = b) (ha : 0 < a) (hb : odd b)
  (hk : ∀ j₁ j₂, j₁ ≠ j₂ → (same_rating r j₁ j₂).card ≤ k) :
  (b - 1) / (2 * b) ≤ k / a :=
begin
  rw clear_denominators ha (nat.odd_gt_zero hb),
  obtain ⟨z, hz⟩ := hb, rw hz at hJ, rw hz,
  have h := le_trans (agreement_lower_bound'' r hJ) (agreement_upper_bound r hk),
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

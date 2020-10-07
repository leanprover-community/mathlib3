/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import data.fintype.basic
import data.int.parity
import algebra.big_operators.order
import tactic.nth_rewrite
import tactic.ring
import tactic.noncomm_ring

/-!
# IMO 1998 Q2
In a competition, there are `a` contestants and `b` judges, where `b ≥ 3` is an odd integer. Each
judge rates each contestant as either "pass" or "fail". Suppose `k` is a number such that, for any
two judges, their rating coincide for at most `k` contestants. Prove that `k / a ≥ (b - 1) / (2b)`.
-/

open_locale classical
noncomputable theory

variables {C J : Type*} (r : C → J → Prop)

/-- The set of contestants on which two judges agree. -/
def same_rating [fintype C] (j₁ j₂ : J) : finset C := finset.univ.filter (λ c, r c j₁ = r c j₂)

section upper_bound

variables [fintype J] [fintype C]

/-- All incidences of agreement. -/
def A : finset (C × J × J) :=
finset.univ.filter (λ (a : C × J × J), r a.1 a.2.1 = r a.1 a.2.2 ∧ a.2.1 ≠ a.2.2)

lemma A_snd_mem (a : C × J × J) : a ∈ A r → a.2 ∈ finset.off_diag (@finset.univ J _) :=
by simp [A, finset.mem_off_diag]

lemma A_left_fibre (c : C) :
  finset.univ.filter (λ (x : J × J), r c x.1 = r c x.2 ∧ x.1 ≠ x.2) =
  ((A r).filter (λ (x : C × J × J), x.1 = c)).image prod.snd :=
begin
  ext x,
  simp only [A, finset.mem_univ, finset.mem_filter, finset.mem_image, true_and, exists_prop],
  split,
  { rintros ⟨h₁, h₂⟩, refine ⟨(c, x), _⟩, finish, },
  { intros h, finish, },
end

lemma A_left_fibre_card (c : C) :
  (finset.univ.filter (λ (x : J × J), r c x.1 = r c x.2 ∧ x.1 ≠ x.2)).card =
  ((A r).filter (λ (x : C × J × J), x.fst = c)).card :=
by { rw A_left_fibre r, apply finset.card_image_of_inj_on, tidy, }

lemma A_right_fibre {j₁ j₂ : J} (hj : j₁ ≠ j₂) :
  same_rating r j₁ j₂ = ((A r).filter(λ (x : C × J × J), x.2 = (j₁, j₂))).image prod.fst :=
by { dunfold A same_rating, ext, split; finish, }

lemma A_right_fibre_card {j₁ j₂ : J} (hj : j₁ ≠ j₂) :
  (same_rating r j₁ j₂).card = ((A r).filter(λ (x : C × J × J), x.2 = (j₁, j₂))).card :=
by { rw A_right_fibre r hj, apply finset.card_image_of_inj_on, tidy, }

lemma agreement_upper_bound {k : ℕ} (hk : ∀ j₁ j₂, j₁ ≠ j₂ → (same_rating r j₁ j₂).card ≤ k) :
  (A r).card ≤ k * ((fintype.card J) * (fintype.card J) - (fintype.card J)) :=
begin
  change _ ≤ k * ((finset.card _ ) * (finset.card _ ) - (finset.card _ )),
  rw ← finset.off_diag_card,
  apply finset.card_le_mul_card_image_of_maps_to (A_snd_mem r),
  rintros ⟨j₁, j₂⟩ hj,
  have hj' : j₁ ≠ j₂, { simp [finset.mem_off_diag] at hj, exact hj, },
  rw ← A_right_fibre_card r hj', apply hk, exact hj',
end

end upper_bound

lemma add_sq_add_sq_sub {α : Type*} [ring α] (x y : α) :
  (x + y) * (x + y) + (x - y) * (x - y) = 2*x*x + 2*y*y :=
by noncomm_ring

lemma norm_bound_of_odd_sum (x y z : ℤ) (h : x + y = 2*z + 1) :
  2*z*z + 2*z + 1 ≤ x*x + y*y :=
begin
  suffices : 4*z*z + 4*z + 1 + 1 ≤ 2*x*x + 2*y*y,
  { rw ← mul_le_mul_left zero_lt_two, convert this; ring, },
  have h' : (x + y) * (x + y) = 4*z*z + 4*z + 1, { rw h, ring, },
  rw [← add_sq_add_sq_sub, h', add_le_add_iff_left],
  suffices : 0 < (x - y) * (x - y), { apply int.add_one_le_of_lt this, },
  apply mul_self_pos, rw sub_ne_zero, apply int.ne_of_odd_sum ⟨z, h⟩,
end

section lower_bound

variables [fintype J]

lemma agreement_lower_bound (z : ℕ) (hJ : fintype.card J = 2*z + 1) (c : C) :
  2*z*z + 2*z + 1 ≤ (finset.univ.filter (λ (x : J × J), r c x.1 = r c x.2)).card :=
begin
  let x := (finset.univ.filter (λ j, r c j)).card,
  let y := (finset.univ.filter (λ j, ¬ r c j)).card,
  have h : (finset.univ.filter (λ (x : J × J), r c x.1 = r c x.2)).card = x*x + y*y,
  { simp [← finset.filter_product_card], },
  rw h, apply int.le_of_coe_nat_le_coe_nat, simp only [int.coe_nat_add, int.coe_nat_mul],
  apply norm_bound_of_odd_sum ↑x ↑y ↑z,
  suffices : x + y = 2*z + 1, { simp [← int.coe_nat_add, this], },
  rw [finset.filter_card_add_filter_neg_card_eq_card, ← hJ], refl,
end

lemma agreement_lower_bound' (z : ℕ) (hJ : fintype.card J = 2*z + 1) (c : C) :
  2*z*z ≤ (finset.univ.filter (λ (x : J × J), r c x.1 = r c x.2 ∧ x.1 ≠ x.2)).card :=
begin
  let s := finset.univ.filter (λ (x : J × J), r c x.1 = r c x.2),
  let t := finset.univ.filter (λ (x : J × J), x.1 ≠ x.2),
  have hs : 2*z*z + 2*z + 1 ≤ s.card, { exact agreement_lower_bound r z hJ c, },
  have hst : s \ t = finset.univ.diag, { ext, split; intros; finish, },
  have hst' : (s \ t).card = 2*z + 1, { rw [hst, finset.diag_card, ← hJ], refl, },
  rw [finset.filter_and, finset.inter_eq_sdiff_sdiff s t, finset.card_sdiff],
  { rw hst', rw add_assoc at hs, apply nat.le_sub_right_of_add_le hs, },
  { apply finset.sdiff_subset_self, },
end

lemma agreement_lower_bound'' [fintype C] (z : ℕ) (hJ : fintype.card J = 2*z + 1) :
  2*z*z * (fintype.card C) ≤ (A r).card :=
begin
  have A_fst_mem : ∀ a, a ∈ A r → prod.fst a ∈ @finset.univ C _, { intros, apply finset.mem_univ, },
  apply finset.mul_card_image_le_card_of_maps_to A_fst_mem,
  intros c hc,
  rw ← A_left_fibre_card,
  apply agreement_lower_bound' r z hJ,
end

end lower_bound

local notation x `/` y := (x : ℚ) / y

-- ## TODO fix up disgusting proof below.
theorem imo1998_q2 [fintype J] [fintype C]
  (a b k : ℕ) (hC : fintype.card C = a) (hJ : fintype.card J = b) (ha : 0 < a) (hb : odd b)
  (hk : ∀ j₁ j₂, j₁ ≠ j₂ → (same_rating r j₁ j₂).card ≤ k) :
  (b - 1) / (2*b) ≤ k / a :=
begin
  obtain ⟨B, hB⟩ := hb, rw hB at hJ, rw hB,
  have h := le_trans (agreement_lower_bound'' r B hJ) (agreement_upper_bound r hk),
  rw [hC, hJ] at h,
  have h' : (2 * B + 1) * (2 * B + 1) - (2 * B + 1) = 2 * (2 * B + 1) * B,
  { simp only [add_mul, two_mul, mul_comm, mul_assoc], finish, },
  have foo : 2 * B * B * a = a * 2 * B * B, { rw [mul_comm, ← mul_assoc, ← mul_assoc], },
  rw [h', ← mul_assoc, foo] at h,
  cases B,
  { apply div_nonneg; simp, },
  { have h'' := le_of_mul_le_mul_right h B.succ_pos, -- Maybe should cast to ℚ up here?
    simp,
    rw div_le_div_iff,
    { rw [mul_comm, ← mul_assoc],
      nth_rewrite 1 ← nat.cast_one,
      nth_rewrite 4 ← nat.cast_one,
      nth_rewrite 5 ← nat.cast_one,
      rw ← nat.cast_two,
      repeat { rw ← nat.cast_add <|> rw ← nat.cast_mul },
      rw nat.cast_le, exact h'', },
    { apply mul_pos zero_lt_two, refine add_pos _ zero_lt_one, apply mul_pos zero_lt_two,
      rw [← nat.cast_one, ← nat.cast_add, nat.cast_pos], exact nat.succ_pos', },
    { rw nat.cast_pos, exact ha, }, },
end

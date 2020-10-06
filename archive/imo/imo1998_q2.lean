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

/-!
# IMO 1998 Q2
In a competition, there are `a` contestants and `b` judges, where `b ≥ 3` is an odd integer. Each
judge rates each contestant as either "pass" or "fail". Suppose `k` is a number such that, for any
two judges, their rating coincide for at most `k` contestants. Prove that `k / a ≥ (b - 1) / (2b)`.
-/

-- ## TODO fix up disgusting proofs below.

open_locale classical
noncomputable theory

variables {C J : Type*} (r : C → J → Prop)

/-- The set of contestants on which two judges agree. -/
def same_rating [fintype C] (j₁ j₂ : J) : finset C := finset.univ.filter (λ c, r c j₁ = r c j₂)

/-- All incidences of agreement. -/
def A [fintype J] [fintype C] : finset (C × J × J) :=
finset.univ.filter (λ (a : C × J × J), r a.1 a.2.1 = r a.1 a.2.2 ∧ a.2.1 ≠ a.2.2)

lemma agreement_upper_bound [fintype J] [fintype C]
  {k : ℕ} (hk : ∀ j₁ j₂, j₁ ≠ j₂ → (same_rating r j₁ j₂).card ≤ k) :
  (A r).card ≤ k * ((fintype.card J) * (fintype.card J) - (fintype.card J)) :=
begin
  change _ ≤ k * ((finset.card _ ) * (finset.card _ ) - (finset.card _ )),
  rw ← finset.off_diag_card,
  have hh : ∀ (a : C × J × J), a ∈ A r → a.snd ∈ finset.off_diag (@finset.univ J _),
  { simp [A, finset.mem_off_diag], },
  apply finset.card_le_mul_card_image_of_maps_to hh,
  rintros ⟨j₁, j₂⟩ hj,
  have hj' : j₁ ≠ j₂, { simp [finset.mem_off_diag] at hj, exact hj, },
  have hsr : same_rating r j₁ j₂ = ((A r).filter(λ (x : C × J × J), prod.snd x = (j₁, j₂))).image prod.fst,
  { ext, split; intros h,
    { simp, refine ⟨j₁, j₂, _⟩, simp [A, hj'], simp [same_rating] at h, exact h, },
    { simp at h, obtain ⟨j₁', j₂', hj'', hj'''⟩ := h,
      simp [A] at hj'', simp [same_rating],
      cases hj''', subst hj'''_left, subst hj'''_right, exact hj''.1, }, },
  have h' : (same_rating r j₁ j₂).card = ((A r).filter (λ (x : C × J × J), prod.snd x = (j₁, j₂))).card,
  { rw hsr, apply finset.card_image_of_inj_on,
    rintros ⟨c, j₁, j₂⟩ h ⟨c', j₁', j₂'⟩ h' hh, simp [*] at *, },
  rw ← h', apply hk, exact hj',
end

lemma add_sq_add_sq_sub {α : Type*} [comm_ring α] (x y : α) :
  (x + y) * (x + y) + (x - y) * (x - y) = 2*x*x + 2*y*y :=
by ring

lemma norm_bound_of_odd_sum (x y z : ℤ) (h : x + y = 2*z + 1) :
  2*z*z + 2*z + 1 ≤ x*x + y*y :=
begin
  suffices : 4*z*z + 4*z + 1 + 1 ≤ 2*x*x + 2*y*y,
  { rw ← mul_le_mul_left zero_lt_two, convert this; ring, },
  have h' : (x + y) * (x + y) = 4*z*z + 4*z + 1, { rw h, ring, },
  rw [← add_sq_add_sq_sub, h', add_le_add_iff_left],
  suffices : 0 < (x - y) * (x - y), { apply int.add_one_le_of_lt this, },
  apply mul_self_pos,
  intros contra,
  have h' : 2*x = 2*z + 1, { rw two_mul, rw ← h, simp [eq_of_sub_eq_zero contra], },
  have ho : odd (2*x), { rw h', exact ⟨z, rfl⟩, },
  rw int.odd_iff_not_even at ho,
  apply ho,
  exact ⟨x, rfl⟩,
end

lemma agreement_lower_bound [fintype J] (B : ℕ) (hJ : fintype.card J = 2*B + 1) (c : C) :
  2*B*B + 2*B + 1 ≤ (finset.univ.filter (λ (jj : J × J), r c jj.1 = r c jj.2)).card :=
begin
  let x := ((@finset.univ J _).filter (λ j, r c j)).card,
  let y := ((@finset.univ J _).filter (λ j, ¬ r c j)).card,
  have h : (finset.univ.filter (λ (jj : J × J), r c jj.1 = r c jj.2)).card = x*x + y*y,
  { have h' := finset.filter_product_card (@finset.univ J _) (@finset.univ J _) (λ j, r c j) (λ j, r c j),
    simp [-eq_iff_iff] at h', rw h', },
  rw [h, ← @nat.cast_le ℤ],
  simp,
  apply norm_bound_of_odd_sum ↑x ↑y ↑B,
  suffices : x + y = 2*B + 1, { simp [← int.coe_nat_add, this], },
  rw [finset.filter_card_add_filter_neg_card_eq_card, ← hJ], refl,
end

lemma agreement_lower_bound' [fintype J] (B : ℕ) (hJ : fintype.card J = 2*B + 1) (c : C) :
  2*B*B ≤ (finset.univ.filter (λ (jj : J × J), r c jj.1 = r c jj.2 ∧ jj.1 ≠ jj.2)).card :=
begin
  let s := finset.filter (λ (jj : J × J), r c jj.fst = r c jj.snd) finset.univ,
  let t := finset.filter (λ (jj : J × J), jj.fst ≠ jj.snd) finset.univ,
  have hs : 2*B*B + 2*B + 1 ≤ s.card, { apply agreement_lower_bound r B hJ, },
  have hst : (s \ t).card = 2*B + 1,
  { have : ∀ (jj : J × J), ((r c jj.fst ↔ r c jj.snd) ∧ jj.fst = jj.snd) ↔ jj.fst = jj.snd, { finish, },
    simp [s, t, finset.sdiff_eq_filter, finset.filter_filter, this],
    rw ← hJ, exact (@finset.univ J _).diag_card, },
  rw [finset.filter_and, finset.inter_eq_sdiff_sdiff s t, finset.card_sdiff],
  { rw hst, rw add_assoc at hs, apply nat.le_sub_right_of_add_le hs, },
  { apply finset.sdiff_subset_self, },
end

lemma agreement_lower_bound'' [fintype J] [fintype C] (B : ℕ) (hJ : fintype.card J = 2*B + 1) :
  (fintype.card C) * 2*B*B ≤ (A r).card :=
begin
  have h₁ : (fintype.card C) * 2*B*B = 2*B*B * fintype.card C,
  { rw [mul_assoc, mul_assoc, mul_comm, ← mul_assoc], },
  rw h₁,
  have hh : ∀ x, x ∈ (A r) → prod.fst x ∈ @finset.univ C _, { intros x hx, apply finset.mem_univ, },
  apply finset.mul_card_image_le_card_of_maps_to hh,
  intros c hc,
  simp only [finset.filter_congr_decidable],
  suffices : ( (A r).filter (λ (x : C × J × J), x.fst = c)).card =
             (finset.univ.filter (λ (jj : J × J), r c jj.1 = r c jj.2 ∧ jj.1 ≠ jj.2)).card,
  { rw this, apply agreement_lower_bound' r B hJ, },
  have hc' : finset.univ.filter (λ (jj : J × J), r c jj.1 = r c jj.2 ∧ jj.1 ≠ jj.2) =
             ((A r).filter (λ (x : C × J × J), x.fst = c)).image prod.snd,
  { ext ⟨j₁, j₂⟩, simp [A], split,
    { rintros ⟨hj, hj'⟩, refine ⟨c, j₁, j₂, _⟩, simp [hj, hj'], },
    { intros hj, obtain ⟨c', j₁', j₂', ⟨hj', hc'⟩, hj₁, hj₂⟩ := hj,
      rw [hc', hj₁, hj₂] at hj', exact hj', }, },
  rw hc', symmetry,
  apply finset.card_image_of_inj_on,
  rintros ⟨c₁, jj₁⟩ hh₁ ⟨c₂, jj₂⟩ hh₂ hjj,
  simp at hh₁, simp at hh₂, simp at hjj,
  obtain ⟨_, hc₁⟩ := hh₁,
  obtain ⟨_, hc₂⟩ := hh₂,
  rw [hc₁, hc₂, hjj],
end

local notation x `/` y := (x : ℚ) / y

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
  rw [h', ← mul_assoc] at h,
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

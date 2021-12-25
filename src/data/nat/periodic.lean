/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import algebra.periodic
import data.nat.interval
import data.nat.count

/-!
# Periodic Functions on ℕ

This file identifies a few functions on `ℕ` which are periodic, and also proves a lemma about
periodic predicates which helps determine their cardinality when filtering intervals over them.
-/

namespace nat

open nat function

lemma periodic_gcd (a : ℕ) : periodic (gcd a) a :=
by simp only [forall_const, gcd_add_self_right, eq_self_iff_true, periodic]

lemma periodic_coprime (a : ℕ) : periodic (coprime a) a :=
by simp only [coprime_add_self_right, forall_const, iff_self, eq_iff_iff, periodic]

lemma periodic_mod (a : ℕ) : periodic (λ n, n % a) a :=
by simp only [forall_const, eq_self_iff_true, add_mod_right, periodic]

lemma _root_.function.periodic.map_mod_nat {α : Type*} {f : ℕ → α} {a : ℕ} (hf : periodic f a) :
  ∀ n, f (n % a) = f n :=
λ n, by { conv_rhs { rw [← nat.mod_add_div n a, mul_comm, ← nsmul_eq_mul, hf.nsmul] } }

lemma mod_inj_on_Ico (n a : ℕ) : set.inj_on (λ k, k % a) (finset.Ico n (n+a)) :=
begin
  induction n with n ih,
  { simp only [zero_add, nat_zero_eq_zero, Ico_zero_eq_range],
    rintro k hk l hl (hkl : k % a = l % a),
    simp only [finset.mem_range, finset.mem_coe] at hk hl,
    rwa [mod_eq_of_lt hk, mod_eq_of_lt hl] at hkl, },
  rw [Ico_succ_left_eq_erase_Ico, succ_add, Ico_succ_right_eq_insert_Ico le_self_add],
  rintro k hk l hl (hkl : k % a = l % a),
  have ha : 0 < a,
  { by_contra ha, simp only [not_lt, nonpos_iff_eq_zero] at ha, simpa [ha] using hk },
  simp only [finset.mem_coe, finset.mem_insert, finset.mem_erase] at hk hl,
  rcases hk with ⟨hkn, (rfl|hk)⟩; rcases hl with ⟨hln, (rfl|hl)⟩,
  { refl },
  { rw add_mod_right at hkl,
    suffices : l = n, { contradiction },
    refine ih hl _ hkl.symm,
    simp only [lt_add_iff_pos_right, set.left_mem_Ico, finset.coe_Ico, ha], },
  { rw add_mod_right at hkl,
    suffices : k = n, { contradiction },
    refine ih hk _ hkl,
    simp only [lt_add_iff_pos_right, set.left_mem_Ico, finset.coe_Ico, ha], },
  { refine ih _ _ hkl; simp only [finset.mem_coe, hk, hl], },
end

section finset
open finset

-- what is the correct generality? It also works for `ℤ`
lemma finset_Ico_image_mod (n a : ℕ) :
  (Ico n (n+a)).image (λ k, k % a) = range a :=
begin
  obtain (rfl|ha) : a = 0 ∨ a ≠ 0 := eq_or_ne a 0,
  { rw [range_zero, add_zero, Ico_self, image_empty], },
  ext i,
  simp only [mem_image, exists_prop, mem_range, mem_Ico],
  split,
  { rintro ⟨i, h, rfl⟩, exact mod_lt i ha.bot_lt },
  { intro hia,
    have hn := nat.mod_add_div n a,
    by_cases hi : i < n % a,
    { refine ⟨i + a * (n/a + 1), ⟨_, _⟩, _⟩,
      { rw [add_comm (n/a), mul_add, mul_one, ← add_assoc],
        refine hn.symm.le.trans (add_le_add_right _ _),
        simpa only [zero_add] using add_le_add (zero_le i) (nat.mod_lt n ha.bot_lt).le, },
      { refine lt_of_lt_of_le (add_lt_add_right hi (a * (n/a + 1))) _,
        rw [mul_add, mul_one, ← add_assoc, hn], },
      { rw [nat.add_mul_mod_self_left, nat.mod_eq_of_lt hia], } },
    { refine ⟨i + a * (n/a), ⟨_, _⟩, _⟩,
      { push_neg at hi,
        exact hn.symm.le.trans  (add_le_add_right hi _), },
      { rw [add_comm n a],
        refine add_lt_add_of_lt_of_le hia (le_trans _ hn.le),
        simp only [zero_le, le_add_iff_nonneg_left], },
      { rw [nat.add_mul_mod_self_left, nat.mod_eq_of_lt hia], } } }
end

-- move this (and generalize)
@[simp] lemma finset.Ico_val (a b : ℕ) : (Ico a b).val = multiset.Ico a b := rfl

end finset

section multiset
open multiset

lemma multiset_Ico_map_mod (n a : ℕ) :
  (multiset.Ico n (n+a)).map (λ k, k % a) = multiset.range a :=
begin
  rw [← finset.range_coe, ← congr_arg finset.val (finset_Ico_image_mod n a),
    finset.image_val, finset.Ico_val, eq_comm, erase_dup_eq_self, nodup_map_iff_inj_on],
  swap, { exact finset.nodup _ },
  intros k hk l hl hkl,
  exact mod_inj_on_Ico n a hk hl hkl
end

lemma multiset.card_filter_eq_count {α : Type*} (s : multiset α) (p : α → Prop) [decidable_pred p] :
  (s.filter p).card = (s.map p).count true :=
begin
  apply multiset.induction_on s; clear s,
  { simp only [filter_zero, card_zero, multiset.count_zero, multiset.map_zero], },
  intros a s ih,
  simp only [filter_cons, map_cons, multiset.count_cons],
  by_cases hpa : p a,
  { rw [if_pos hpa, card_add, card_singleton, ih, add_comm, if_pos],
    simp only [hpa], },
  { rw [if_neg hpa, zero_add, ih, if_neg, add_zero],
    simp only [hpa, eq_iff_iff, iff_false, not_not], }
end

end multiset

section finset
open finset

/-- An interval of length `a` filtered over a periodic predicate of period `a` has the
same cardinality as `range a` filtered over that predicate. -/
lemma filter_Ico_card_eq_of_periodic' (n a : ℕ) (p : ℕ → Prop) [decidable_pred p]
  (pp : periodic p a) :
  (multiset.filter p (multiset.Ico n (n+a))).card = a.count p :=
begin
  rw [count_eq_card_filter_range, finset.card, finset.filter_val, finset.range_coe,
    ← multiset_Ico_map_mod n, multiset.card_filter_eq_count, multiset.card_filter_eq_count,
    multiset.map_map, function.comp],
  simp only [pp.map_mod_nat],
end

/-- An interval of length `a` filtered over a periodic predicate of period `a` has the
same cardinality as `range a` filtered over that predicate. -/
lemma filter_Ico_card_eq_of_periodic (n a : ℕ) (p : ℕ → Prop) [decidable_pred p]
  (pp : periodic p a) :
  (finset.filter p (finset.Ico n (n+a))).card = a.count p :=
by { rw [← filter_Ico_card_eq_of_periodic' n a p pp], refl, }

end finset

end nat

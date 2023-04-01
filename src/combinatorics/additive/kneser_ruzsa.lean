/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import combinatorics.additive.e_transform
import combinatorics.additive.mul_stab
import tactic.linarith

/-!
# Kneser's addition theorem

This file proves Kneser's theorem. This states that `|s + H| + |t + H| - |H| ≤ |s + t|` where `s`,
`t` are finite nonempty sets in a commutative group and `H` is the stabilizer of `s + t`. Further,
if the inequality is strict, then we in fact have `|s + H| + |t + H| ≤ |s + t|`.

## Main declarations

* `finset.mul_kneser`: Kneser's theorem.
* `finset.mul_strict_kneser`: Strict Kneser theorem.

## References

* [Imre Ruzsa, *Sumsets and structure*][ruzsa2009]
* Matt DeVos, *A short proof of Kneser's addition theorem*
-/

section
variables {α : Type*} [canonically_ordered_comm_semiring α] [pos_mul_strict_mono α]
  [mul_pos_strict_mono α] {a b c d : α}

--TODO: Fix implicitness of `eq_zero_or_pos`
lemma mul_lt_mul_of_lt_of_lt'' (hab : a < b) (hcd : c < d) : a * c < b * d :=
begin
  obtain rfl | hc := @eq_zero_or_pos _ _ c,
  { rw mul_zero,
    exact mul_pos ((zero_le _).trans_lt hab) hcd },
  { exact mul_lt_mul_of_lt_of_lt' hab hcd ((zero_le _).trans_lt hab) hc }
end

end

open function mul_action
open_locale classical pointwise

variables {ι α : Type*} [comm_group α] [decidable_eq α] {s s' t t' C : finset α} {a b : α}

namespace finset

/-! ### Auxiliary results -/

-- Lemma 3.3 in Ruzsa's notes
lemma le_card_union_add_card_mul_stab_union :
  min (s.card + s.mul_stab.card) (t.card + t.mul_stab.card)
    ≤ (s ∪ t).card + (s ∪ t).mul_stab.card :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  obtain hst | hst := (subset_union_left s t).eq_or_ssubset,
  { simp [hst.symm] },
  obtain hts | hts := (subset_union_right s t).eq_or_ssubset,
  { simp [hts.symm] },
  set Hs := s.mul_stab with hHs,
  set Ht := t.mul_stab with hHt,
  set H := Hs * Ht with hH,
  have : Hs ∩ Ht = 1,
  { sorry },
  have : H.card = Hs.card * Ht.card,
  { refine card_mul_iff.2 (λ a ha b hb hab, _),
    sorry },
  set k : α → ℕ := sorry,
  set l : α → ℕ := sorry,
  have hk : ∀ a, (s \ t ∩ a • H).card = k a * (Hs.card - l a),
  { sorry },
  have hl : ∀ a, (t \ s ∩ a • H).card = l a * (Ht.card - k a),
  { sorry },
  suffices : Hs.card - H.card \le (s \ t ∩ a • H).card ≤  ∨ (t \ s ∩ a • H).card ≤ Ht.card - H.card,
  { sorry },
  by_cases hkl : ∃ a, k a ≠ 0 ∧ k a < Ht.card ∧ l a ≠ 0 ∧ l a < Hs.card,
  { obtain ⟨a, hka, hka', hla, hla'⟩ := hkl,
    have hHst :
      (Hs.card - 1) * (Ht.card - 1) ≤ (s \ t ∩ a • H).card * (t \ s ∩ a • H).card,
    { rw [hk, hl, mul_comm (k a), mul_mul_mul_comm, mul_comm (k a)],
      refine le_trans _ (mul_le_mul' (nat.add_sub_one_le_mul (tsub_pos_of_lt hla').ne' hla) $
        nat.add_sub_one_le_mul (tsub_pos_of_lt hka').ne' hka),
      rw [tsub_add_cancel_of_le hka'.le, tsub_add_cancel_of_le hla'.le] },
    obtain h | h : Hs.card - 1 ≤ (s \ t ∩ a • H).card ∨ Ht.card - 1 ≤ (t \ s ∩ a • H).card,
    { by_contra',
      exact hHst.not_lt (mul_lt_mul_of_lt_of_lt'' this.1 this.2) },
    obtain h | h := le_or_le_of_mul_le_mul this,
    },
  by_cases hk : ∃ a, k a = 0,
  sorry
end

-- Lemma 3.4 in Ruzsa's notes
lemma le_card_sup_add_card_mul_stab_sup {s : finset ι} {f : ι → finset α} (hs : s.nonempty) :
  s.inf' hs (λ i, (f i).card + (f i).mul_stab.card) ≤ (s.sup f).card + (s.sup f).mul_stab.card :=
begin
  induction s using finset.cons_induction with i s hi ih,
  { cases not_nonempty_empty hs },
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  simp only [hs, inf'_cons, sup_cons, sup_eq_union],
  exact (inf_le_inf_left _ $ ih hs).trans le_card_union_add_card_mul_stab_union,
end

/-! ### Kneser's theorem -/

lemma le_card_mul_add_card_mul_stab_mul (hs : s.nonempty) (ht : t.nonempty) :
  s.card + t.card ≤ (s * t).card + (s * t).mul_stab.card :=
begin
  -- For every `b ∈ t`, consider sets `s_b, t_b` such that
  -- * `b ∈ s_b`
  -- * `s ⊆ s_b`
  -- * `s_b * t_b ⊆ s * t`
  -- * `|s_b| + |t_b| = |s| + |t|`
  -- Such sets exist because we can take `s_b = s, t_b = t`. So pick `s_b, t_b` such that `|t_b|` is
  -- minimal among such sets.
  have : ∀ b : t, ∃ n s' t', ↑b ∈ t' ∧ s ⊆ s' ∧
    s' * t' ⊆ s * t ∧ s'.card + t'.card = s.card + t.card ∧ n = t'.card,
  { exact λ b, ⟨_, s, t, b.2, subset.rfl, subset.rfl, rfl, rfl⟩ },
  choose s' t' hbt' hs' hst' hstcard ht' using λ b, nat.find_spec (this b),
  -- We have  `⋃ b ∈ t, s_b * t_b = s * t` because `s_b * t_b ⊆ s * t` and
  -- `∀ b ∈ t, s • b ⊆ s * t_b ⊆ s_b * t_b`.
  have : s * t = univ.sup (λ b, s' b * t' b),
  { refine le_antisymm _ (finset.sup_le_iff.2 $ λ _ _, hst' _),
    exact mul_subset_iff_right.2 (λ b hb, (smul_finset_subset_smul_finset $ hs' ⟨b, hb⟩).trans $
      (op_smul_finset_subset_mul $ hbt' ⟨b, hb⟩).trans $
        @le_sup _ _ _ _ _ (λ b, s' b * t' b) _ $ mem_univ _) },
  rw this,
  refine (le_inf' ht.attach _ $ λ b _, _).trans (le_card_sup_add_card_mul_stab_sup _),
  rw ←hstcard b,
  refine add_le_add (card_le_card_mul_right _ ⟨_, hbt' _⟩)
    ((card_le_of_subset $ subset_mul_stab_mul_left ⟨_, hbt' _⟩).trans' _),
  rw ←card_smul_finset (b : α)⁻¹ (t' _),
  refine card_le_of_subset ((mul_subset_left_iff $ hs.mono $ hs' _).1 _),
  refine mul_subset_iff_left.2 (λ c hc, _),
  rw ←mul_smul,
  refine smul_finset_subset_iff.2 ((inter_eq_left_iff_subset _ _).1 $
    eq_of_subset_of_card_le (inter_subset_left _ _) _),
  rw ←ht',
  refine nat.find_min' _ ⟨_, _, mem_inter.2 ⟨hbt' _, _⟩, (hs' _).trans $ subset_union_left _ _,
    (mul_dyson_e_transform.subset _ (s' b, t' b)).trans $ hst' _,
    (mul_dyson_e_transform.card _ _).trans $ hstcard _, rfl⟩,
  rwa [mem_inv_smul_finset_iff, smul_eq_mul, inv_mul_cancel_right],
end

/-- **Kneser's multiplication theorem**: A lower bound on the size of `s * t` in terms of its
stabilizer. -/
-- @[to_additive "**Kneser's addition theorem**: A lower bound on the size of `s + t` in terms of its
-- stabilizer."]
lemma mul_kneser (s t : finset α) :
  (s * (s * t).mul_stab).card + (t * (s * t).mul_stab).card ≤
    (s * t).card + (s * t).mul_stab.card :=
begin
  -- The cases `s = ∅` and `t = ∅` are easily taken care of.
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  refine (le_card_mul_add_card_mul_stab_mul (hs.mul (hs.mul ht).mul_stab) $
    ht.mul (hs.mul ht).mul_stab).trans_eq _,
  rw mul_mul_stab_mul_mul_mul_mul_stab_mul,
end

/-- The strict version of **Kneser's multiplication theorem**. If the LHS of `finset.mul_kneser`
does not equal the RHS, then it is in fact much smaller. -/
-- @[to_additive "The strict version of **Kneser's addition theorem**. If the LHS of
-- `finset.add_kneser` does not equal the RHS, then it is in fact much smaller."]
lemma mul_strict_kneser (h : (s * (s * t).mul_stab).card + (t * (s * t).mul_stab).card <
    (s * t).card + (s * t).mul_stab.card) :
  (s * (s * t).mul_stab).card + (t * (s * t).mul_stab).card ≤ (s * t).card :=
nat.le_of_lt_add_of_dvd h ((card_mul_stab_dvd_card_mul_mul_stab _ _).add $
  card_mul_stab_dvd_card_mul_mul_stab _ _) $ card_mul_stab_dvd_card _

end finset

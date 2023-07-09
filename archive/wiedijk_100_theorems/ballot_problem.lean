/-
Copyright (c) 2022 Bhavik Mehta, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kexing Ying
-/
import probability.cond_count

/-!
# Ballot problem

This file proves Theorem 30 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

The ballot problem asks, if in an election, candidate A receives `p` votes whereas candidate B
receives `q` votes where `p > q`, what is the probability that candidate A is strictly ahead
throughout the count. The probability of this is `(p - q) / (p + q)`.

## Main definitions

* `counted_sequence`: given natural numbers `p` and `q`, `counted_sequence p q` is the set of
  all lists containing `p` of `1`s and `q` of `-1`s representing the votes of candidate A and B
  respectively.
* `stays_positive`: is the set of lists of integers which suffix has positive sum. In particular,
  the intersection of this set with `counted_sequence` is the set of lists where candidate A is
  strictly ahead.

## Main result

* `ballot`: the ballot problem.

-/

open set probability_theory measure_theory

namespace ballot

/-- The set of nonempty lists of integers which suffix has positive sum. -/
def stays_positive : set (list ℤ) := {l | ∀ l₂, l₂ ≠ [] → l₂ <:+ l → 0 < l₂.sum}

@[simp] lemma stays_positive_nil : [] ∈ stays_positive :=
λ l hl hl₁, (hl (list.eq_nil_of_suffix_nil hl₁)).elim

lemma stays_positive_cons_pos (x : ℤ) (hx : 0 < x) (l : list ℤ) :
  (x :: l) ∈ stays_positive ↔ l ∈ stays_positive :=
begin
  split,
  { intros hl l₁ hl₁ hl₂,
    apply hl l₁ hl₁ (hl₂.trans (list.suffix_cons _ _)) },
  { intros hl l₁ hl₁ hl₂,
    rw list.suffix_cons_iff at hl₂,
    rcases hl₂ with (rfl | hl₂),
    { rw list.sum_cons,
      apply add_pos_of_pos_of_nonneg hx,
      cases l with hd tl,
      { simp },
      { apply le_of_lt (hl (hd :: tl) (list.cons_ne_nil hd tl) (hd :: tl).suffix_refl) } },
    { apply hl _ hl₁ hl₂ } }
end

/--
`counted_sequence p q` is the set of lists of integers for which every element is `+1` or `-1`,
there are `p` lots of `+1` and `q` lots of `-1`.

This represents vote sequences where candidate `+1` receives `p` votes and candidate `-1` receives
`q` votes.
-/
def counted_sequence (p q : ℕ) : set (list ℤ) :=
{l | l.count 1 = p ∧ l.count (-1) = q ∧ ∀ x ∈ l, x = (1 : ℤ) ∨ x = -1}

/-- An alternative definition of `counted_sequence` that uses `list.perm`. -/
lemma mem_counted_sequence_iff_perm {p q l} :
  l ∈ counted_sequence p q ↔ l ~ list.replicate p (1 : ℤ) ++ list.replicate q (-1) :=
begin
  rw [list.perm_replicate_append_replicate],
  { simp only [counted_sequence, list.subset_def, mem_set_of_eq, list.mem_cons_iff,
      list.mem_singleton] },
  { norm_num1 }
end

@[simp] lemma counted_right_zero (p : ℕ) : counted_sequence p 0 = {list.replicate p 1} :=
by { ext l, simp [mem_counted_sequence_iff_perm] }

@[simp] lemma counted_left_zero (q : ℕ) : counted_sequence 0 q = {list.replicate q (-1)} :=
by { ext l, simp [mem_counted_sequence_iff_perm] }

lemma mem_of_mem_counted_sequence {p q} {l} (hl : l ∈ counted_sequence p q) {x : ℤ} (hx : x ∈ l) :
  x = 1 ∨ x = -1 :=
hl.2.2 x hx

lemma length_of_mem_counted_sequence {p q} {l : list ℤ} (hl : l ∈ counted_sequence p q) :
  l.length = p + q :=
by simp [(mem_counted_sequence_iff_perm.1 hl).length_eq]

lemma counted_eq_nil_iff {p q : ℕ} {l : list ℤ} (hl : l ∈ counted_sequence p q) :
  l = [] ↔ p = 0 ∧ q = 0 :=
list.length_eq_zero.symm.trans $ by simp [length_of_mem_counted_sequence hl]

lemma counted_ne_nil_left {p q : ℕ} (hp : p ≠ 0) {l : list ℤ} (hl : l ∈ counted_sequence p q) :
  l ≠ [] :=
by simp [counted_eq_nil_iff hl, hp]

lemma counted_ne_nil_right {p q : ℕ} (hq : q ≠ 0) {l : list ℤ} (hl : l ∈ counted_sequence p q) :
  l ≠ [] :=
by simp [counted_eq_nil_iff hl, hq]

lemma counted_succ_succ (p q : ℕ) : counted_sequence (p + 1) (q + 1) =
  list.cons 1 '' counted_sequence p (q + 1) ∪ list.cons (-1) '' counted_sequence (p + 1) q  :=
begin
  ext l,
  rw [counted_sequence, counted_sequence, counted_sequence],
  split,
  { intro hl,
    have hlnil := counted_ne_nil_left (nat.succ_ne_zero p) hl,
    obtain ⟨hl₀, hl₁, hl₂⟩ := hl,
    obtain hlast | hlast := hl₂ l.head (list.head_mem_self hlnil),
    { refine or.inl ⟨l.tail, ⟨_, _, _⟩, _⟩,
      { rw [list.count_tail l 1 (list.length_pos_of_ne_nil hlnil), hl₀, if_pos,
          nat.add_succ_sub_one, add_zero],
        rw [list.nth_le_zero, hlast] },
      { rw [list.count_tail l (-1) (list.length_pos_of_ne_nil hlnil), hl₁, if_neg, nat.sub_zero],
        rw [list.nth_le_zero, hlast],
        norm_num },
      { exact λ x hx, hl₂ x (list.mem_of_mem_tail hx) },
      { rw [← hlast, list.cons_head_tail hlnil] } },
    { refine or.inr ⟨l.tail, ⟨_, _, _⟩, _⟩,
      { rw [list.count_tail l 1 (list.length_pos_of_ne_nil hlnil), hl₀, if_neg, nat.sub_zero],
        rw [list.nth_le_zero, hlast],
        norm_num },
      { rw [list.count_tail l (-1) (list.length_pos_of_ne_nil hlnil), hl₁, if_pos,
          nat.add_succ_sub_one, add_zero],
        rw [list.nth_le_zero, hlast] },
      { exact λ x hx, hl₂ x (list.mem_of_mem_tail hx) },
      { rw [← hlast, list.cons_head_tail hlnil] } } },
  { rintro (⟨t, ⟨ht₀, ht₁, ht₂⟩, rfl⟩ | ⟨t, ⟨ht₀, ht₁, ht₂⟩, rfl⟩),
    { refine ⟨_, _, _⟩,
      { rw [list.count_cons, if_pos rfl, ht₀] },
      { rw [list.count_cons, if_neg, ht₁],
        norm_num },
      { rintro x (hx | hx),
        exacts [or.inl hx, ht₂ x hx] } },
    { refine ⟨_, _, _⟩,
      { rw [list.count_cons, if_neg, ht₀],
        norm_num },
      { rw [list.count_cons, if_pos rfl, ht₁] },
      { rintro x (hx | hx),
        exacts [or.inr hx, ht₂ x hx] } } }
end

lemma counted_sequence_finite : ∀ (p q : ℕ), (counted_sequence p q).finite
| 0 q := by simp
| (p + 1) 0 := by simp
| (p + 1) (q + 1) :=
  begin
    rw [counted_succ_succ, set.finite_union, set.finite_image_iff (list.cons_injective.inj_on _),
      set.finite_image_iff (list.cons_injective.inj_on _)],
    exact ⟨counted_sequence_finite _ _, counted_sequence_finite _ _⟩
  end

lemma counted_sequence_nonempty : ∀ (p q : ℕ), (counted_sequence p q).nonempty
| 0 q := by simp
| (p + 1) 0 := by simp
| (p + 1) (q + 1) :=
  begin
    rw [counted_succ_succ, union_nonempty, nonempty_image_iff],
    exact or.inl (counted_sequence_nonempty _ _),
  end

lemma sum_of_mem_counted_sequence {p q} {l : list ℤ} (hl : l ∈ counted_sequence p q) :
  l.sum = p - q :=
by simp [(mem_counted_sequence_iff_perm.1 hl).sum_eq, sub_eq_add_neg]

lemma disjoint_bits (p q : ℕ) :
  disjoint (list.cons 1 '' counted_sequence p (q + 1))
    (list.cons (-1) '' counted_sequence (p + 1) q) :=
begin
  simp_rw [disjoint_left, mem_image, not_exists, exists_imp_distrib],
  rintros _ _ ⟨_, rfl⟩ _ ⟨_, _, _⟩,
end

open measure_theory.measure

private def measureable_space_list_int : measurable_space (list ℤ) := ⊤

local attribute [instance] measureable_space_list_int

private lemma measurable_singleton_class_list_int : measurable_singleton_class (list ℤ) :=
{ measurable_set_singleton := λ s, trivial }

local attribute [instance] measurable_singleton_class_list_int

private lemma list_int_measurable_set {s : set (list ℤ)} : measurable_set s :=
trivial

lemma count_counted_sequence : ∀ p q : ℕ, count (counted_sequence p q) = (p + q).choose p
| p 0 := by simp [counted_right_zero, count_singleton]
| 0 q := by simp [counted_left_zero, count_singleton]
| (p + 1) (q + 1) :=
  begin
    rw [counted_succ_succ, measure_union (disjoint_bits _ _) list_int_measurable_set,
      count_injective_image list.cons_injective, count_counted_sequence,
      count_injective_image list.cons_injective, count_counted_sequence],
    { norm_cast,
      rw [add_assoc, add_comm 1 q, ← nat.choose_succ_succ, nat.succ_eq_add_one, add_right_comm] },
    all_goals { try { apply_instance } },
  end

lemma first_vote_pos :
  ∀ p q, 0 < p + q →
    cond_count (counted_sequence p q : set (list ℤ)) {l | l.head = 1} = p / (p + q)
| (p + 1) 0 h :=
  begin
    rw [counted_right_zero, cond_count_singleton],
    simp [ennreal.div_self _ _],
  end
| 0 (q + 1) _ :=
  begin
    rw [counted_left_zero, cond_count_singleton],
    simpa,
  end
| (p + 1) (q + 1) h :=
  begin
    simp_rw [counted_succ_succ],
    rw [← cond_count_disjoint_union ((counted_sequence_finite _ _).image _)
        ((counted_sequence_finite _ _).image _) (disjoint_bits _ _), ← counted_succ_succ,
      cond_count_eq_one_of ((counted_sequence_finite p (q + 1)).image _)
        (nonempty_image_iff.2 (counted_sequence_nonempty _ _))],
    { have : list.cons (-1) '' counted_sequence (p + 1) q ∩ {l : list ℤ | l.head = 1} = ∅,
      { ext,
        simp only [mem_inter_iff, mem_image, mem_set_of_eq, mem_empty_iff_false, iff_false, not_and,
          forall_exists_index, and_imp],
        rintro l _ rfl,
        norm_num },
      have hint : counted_sequence (p + 1) (q + 1) ∩ list.cons 1 '' counted_sequence p (q + 1) =
        list.cons 1 '' counted_sequence p (q + 1),
      { rw [inter_eq_right_iff_subset, counted_succ_succ],
        exact subset_union_left _ _ },
      rw [(cond_count_eq_zero_iff $ (counted_sequence_finite _ _).image _).2 this,
        cond_count, cond_apply _ list_int_measurable_set, hint,
        count_injective_image list.cons_injective, count_counted_sequence, count_counted_sequence,
        one_mul, zero_mul, add_zero, nat.cast_add, nat.cast_one],
      { rw [mul_comm, ← div_eq_mul_inv, ennreal.div_eq_div_iff],
        { norm_cast,
          rw [mul_comm _ (p + 1), ← nat.succ_eq_add_one p, nat.succ_add,
            nat.succ_mul_choose_eq, mul_comm] },
          all_goals { simp [(nat.choose_pos $ (le_add_iff_nonneg_right _).2 zero_le').ne.symm] } },
      all_goals { apply_instance } },
    { simp },
    { apply_instance }
  end

lemma head_mem_of_nonempty {α : Type*} [inhabited α] :
  ∀ {l : list α} (hl : l ≠ []), l.head ∈ l
| [] h := h rfl
| (x :: l) _ := or.inl rfl

lemma first_vote_neg (p q : ℕ) (h : 0 < p + q) :
  cond_count (counted_sequence p q) {l | l.head = 1}ᶜ = q / (p + q) :=
begin
  have := cond_count_compl {l : list ℤ | l.head = 1}ᶜ
    (counted_sequence_finite p q) (counted_sequence_nonempty p q),
  rw [compl_compl, first_vote_pos _ _ h] at this,
  rw [(_ : (q / (p + q) : ennreal) = 1 - p / (p + q)), ← this, ennreal.add_sub_cancel_right],
  { simp only [ne.def, ennreal.div_eq_top, nat.cast_eq_zero, add_eq_zero_iff,
      ennreal.nat_ne_top, false_and, or_false, not_and],
    intros,
    contradiction },
  rw [eq_comm, ennreal.eq_div_iff, ennreal.mul_sub, ennreal.mul_div_cancel'],
  all_goals { simp, try { rintro rfl, rw zero_add at h, exact h.ne.symm } },
end

lemma ballot_same (p : ℕ) : cond_count (counted_sequence (p + 1) (p + 1)) stays_positive = 0 :=
begin
  rw [cond_count_eq_zero_iff (counted_sequence_finite _ _), eq_empty_iff_forall_not_mem],
  rintro x ⟨hx, t⟩,
  apply ne_of_gt (t x _ x.suffix_refl),
  { simpa using sum_of_mem_counted_sequence hx },
  { refine list.ne_nil_of_length_pos _,
    rw length_of_mem_counted_sequence hx,
    exact nat.add_pos_left (nat.succ_pos _) _ },
end

lemma ballot_edge (p : ℕ) : cond_count (counted_sequence (p + 1) 0) stays_positive = 1 :=
begin
  rw counted_right_zero,
  refine cond_count_eq_one_of (finite_singleton _) (singleton_nonempty _) _,
  { intros l hl,
    rw mem_singleton_iff at hl,
    subst hl,
    refine λ l hl₁ hl₂, list.sum_pos _ (λ x hx, _) hl₁,
    rw list.eq_of_mem_replicate (list.mem_of_mem_suffix hx hl₂),
    norm_num },
end

lemma counted_sequence_int_pos_counted_succ_succ (p q : ℕ) :
  (counted_sequence (p + 1) (q + 1)) ∩ {l | l.head = 1} =
  (counted_sequence p (q + 1)).image (list.cons 1) :=
begin
  rw [counted_succ_succ, union_inter_distrib_right,
    (_ : list.cons (-1) '' counted_sequence (p + 1) q ∩ {l | l.head = 1} = ∅), union_empty];
  { ext,
    simp only [mem_inter_iff, mem_image, mem_set_of_eq, and_iff_left_iff_imp, mem_empty_iff_false,
      iff_false, not_and, forall_exists_index, and_imp],
    rintro y hy rfl,
    norm_num }
end

lemma ballot_pos (p q : ℕ) :
  cond_count ((counted_sequence (p + 1) (q + 1)) ∩ {l | l.head = 1}) stays_positive =
  cond_count (counted_sequence p (q + 1)) stays_positive :=
begin
  rw [counted_sequence_int_pos_counted_succ_succ, cond_count, cond_count,
    cond_apply _ list_int_measurable_set, cond_apply _ list_int_measurable_set,
    count_injective_image list.cons_injective],
  all_goals { try { apply_instance } },
  congr' 1,
  have : (counted_sequence p (q + 1)).image (list.cons 1) ∩ stays_positive =
         (counted_sequence p (q + 1) ∩ stays_positive).image (list.cons 1),
  { ext t,
    simp only [mem_inter_iff, mem_image],
    split,
    { simp only [and_imp, exists_imp_distrib],
      rintro l hl rfl t,
      refine ⟨l, ⟨hl, _⟩, rfl⟩,
      rwa stays_positive_cons_pos at t,
      norm_num },
    { simp only [and_imp, exists_imp_distrib],
      rintro l hl₁ hl₂ rfl,
      refine ⟨⟨_, hl₁, rfl⟩, _⟩,
      rwa stays_positive_cons_pos,
      norm_num } },
  rw [this, count_injective_image],
  exact list.cons_injective,
end

lemma counted_sequence_int_neg_counted_succ_succ (p q : ℕ) :
  (counted_sequence (p + 1) (q + 1)) ∩ {l | l.head = 1}ᶜ =
  (counted_sequence (p + 1) q).image (list.cons (-1)) :=
begin
  rw [counted_succ_succ, union_inter_distrib_right,
    (_ : list.cons 1 '' counted_sequence p (q + 1) ∩ {l : list ℤ | l.head = 1}ᶜ = ∅), empty_union];
  { ext,
    simp only [mem_inter_iff, mem_image, mem_set_of_eq, and_iff_left_iff_imp, mem_empty_iff_false,
      iff_false, not_and, forall_exists_index, and_imp],
    rintro y hy rfl,
    norm_num }
end

lemma ballot_neg (p q : ℕ) (qp : q < p) :
  cond_count ((counted_sequence (p + 1) (q + 1)) ∩ {l | l.head = 1}ᶜ) stays_positive =
  cond_count (counted_sequence (p + 1) q) stays_positive :=
begin
  rw [counted_sequence_int_neg_counted_succ_succ, cond_count, cond_count,
    cond_apply _ list_int_measurable_set, cond_apply _ list_int_measurable_set,
    count_injective_image list.cons_injective],
  all_goals { try { apply_instance } },
  congr' 1,
  have : (counted_sequence (p + 1) q).image (list.cons (-1)) ∩ stays_positive =
         ((counted_sequence (p + 1) q) ∩ stays_positive).image (list.cons (-1)),
  { ext t,
    simp only [mem_inter_iff, mem_image],
    split,
    { simp only [and_imp, exists_imp_distrib],
      rintro l hl rfl t,
      exact ⟨_, ⟨hl, λ l₁ hl₁ hl₂, t l₁ hl₁ (hl₂.trans (list.suffix_cons _ _))⟩, rfl⟩ },
    { simp only [and_imp, exists_imp_distrib],
      rintro l hl₁ hl₂ rfl,
      refine ⟨⟨l, hl₁, rfl⟩, λ l₁ hl₃ hl₄, _⟩,
      rw list.suffix_cons_iff at hl₄,
      rcases hl₄ with (rfl | hl₄),
      { simp [list.sum_cons, sum_of_mem_counted_sequence hl₁, sub_eq_add_neg, ← add_assoc, qp] },
      exact hl₂ _ hl₃ hl₄ } },
  rw [this, count_injective_image],
  exact list.cons_injective
end

theorem ballot_problem' :
  ∀ q p, q < p → (cond_count (counted_sequence p q) stays_positive).to_real = (p - q) / (p + q) :=
begin
  classical,
  apply nat.diag_induction,
  { intro p,
    rw ballot_same,
    simp },
  { intro p,
    rw ballot_edge,
    simp only [ennreal.one_to_real, nat.cast_add, nat.cast_one, nat.cast_zero, sub_zero, add_zero],
    rw div_self ,
    exact nat.cast_add_one_ne_zero p },
  { intros q p qp h₁ h₂,
    haveI := cond_count_is_probability_measure
      (counted_sequence_finite p (q + 1)) (counted_sequence_nonempty _ _),
    haveI := cond_count_is_probability_measure
      (counted_sequence_finite (p + 1) q) (counted_sequence_nonempty _ _),
    have h₃ : p + 1 + (q + 1) > 0 := nat.add_pos_left (nat.succ_pos _) _,
    rw [← cond_count_add_compl_eq {l : list ℤ | l.head = 1} _ (counted_sequence_finite _ _),
      first_vote_pos _ _ h₃, first_vote_neg _ _ h₃, ballot_pos, ballot_neg _ _ qp],
    rw [ennreal.to_real_add, ennreal.to_real_mul, ennreal.to_real_mul, ← nat.cast_add,
      ennreal.to_real_div, ennreal.to_real_div, ennreal.to_real_nat, ennreal.to_real_nat,
      ennreal.to_real_nat, h₁, h₂],
    { have h₄ : (↑(p + 1) + ↑(q + 1)) ≠ (0 : ℝ),
      { apply ne_of_gt,
        assumption_mod_cast },
      have h₅ : (↑(p + 1) + ↑q) ≠ (0 : ℝ),
      { apply ne_of_gt,
        norm_cast,
        linarith },
      have h₆ : (↑p + ↑(q + 1)) ≠ (0 : ℝ),
      { apply ne_of_gt,
        norm_cast,
        linarith },
      field_simp [h₄, h₅, h₆] at *,
      ring },
    all_goals { refine (ennreal.mul_lt_top (measure_lt_top _ _).ne _).ne,
      simp [ne.def, ennreal.div_eq_top] } }
end

/-- The ballot problem. -/
theorem ballot_problem :
  ∀ q p, q < p → cond_count (counted_sequence p q) stays_positive = (p - q) / (p + q) :=
begin
  intros q p qp,
  haveI := cond_count_is_probability_measure
    (counted_sequence_finite p q) (counted_sequence_nonempty _ _),
  have : (cond_count (counted_sequence p q) stays_positive).to_real =
    ((p - q) / (p + q) : ennreal).to_real,
  { rw ballot_problem' q p qp,
    rw [ennreal.to_real_div, ← nat.cast_add, ← nat.cast_add, ennreal.to_real_nat,
      ennreal.to_real_sub_of_le, ennreal.to_real_nat, ennreal.to_real_nat],
    exacts [nat.cast_le.2 qp.le, ennreal.nat_ne_top _] },
  rwa ennreal.to_real_eq_to_real (measure_lt_top _ _).ne at this,
  { simp only [ne.def, ennreal.div_eq_top, tsub_eq_zero_iff_le, nat.cast_le,
      not_le, add_eq_zero_iff, nat.cast_eq_zero, ennreal.add_eq_top, ennreal.nat_ne_top,
      or_self, not_false_iff, and_true],
    push_neg,
    exact ⟨λ _ _, by linarith, (lt_of_le_of_lt tsub_le_self (ennreal.nat_ne_top p).lt_top).ne⟩ },
  apply_instance,
end

end ballot

/-
A collection of useful lemmas that might be useful in mathlib, approximately sorted by where they belong
-/

import data.finset
import algebra.big_operators
import tactic

open finset

section finset
  variables {α : Type*} [decidable_eq α]
  lemma sdiff_union_inter (A B : finset α) : (A \ B) ∪ (A ∩ B) = A :=
  by simp only [ext, mem_union, mem_sdiff, mem_inter]; tauto

  lemma sdiff_inter_inter (A B : finset α) : disjoint (A \ B) (A ∩ B) :=
  disjoint_of_subset_right (inter_subset_right _ _) sdiff_disjoint

  @[simp] lemma sdiff_idem (s t : finset α) : s \ t \ t = s \ t :=
  by simp only [ext, mem_sdiff]; tauto
  @[simp] lemma sdiff_self (s : finset α) : s \ s = ∅ :=
  by simp only [ext, not_mem_empty, iff_self, mem_sdiff, and_not_self, forall_true_iff]
  lemma inter_union_self (s t : finset α) : s ∩ (t ∪ s) = s :=
  by simp only [ext, mem_inter, mem_union]; tauto
  lemma union_sdiff_self (s t : finset α) : (s ∪ t) \ t = s \ t :=
  by simp only [ext, mem_union, mem_sdiff]; tauto
  lemma singleton_union_eq_insert (a : α) (s : finset α) : finset.singleton a ∪ s = insert a s :=
  rfl
  lemma sdiff_singleton_eq_erase (a : α) (s : finset α) : s \ finset.singleton a = erase s a :=
  begin ext, rw [mem_erase, mem_sdiff, mem_singleton], tauto end
  lemma union_sdiff_distrib_right (s₁ s₂ t : finset α) : (s₁ ∪ s₂) \ t = s₁ \ t ∪ s₂ \ t :=
  by simp only [ext, mem_sdiff, mem_union]; tauto
  lemma sdiff_union_distrib_left (s t₁ t₂ : finset α) : s \ (t₁ ∪ t₂) = (s \ t₁) ∩ (s \ t₂) :=
  by simp only [ext, mem_union, mem_sdiff, mem_inter]; tauto
  lemma union_eq_left_of_subset {s t : finset α} (h : t ⊆ s) : s ∪ t = s := lattice.sup_of_le_left h
  lemma not_mem_sdiff_of_mem_right {a : α} {s t : finset α} (h : a ∈ t) : a ∉ s \ t :=
  begin simp only [mem_sdiff, h, not_true, not_false_iff, and_false] end
  lemma sdiff_sdiff_self_left (s t : finset α) : s \ (s \ t) = s ∩ t :=
  by simp only [ext, mem_sdiff, mem_inter]; tauto
  lemma union_empty_iff (A B : finset α) : A ∪ B = ∅ ↔ A = ∅ ∧ B = ∅ := lattice.sup_eq_bot_iff

  lemma sdiff_eq_self_of_disjoint {s t : finset α} : disjoint s t → s \ t = s :=
  by simp [ext, disjoint_left]; tauto

  lemma sdiff_eq_self_iff_disjoint {s t : finset α} : s \ t = s ↔ disjoint s t :=
  ⟨λ p, p ▸ sdiff_disjoint, sdiff_eq_self_of_disjoint⟩

  lemma disjoint_self_iff_empty (s : finset α) : disjoint s s ↔ s = ∅ :=
  disjoint_self

  lemma sdiff_subset_left (s t : finset α) : s \ t ⊆ s :=
  by simp [subset_iff]; tauto

  -- TODO: This could be an iff
  lemma sdiff_partially_injective {s t₁ t₂ : finset α} : s \ t₁ = s \ t₂ → s ∩ t₁ = s ∩ t₂ :=
  by simp [ext]; intros b c; replace b := b c; split; tauto

  instance decidable_disjoint (U V : finset α) : decidable (disjoint U V) :=
  decidable_of_decidable_of_iff (by apply_instance) disjoint_iff_inter_eq_empty.symm

  -- There's a similar thing in data.finset already, but this one is sometimes more practical
  lemma min_ne_max_of_card {α : Type*} [decidable_linear_order α] {U : finset α} {h₁ : finset.nonempty U}
    (h₂ : 1 < card U) : min' U h₁ ≠ max' U h₁ :=
  begin
    intro, apply not_le_of_lt h₂ (le_of_eq _), rw card_eq_one,
    use max' U h₁, rw eq_singleton_iff_unique_mem,
    exact ⟨max'_mem _ _, λ t Ht, le_antisymm (le_max' U h₁ t Ht) (a ▸ min'_le U h₁ t Ht)⟩
  end

  /--
  Given a set A and a set B inside it, we can shrink A to any appropriate size, and keep B
  inside it.
  -/
  lemma exists_intermediate_set {A B : finset α} (i : ℕ)
    (h₁ : card A ≥ i + card B) (h₂ : B ⊆ A) :
    ∃ (C : finset α), B ⊆ C ∧ C ⊆ A ∧ card C = i + card B :=
  begin
    rcases nat.le.dest h₁ with ⟨k, _⟩, clear h₁, revert A,
    induction k with k ih,
      intros A BsubA cards, exact ⟨A, BsubA, subset.refl _, cards.symm⟩,
    intros A BsubA cards,
    have: ∃ i, i ∈ A \ B,
      rw [exists_mem_iff_ne_empty, ← ne, ← card_pos, card_sdiff BsubA,
          ← cards, nat.add_right_comm, nat.add_sub_cancel, nat.add_succ],
      apply nat.succ_pos,
    rcases this with ⟨a, ha⟩,
    set A' := erase A a,
    have z: i + card B + k = card A',
      rw [card_erase_of_mem, ← cards, nat.add_succ, nat.pred_succ],
      rw mem_sdiff at ha, exact ha.1,
    rcases ih _ z with ⟨B', hB', B'subA', cards⟩,
    refine ⟨B', hB', trans B'subA' (erase_subset _ _), cards⟩,
    rintros t th, apply mem_erase_of_ne_of_mem _ (BsubA th), rintro rfl,
    rw mem_sdiff at ha, tauto
  end

  /-- We can shrink A to any smaller size. -/
  lemma exists_smaller_set (A : finset α) (i : ℕ) (h₁ : card A ≥ i) :
    ∃ (B : finset α), B ⊆ A ∧ card B = i :=
  begin
    rcases exists_intermediate_set i _ (empty_subset A) with ⟨B, _, x₁, x₂⟩,
    simp at x₂, exact ⟨B, x₁, x₂⟩, simpa,
  end

  /-- A flipped version of exists_min from data.finset. -/
  lemma exists_max {α β : Type*} [decidable_linear_order α] (s : finset β) (f : β → α)
    (h : s ≠ ∅) : ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x :=
  begin
    have : s.image f ≠ ∅,
      rwa [ne, image_eq_empty, ← ne.def],
    cases max_of_ne_empty this with y hy,
    rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩,
    exact ⟨x, hx, λ x' hx', le_max_of_mem (mem_image_of_mem f hx') hy⟩,
  end

  /-- An alternate version of the above with different typeclass requirements. -/
  lemma exists_max' {α β : Type*} [linear_order α] [decidable_eq β] (s : finset β) (f : β → α) :
    s ≠ ∅ → ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  begin
    apply finset.induction_on s,
    intro a, exfalso, apply a, refl,
    intros i B hi ih _, by_cases (B = ∅), rw h, refine ⟨i, mem_insert_self _ _, λ t th, _⟩,
    rw [mem_insert] at th, rw or.resolve_right th (not_mem_empty t),
    specialize ih h, rcases ih with ⟨k, kB, q⟩,
    apply or.elim (le_total (f i) (f k)),
    intro ik, refine ⟨k, mem_insert_of_mem kB, λ t th, _⟩,
    rw mem_insert at th, cases th, rwa th, apply q _ th,
    intro ki, refine ⟨i, mem_insert_self _ _,  λ t th, _⟩,
    rw mem_insert at th, cases th, rwa th, apply trans (q _ th) ki,
  end
end finset

lemma bind_sub_bind_of_sub_left {α β : Type*} [decidable_eq α] {s₁ s₂ : finset β}
  (t : β → finset α) (h : s₁ ⊆ s₂) : s₁.bind t ⊆ s₂.bind t :=
by intro x; simp; intros y hy hty; refine ⟨y, h hy, hty⟩

section big_operators
  lemma sum_div {α β : Type*} [division_ring β] {s : finset α} {f : α → β} {b : β} :
    s.sum f / b = s.sum (λx, f x / b) :=
  calc s.sum f / b = s.sum (λ x, f x * (1 / b)) : by rw [div_eq_mul_one_div, sum_mul]
       ...         = s.sum (λ x, f x / b) : by congr; ext; rw ← div_eq_mul_one_div (f x) b

  lemma sum_const_nat {α : Type*} {m : ℕ} {f : α → ℕ} {s : finset α} (h₁ : ∀x ∈ s, f x = m) :
    s.sum f = card s * m :=
  begin
    rw [← nat.smul_eq_mul, ← sum_const],
    apply sum_congr rfl h₁
  end

  lemma sum_lt_sum {α β : Type*} {s : finset α} {f g : α → β} [decidable_eq α] [ordered_cancel_comm_monoid β] :
    s ≠ ∅ → (∀ x ∈ s, f x < g x) → s.sum f < s.sum g :=
  begin
    apply finset.induction_on s, intro, exfalso, apply a, refl,
    intros x s not_mem ih _ assump, simp only [sum_insert not_mem],
    apply lt_of_lt_of_le,
      rw add_lt_add_iff_right (s.sum f),
      exact assump x (mem_insert_self _ _),
    rw add_le_add_iff_left,
    by_cases (s = ∅), simp only [h, sum_empty],
    exact (le_of_lt $ ih h $ λ t, assump t ∘ mem_insert_of_mem),
  end

  lemma sum_flip {α : Type*} [add_comm_monoid α] {n : ℕ} (f : ℕ → α) : sum (range (n+1)) (λ r, f (n - r)) = sum (range (n+1)) (λ r, f r) :=
  begin
    induction n with n ih,
      rw [sum_range_one, sum_range_one],
    rw sum_range_succ',
    rw sum_range_succ _ (nat.succ n),
    simp [ih],
  end
end big_operators

section nat
  lemma choose_symm' {n a b : ℕ} (h : n = a + b) : nat.choose n a = nat.choose n b :=
  begin
    have: a = n - b, rw h, rw nat.add_sub_cancel,
    rw [this, nat.choose_symm], apply nat.le.intro, symmetry, rwa add_comm
  end
end nat

section natchoose
  lemma dominate_choose_lt {r n : ℕ} (h : r < n/2) :
    nat.choose n r ≤ nat.choose n (r+1) :=
  begin
    refine le_of_mul_le_mul_right _ (nat.lt_sub_left_of_add_lt (lt_of_lt_of_le h (nat.div_le_self n 2))),
    rw ← nat.choose_succ_right_eq,
    apply nat.mul_le_mul_left,
    rw [← nat.lt_iff_add_one_le, nat.lt_sub_left_iff_add_lt, ← mul_two],
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_right h zero_lt_two) (nat.div_mul_le_self n 2),
  end

  lemma dominate_choose_lt' {n r : ℕ} (hr : r ≤ n/2) : nat.choose n r ≤ nat.choose n (n/2) :=
  begin
    refine @nat.decreasing_induction (λ k, k ≤ n/2 → nat.choose n k ≤ nat.choose n (n/2)) (λ m k a, _) r (n/2) hr (λ _, by refl) hr,
    rcases eq_or_lt_of_le a with rfl | h, refl,
    exact trans (dominate_choose_lt h) (k h)
  end

  lemma dominate_choose {r n : ℕ} : nat.choose n r ≤ nat.choose n (n/2) :=
  begin
    cases le_or_gt r n with b b,
      cases le_or_lt r (n/2) with a h,
        apply dominate_choose_lt' a,
      rw ← nat.choose_symm b,
      apply dominate_choose_lt',
      rw [nat.div_lt_iff_lt_mul' zero_lt_two] at h,
      rw [nat.le_div_iff_mul_le' zero_lt_two, nat.mul_sub_right_distrib, nat.sub_le_iff, mul_two, nat.add_sub_cancel],
      exact le_of_lt h,
    rw nat.choose_eq_zero_of_lt b,
    apply zero_le
  end
end natchoose

lemma div_nonneg_of_nonneg_of_nonneg {α : Type*} [discrete_linear_ordered_field α] {a b : α} : 0 ≤ a → 0 ≤ b → 0 ≤ a / b :=
begin
  intros ah bh,
  cases eq_or_lt_of_le bh,
    rw [← h, div_zero],
  apply div_nonneg_of_nonneg_of_pos ah h
end

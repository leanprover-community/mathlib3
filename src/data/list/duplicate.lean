/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Chris Hughes
-/
import data.list.basic
import data.fin

/-!
# List duplicates

## Main definitions

* `list.duplicate x l : Prop` is an inductive property that holds when `x` is a duplicate in `l`

-/

variable {α : Type*}

namespace list

/-- Property that an element `x : α` of `l : list α` can be found in the list more than once. -/
inductive duplicate (x : α) : list α → Prop
| cons_mem {l : list α} : x ∈ l → duplicate (x :: l)
| cons_duplicate {y : α} {l : list α} : duplicate l → duplicate (y :: l)

local infix ` ∈+ `:50 := list.duplicate

variables {l : list α} {x : α}

lemma mem.duplicate_cons_self (h : x ∈ l) : x ∈+ x :: l := duplicate.cons_mem h

lemma duplicate.duplicate_cons (h : x ∈+ l) (y : α) : x ∈+ y :: l := duplicate.cons_duplicate h

lemma duplicate.mem (h : x ∈+ l) : x ∈ l :=
begin
  induction h with l' h y l' h hm,
  { exact mem_cons_self _ _ },
  { exact mem_cons_of_mem _ hm }
end

lemma duplicate.mem_cons_self (h : x ∈+ x :: l) : x ∈ l :=
begin
  cases h with _ h _ _ h,
  { exact h },
  { exact h.mem }
end

@[simp] lemma duplicate_cons_self_iff : x ∈+ x :: l ↔ x ∈ l :=
⟨duplicate.mem_cons_self, mem.duplicate_cons_self⟩

lemma duplicate.ne_nil (h : x ∈+ l) : l ≠ [] :=
λ H, (mem_nil_iff x).mp (H ▸ h.mem)

@[simp] lemma not_duplicate_nil (x : α) : ¬ x ∈+ [] :=
λ H, by simpa using H.ne_nil

lemma duplicate.ne_singleton (h : x ∈+ l) (y : α) : l ≠ [y] :=
begin
  induction h with l' h z l' h hm,
  { simp [ne_nil_of_mem h] },
  { simp [ne_nil_of_mem h.mem] }
end

@[simp] lemma not_duplicate_singleton (x y : α) : ¬ x ∈+ [y] :=
λ H, by simpa using H.ne_singleton _

lemma duplicate_cons_iff {y : α} : x ∈+ y :: l ↔ (y = x ∧ x ∈ l) ∨ x ∈+ l :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { cases h with _ hm _ _ hm,
    { exact or.inl ⟨rfl, hm⟩ },
    { exact or.inr hm } },
  { rcases h with ⟨rfl|h⟩|h,
    { simpa },
    { exact h.duplicate_cons _ } }
end

lemma duplicate.of_duplicate_cons {y : α} (h : x ∈+ y :: l) (hx : x ≠ y) : x ∈+ l :=
by simpa [duplicate_cons_iff, hx.symm] using h

lemma duplicate_cons_iff_of_ne {y : α} (hne : x ≠ y) : x ∈+ y :: l ↔ x ∈+ l :=
by simp [duplicate_cons_iff, hne.symm]

lemma duplicate.mono_sublist {l' : list α} (hx : x ∈+ l) (h : l <+ l') : x ∈+ l' :=
begin
  induction h with l₁ l₂ y h IH l₁ l₂ y h IH,
  { simpa using hx.ne_nil },
  { exact (IH hx).duplicate_cons _ },
  { rw duplicate_cons_iff at hx ⊢,
    rcases hx with ⟨rfl, hx⟩|hx,
    { simp [h.subset hx] },
    { simp [IH hx] } }
end

/-- The contrapositive of `list.nodup_iff_sublist`. -/
lemma duplicate_iff_sublist : x ∈+ l ↔ [x, x] <+ l :=
begin
  induction l with y l IH,
  { simp },
  { by_cases hx : x = y,
    { simp [hx, cons_sublist_cons_iff, singleton_sublist] },
    { rw [duplicate_cons_iff_of_ne hx, IH],
      refine ⟨sublist_cons_of_sublist y, λ h, _⟩,
      cases h,
      { assumption },
      { contradiction } } }
end

lemma duplicate_iff_count_le_two [decidable_eq α] : (x ∈+ l) ↔ 2 ≤ count x l :=
by simp [duplicate_iff_sublist, le_count_iff_repeat_sublist]
lemma sublist_of_order_embedding {l l' : list α} (f : ℕ ↪o ℕ)
  (hf : ∀ (ix : ℕ), l.nth ix = l'.nth (f ix)) :
  l <+ l' :=
begin
  induction l with hd tl IH generalizing l' f,
  { simp },
  have : some hd = _ := hf 0,
  rw [eq_comm, list.nth_eq_some] at this,
  obtain ⟨w, h⟩ := this,
  let f' : ℕ ↪o ℕ := order_embedding.of_map_rel_iff (λ i, f (i + 1) - (f 0 + 1))
    (λ a b, by simp [nat.sub_le_sub_right_iff, nat.succ_le_iff, nat.lt_succ_iff]),
  have : ∀ ix, tl.nth ix = (l'.drop (f 0 + 1)).nth (f' ix),
  { intro ix,
    simp [list.nth_drop, nat.add_sub_of_le, nat.succ_le_iff, ←hf] },
  rw [←list.take_append_drop (f 0 + 1) l', ←list.singleton_append],
  apply list.sublist.append _ (IH _ this),
  rw [list.singleton_sublist, ←h, l'.nth_le_take _ (nat.lt_succ_self _)],
  apply list.nth_le_mem
end

lemma sublist_iff_nth_eq {l l' : list α} :
  l <+ l' ↔ ∃ (f : ℕ ↪o ℕ), ∀ (ix : ℕ), l.nth ix = l'.nth (f ix) :=
begin
  split,
  { intro H,
    induction H with xs ys y H IH xs ys x H IH,
    { simp },
    { obtain ⟨f, hf⟩ := IH,
      refine ⟨f.trans (order_embedding.of_strict_mono (+ 1) (λ _, by simp)), _⟩,
      simpa using hf },
    { obtain ⟨f, hf⟩ := IH,
      refine ⟨order_embedding.of_map_rel_iff
        (λ (ix : ℕ), if ix = 0 then 0 else (f ix.pred).succ) _, _⟩,
      { rintro ⟨_|a⟩ ⟨_|b⟩;
        simp [nat.succ_le_succ_iff] },
      { rintro ⟨_|i⟩,
        { simp },
        { simpa using hf _ } } } },
  { rintro ⟨f, hf⟩,
    exact sublist_of_order_embedding f hf }
end

lemma sublist_iff_nth_le_eq {l l' : list α} :
  l <+ l' ↔ ∃ (f : fin l.length ↪o fin l'.length),
    ∀ (ix : fin l.length), l.nth_le ix ix.is_lt = l'.nth_le (f ix) (f ix).is_lt :=
begin
  rw sublist_iff_nth_eq,
  split,
  { rintro ⟨f, hf⟩,
    have h : ∀ {i : ℕ} (h : i < l.length), f i < l'.length,
    { intros i hi,
      specialize hf i,
      rw [nth_le_nth hi, eq_comm, nth_eq_some] at hf,
      obtain ⟨h, -⟩ := hf,
      exact h },
    refine ⟨order_embedding.of_map_rel_iff (λ ix, ⟨f ix, h ix.is_lt⟩) _, _⟩,
    { simp },
    { intro i,
      apply option.some_injective,
      simpa [←nth_le_nth] using hf _ } },
  { rintro ⟨f, hf⟩,
    refine ⟨order_embedding.of_strict_mono
      (λ i, if hi : i < l.length then f ⟨i, hi⟩ else i + l'.length) _, _⟩,
    { intros i j h,
      dsimp only,
      split_ifs with hi hj hj hi,
      { simpa using h },
      { rw add_comm,
        exact lt_add_of_lt_of_pos (fin.is_lt _) (i.zero_le.trans_lt h) },
      { exact absurd (h.trans hj) hi },
      { simpa using h } },
    { intro i,
      simp only [order_embedding.coe_of_strict_mono],
      split_ifs with hi,
      { rw [nth_le_nth hi, nth_le_nth, ←hf],
        simp },
      { rw [nth_len_le, nth_len_le],
        { simp },
        { simpa using hi } } } }
end

lemma duplicate_iff_exists_distinct :
  x ∈+ l ↔ ∃ (n : ℕ) (hn : n < l.length) (m : ℕ) (hm : m < l.length) (h : n < m),
    x = l.nth_le n hn ∧ x = l.nth_le m hm :=
begin
  classical,
  rw [duplicate_iff_count_le_two, le_count_iff_repeat_sublist, sublist_iff_nth_le_eq],
  split,
  { rintro ⟨f, hf⟩,
    refine ⟨f ⟨0, by simp⟩, fin.is_lt _, f ⟨1, by simp⟩, fin.is_lt _, by simp, _, _⟩,
    { simpa using hf ⟨0, by simp⟩ },
    { simpa using hf ⟨1, by simp⟩ } },
  { rintro ⟨n, hn, m, hm, hnm, h, h'⟩,
    refine ⟨order_embedding.of_strict_mono (λ i, if (i : ℕ) = 0 then ⟨n, hn⟩ else ⟨m, hm⟩) _, _⟩,
    { rintros ⟨⟨_|i⟩, hi⟩ ⟨⟨_|j⟩, hj⟩,
      { simp  },
      { simp [hnm] },
      { simp },
      { simp only [nat.lt_succ_iff, nat.succ_le_succ_iff, repeat, length, nonpos_iff_eq_zero]
          at hi hj,
        simp [hi, hj] } },
    { rintros ⟨⟨_|i⟩, hi⟩,
      { simpa using h },
      { simpa using h' } } },
end

instance decidable_duplicate [decidable_eq α] (x : α) : ∀ (l : list α), decidable (x ∈+ l)
| []       := is_false (not_duplicate_nil x)
| (y :: l) := match decidable_duplicate l with
  | is_true  h := is_true (h.duplicate_cons y)
  | is_false h := if hx : y = x ∧ x ∈ l
      then is_true (hx.left.symm ▸ hx.right.duplicate_cons_self)
      else is_false (by simpa [duplicate_cons_iff, h] using hx)
  end

end list

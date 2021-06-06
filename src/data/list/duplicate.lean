/-
Copyright (c) 2018 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Chris Hughes
-/
import data.list.basic

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

local infix ` ∈+ `:1 := list.duplicate

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

@[simp] lemma duplicate_cons_self_iff : (x ∈+ x :: l) ↔ x ∈ l :=
⟨duplicate.mem_cons_self, mem.duplicate_cons_self⟩

lemma duplicate.ne_nil (h : x ∈+ l) : l ≠ [] :=
λ H, (mem_nil_iff x).mp (H ▸ h.mem)

@[simp] lemma not_duplicate_nil (x : α) : ¬ (x ∈+ []) :=
λ H, by simpa using H.ne_nil

lemma duplicate.ne_singleton (h : x ∈+ l) (y : α) : l ≠ [y] :=
begin
  induction h with l' h z l' h hm,
  { simp [ne_nil_of_mem h] },
  { simp [ne_nil_of_mem h.mem] }
end

@[simp] lemma not_duplicate_singleton (x y : α) : ¬ (x ∈+ [y]) :=
λ H, by simpa using H.ne_singleton _

lemma duplicate.eq_and_mem_or_duplicate {y : α} (h : x ∈+ y :: l) : (y = x ∧ x ∈ l) ∨ (x ∈+ l) :=
begin
  cases h with _ hm _ _ hm,
  { exact or.inl ⟨rfl, hm⟩ },
  { exact or.inr hm }
end

lemma duplicate.cons_imp_of_ne {y : α} (h : x ∈+ y :: l) (hx : x ≠ y) : x ∈+ l :=
begin
  refine h.eq_and_mem_or_duplicate.resolve_left _,
  simp [and.comm, hx.symm]
end

lemma duplicate_cons_iff_of_ne {y : α} (hne : x ≠ y) : (x ∈+ y :: l) ↔ (x ∈+ l) :=
⟨λ h, h.cons_imp_of_ne hne, λ h, h.duplicate_cons _⟩

lemma duplicate.mono_sublist {l' : list α} (hx : x ∈+ l) (h : l <+ l') : x ∈+ l' :=
begin
  induction h with l₁ l₂ y h IH l₁ l₂ y h IH,
  { simpa using hx.ne_nil },
  { exact (IH hx).duplicate_cons _ },
  { rcases hx.eq_and_mem_or_duplicate with ⟨rfl, hm⟩|hm,
    { exact (h.subset hx.mem_cons_self).duplicate_cons_self },
    { exact (IH hm).duplicate_cons _ } }
end

/-- The contrapositive of `list.nodup_iff_sublist`. -/
lemma duplicate_iff_sublist : (x ∈+ l) ↔ [x, x] <+ l :=
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

lemma duplicate_nth_le_iff_exists_distinct {n : ℕ} {hn : n < l.length} :
  (l.nth_le n hn ∈+ l) ↔ ∃ (m : ℕ) (hm : m < l.length) (h : n ≠ m), l.nth_le n hn = l.nth_le m hm :=
begin
  induction l with y l IH generalizing n,
  { simp },
  { cases n,
    { simp only [mem_iff_nth_le, exists_prop, duplicate_cons_self_iff, nat.nat_zero_eq_zero, length,
                 exists_and_distrib_left, ne.def, nth_le],
      split,
      { rintro ⟨m, hm, rfl⟩,
        use m + 1,
        simpa [hm, m.zero_lt_succ.ne] },
      { rintro ⟨_ | m, h, hm, hy⟩,
        { contradiction },
        { use m,
          simp only [length, nat.succ_lt_succ_iff] at hm,
          rw hy,
          simpa [hm] } } },
    { by_cases hy : (y :: l).nth_le n.succ hn = y,
      { rw hy,
        simp only [mem_iff_nth_le, exists_prop, duplicate_cons_self_iff, length,
                   exists_and_distrib_left, ne.def, nth_le],
        split,
        { intro,
          use 0,
          simp },
        { intro,
          simp only [nat.succ_lt_succ_iff, length] at hn,
          use [n, hn],
          simpa using hy } },
      { rw duplicate_cons_iff_of_ne hy,
        simp only [IH, exists_prop, length, exists_and_distrib_left, ne.def, nth_le],
        split,
        { rintro ⟨m, h, hm, hy⟩,
          use m + 1,
          simpa [nat.succ_inj', hm, h] using hy },
        { rintro ⟨_ | m, h, hm, hy⟩,
          { contradiction },
          { use m,
            rw [nat.succ_inj'] at h,
            simp only [length, nat.succ_lt_succ_iff] at hm,
            rw hy,
            simpa [h, hm] } } } } }
end

instance decidable_duplicate [decidable_eq α] (x : α) : ∀ (l : list α), decidable (x ∈+ l)
| []       := is_false (not_duplicate_nil x)
| (y :: l) := match decidable_duplicate l with
  | is_true  h := is_true (h.duplicate_cons y)
  | is_false h :=
    if hx : x ∈ l
      then if hy : x = y
        then is_true (hy ▸ hx.duplicate_cons_self)
        else is_false (λ H, h (H.cons_imp_of_ne hy))
      else is_false (λ H, hx (or.cases_on H.eq_and_mem_or_duplicate and.elim_right duplicate.mem))
  end

end list

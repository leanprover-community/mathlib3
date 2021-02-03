import data.list.sort

universe u

open list

variables {α : Type u} {r : α → α → Prop}

lemma nth_le_of_sorted_of_lt {l : list α}
  (h : l.sorted r) {a b : ℕ} {ha : a < l.length} {hb : b < l.length} (hab : a < b) :
  r (l.nth_le a ha) (l.nth_le b hb) :=
list.pairwise_iff_nth_le.1 h a b hb hab

-- @[simp] theorem index_of_nth_le [decidable_eq α] {a : α} :
--   ∀ {l : list α} h, nth_le l (index_of a l) h = a
-- | (b::l) h := by by_cases h' : a = b;
--   simp only [h', if_pos, if_false, index_of_cons, nth_le, @index_of_nth_le l]

-- @[simp] theorem index_of_nth [decidable_eq α] {a : α} {l : list α} (h : a ∈ l) :
--   nth l (index_of a l) = some a :=
-- by rw [nth_le_nth, index_of_nth_le (index_of_lt_length.2 h)]

lemma mem_take_iff (x : α) (k : ℕ) (l : list α) [decidable_eq α] (hx : x ∈ list.take k l) :
  list.index_of x l ≤ k :=
begin
  induction l generalizing k,
  { simp only [not_mem_nil, take_nil] at hx,
    cases hx },
  { rw index_of_cons,
    split_ifs,
    { apply nat.zero_le },
    { cases k,
      { simp only [not_mem_nil, take] at hx,
        cases hx },
      { rw take_cons at hx,
        have := l_ih _ (hx.resolve_left h),
        exact nat.succ_le_succ (l_ih _ (hx.resolve_left h)) } } }
end

example {α : Type u} (k : ℕ)
  (r : α → α → Prop)
  [decidable_rel r]
  [is_trans α r]
  (l : list α)
  (ls : list.sorted r l) : ∀ (x ∈ list.take k l) (y ∈ list.drop k l), r x y :=
begin
  intros x hx y hy,
  have := nth_le_of_mem,
  -- have := nth_le_of_sorted_of_lt ls _ _,
end

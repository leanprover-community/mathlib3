import tactic.basic

import data.multiset.basic

lemma list.sum_le_sup_mul_length {s : list ℕ} (a : ℕ) (h : ∀ (n : ℕ), n ∈ s → n ≤ a) :
  s.sum ≤ a * s.length :=
begin
  induction s with hd tl ih,
  { simp , },
  rw [list.sum_cons, add_comm],
  rw [list.length_cons, mul_add, mul_one],
  refine nat.add_le_add (ih _) (h _ _),
  { intros n hn, refine h n _,  --
    apply list.mem_cons_of_mem, exact hn, } ,
  { apply list.mem_cons_self, }
end

lemma list.inf_mul_length_le_sum {s : list ℕ} (a : ℕ) (h : ∀ (n : ℕ), n ∈ s → a ≤ n) :
  a * s.length ≤ s.sum :=
begin
  induction s with hd tl ih,
  { simp , },
  rw [list.sum_cons, add_comm],
  rw [list.length_cons, mul_add, mul_one],
  refine nat.add_le_add (ih _) (h _ _),
  { intros n hn, refine h n _,  --
    apply list.mem_cons_of_mem, exact hn, } ,
  { apply list.mem_cons_self, }
end

lemma list.sum_eq_const_mul_length {s : list ℕ} (a : ℕ) (h : ∀ (n : ℕ), n ∈ s → n = a) :
  s.sum = a * s.length :=
begin
  apply le_antisymm,
  have h' : ∀ (n : ℕ), n ∈ s → n ≤ a, { intros n hn, rw h n hn, },
  exact list.sum_le_sup_mul_length a h',
  have h'' : ∀ (n : ℕ), n ∈ s → a ≤ n, { intros n hn, rw h n hn, },
  exact list.inf_mul_length_le_sum a h'',
end


lemma multiset.sum_le_sup_mul_card {m : multiset ℕ} : ∀ (a : ℕ) (h : ∀ (n : ℕ), n ∈ m → n ≤ a),
  m.sum ≤ a * m.card :=
quotient.induction_on m (λ l a h, by simpa using list.sum_le_sup_mul_length a h)

lemma multiset.inf_mul_length_le_card {m : multiset ℕ} : ∀ (a : ℕ) (h : ∀ (n : ℕ), n ∈ m → a ≤ n),
  a * m.card ≤ m.sum :=
quotient.induction_on m (λ l a h, by simpa using list.inf_mul_length_le_sum a h)

lemma multiset.sum_eq_const_mul_card {m : multiset ℕ} : ∀ (a : ℕ) (h : ∀ (n : ℕ), n ∈ m → n = a),
  m.sum = a * m.card :=
quotient.induction_on m (λ l a h, by simpa using list.sum_eq_const_mul_length a h)

example (l : list ℕ): l.sum = (l : multiset ℕ).sizeof :=
begin
  refl,
  sorry
end

lemma multiset.sum_le_sup_mul_card {m : multiset ℕ} (a : ℕ) (h : ∀ (n : ℕ), n ∈ m → n ≤ a) :
  m.sum ≤ a * m.card :=
-- quotient.induction_on m $ λ l a hl, by simpa using list.sum_le_sup_mul_length a hl
begin
  revert a,
  apply quotient.induction_on m,
  intros l a h,
  simpa using list.sum_le_sup_mul_length a h,
end

import data.multiset.dedup

lemma list.length_dedup_le {α : Type*} [decidable_eq α] (l : list α) :
  l.dedup.length ≤ l.length :=
begin
  induction l with hd tl IH,
  { simp },
  { by_cases h : hd ∈ tl,
    { simpa [h] using IH.trans (nat.le_succ _) },
    { simp [h, IH] } }
end

lemma multiset.card_dedup_le {α : Type*} [decidable_eq α] (s : multiset α) :
  s.dedup.card ≤ s.card :=
begin
  induction s using quotient.induction_on,
  simpa using list.length_dedup_le _
end

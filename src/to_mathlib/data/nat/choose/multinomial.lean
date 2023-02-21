import data.nat.choose.multinomial

variables {α : Type*}

lemma finsupp.multinomial_pos (s : α →₀ ℕ) : 0 < s.multinomial :=
nat.multinomial_pos _ _

lemma multiset.multinomial_pos (s : multiset α) : 0 < s.multinomial :=
finsupp.multinomial_pos _

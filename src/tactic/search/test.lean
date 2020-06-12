-- import data.finset
import tactic.search.foo

example {α : Type} (s t : set α) (a : α) (m : a ∈ s) (h : s ⊆ t) : a ∈ t :=
by show_term { ariadne }

-- TODO better filtering of crap lemmas
-- TODO look at the metavariables in goals: go for ones without

example {a b c d : ℕ} (h₁ : a < c) (h₂ : b < d) : max (c + d) (a + b) = (c + d) :=
-- by exact max_eq_left_of_lt (add_lt_add h₁ h₂)
-- by suggest
by show_term { ariadne }

#print plift.up.inj
#print let_eq
#print int.of_nat.inj
#print int.of_nat_inj

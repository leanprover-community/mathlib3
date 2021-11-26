import logic.nontrivial
import algebra.order.ring
import data.nat.basic

/-! ### Test `nontriviality` with inequality hypotheses -/

example {R : Type} [ordered_ring R] {a : R} (h : 0 < a) : 0 < a :=
begin
  nontriviality,
  guard_hyp _inst : nontrivial R,
  assumption,
end

/-! ### Test `nontriviality` with equality or non-strict inequality goals -/

example {R : Type} [comm_ring R] {r s : R} : r * s = s * r :=
begin
  nontriviality,
  guard_hyp _inst : nontrivial R,
  apply mul_comm,
end

/-! ### Test deducing `nontriviality` by instance search -/

example {R : Type} [ordered_ring R] : 0 ≤ (1 : R) :=
begin
  nontriviality R,
  guard_hyp _inst : nontrivial R,
  exact zero_le_one,
end

example {R : Type} [ordered_ring R] : 0 ≤ (1 : R) :=
begin
  nontriviality ℕ,
  guard_hyp _inst : nontrivial ℕ,
  exact zero_le_one,
end

example {R : Type} [ordered_ring R] : 0 ≤ (2 : R) :=
begin
  success_if_fail { nontriviality punit },
  exact zero_le_two,
end

example {R : Type} [ordered_ring R] {a : R} (h : 0 < a) : 2 ∣ 4 :=
begin
  nontriviality R,
  guard_hyp _inst : nontrivial R,
  dec_trivial
end

/-! Test using `@[nontriviality]` lemmas in `nontriviality and custom `simp` lemmas -/

def empty_or_univ {α : Type*} (s : set α) : Prop := s = ∅ ∨ s = set.univ

lemma subsingleton.set_empty_or_univ {α} [subsingleton α] (s : set α) :
  s = ∅ ∨ s = set.univ :=
subsingleton.set_cases (or.inl rfl) (or.inr rfl) s

lemma subsingleton.set_empty_or_univ' {α} [subsingleton α] (s : set α) :
  empty_or_univ s :=
subsingleton.set_empty_or_univ s

example {α : Type*} (s : set α) (hs : s = ∅ ∪ set.univ) : empty_or_univ s :=
begin
  success_if_fail { nontriviality α },
  rw [set.empty_union] at hs,
  exact or.inr hs
end

section

local attribute [nontriviality] subsingleton.set_empty_or_univ

example {α : Type*} (s : set α) (hs : s = ∅ ∪ set.univ) : empty_or_univ s :=
begin
  success_if_fail { nontriviality α },
  nontriviality α using [subsingleton.set_empty_or_univ'],
  rw [set.empty_union] at hs,
  exact or.inr hs
end

end

local attribute [nontriviality] subsingleton.set_empty_or_univ'

example {α : Type*} (s : set α) (hs : s = ∅ ∪ set.univ) : empty_or_univ s :=
begin
  nontriviality α,
  rw [set.empty_union] at hs,
  exact or.inr hs
end

/-! Test with nonatomic type argument -/

example (α : ℕ → Type) (a b : α 0) (h : a = b) : a = b :=
begin
  nontriviality α 0 using [nat.zero_lt_one],
  guard_hyp _inst : nontrivial (α 0),
  exact h
end

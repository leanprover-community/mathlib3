import data.nat.factorial
import data.equiv.basic
import data.finsupp.basic
import data.fintype.card

open finset finsupp
open_locale big_operators

def finset.bInter {α β : Type*} [decidable_eq β] (s : finset α) (t : α → finset β) : finset β :=
(s.bUnion t).filter (λ b, ∀ a ∈ s, b ∈ t a)

@[simp] lemma finset.bInter_empty {α β : Type*} [decidable_eq β] {t : α → finset β} :
  finset.bInter ∅ t = ∅ :=
begin
  sorry
end


def finset.indicator {α : Type*} [decidable_eq α] (s : finset α) : α →₀ ℕ :=
{ support := s,
  to_fun := λ a, if a ∈ s then 1 else 0,
  mem_support_to_fun := λ a, by simp }


lemma PIE {α ι : Type*} [decidable_eq ι] [decidable_eq α] {f : ι → finset α} {s : finset ι} :
  (s.bUnion f).card = ∑ i in range (s.card + 1), ∑ t in powerset_len i s, (t.bInter f).card :=
begin
  revert f,
  apply s.induction_on,
  { sorry },
  clear s,
  intros i s hi ih f,
  simp,
  sorry
end

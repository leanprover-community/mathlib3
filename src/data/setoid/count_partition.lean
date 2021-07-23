import data.setoid.partition
import data.fintype.basic
import algebra.big_operators

open_locale classical big_operators

lemma card_set_is_sum_card_classes
  {α : Type*} [fintype α] (S : setoid α) :
  fintype.card α = ∑ s in S.classes.to_finset, (s : set α).to_finset.card :=
begin
  sorry,
end

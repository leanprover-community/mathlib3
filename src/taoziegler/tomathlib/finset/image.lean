import data.finset.image
import algebra.big_operators

namespace finset

open_locale big_operators

variables {α β : Type*} [comm_monoid β] (p : α → Prop) [decidable_pred p] (s : finset α) (f : α → β)

@[simp] lemma map_subtype {s : finset (subtype p)} :
  finset.subtype p (map (function.embedding.subtype p) s) = s :=
begin
  rw [←(map_injective (function.embedding.subtype p)).eq_iff, subtype_map_of_mem],
  simp { contextual := tt }
end

@[to_additive]
lemma prod_subtype' :
  ∏ i in (s.subtype p), f i = ∏ i in s.filter p, f i :=
begin
  refine prod_bij' (λ a _, a) (λ a ha, mem_filter.mpr ⟨mem_subtype.mp ha, a.prop⟩) (λ _ _, rfl)
    (λ a ha, ⟨a, (mem_filter.mp ha).right⟩) _ _ _;
  simp { contextual := tt }
end

@[to_additive]
lemma prod_subtype_mem (p : set α) [decidable_pred (∈ p)] (s : finset α) (f : α → β) :
  ∏ (i : p) in (s.subtype (∈ p)), f i = ∏ i in s.filter p, f i :=
prod_subtype' _ _ _

end finset

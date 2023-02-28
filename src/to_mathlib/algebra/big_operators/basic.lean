import algebra.big_operators.basic

universes u v w
variables {ι : Type*} {β : Type u} {α : Type v} {γ : Type w}

open_locale big_operators

open fin function

namespace finset

@[to_additive]
def prod_induction' [comm_monoid γ] {C : γ → Prop} (s : finset β) (f : β → γ) (h1 : C 1)
  (hmul : ∀ (a ∈ s) b, C b → C (f a * b)) : C (s.prod f) :=
begin
  induction s using finset.cons_induction_on with a s ha IH,
  { exact h1 },
  { rw prod_cons ha,
    refine hmul _ (mem_cons_self _ _) _ (IH _),
    intros a ha,
    exact hmul _ (mem_cons.mpr (or.inr ha)) }
end

@[to_additive]
lemma is_unit_prod [comm_monoid γ] (s : finset β) (f : β → γ) (hs : ∀ b ∈ s, is_unit (f b)) :
  is_unit (s.prod f) :=
prod_induction' _ _ is_unit_one (λ a ha b hb, (hs _ ha).mul hb)

attribute [to_additive] is_unit.decidable

@[to_additive]
lemma is_unit_prod_filter [comm_monoid γ] (s : finset β) (f : β → γ)
  [decidable_pred (λ b, is_unit (f b))] :
  is_unit ((s.filter (λ b, is_unit (f b))).prod f) :=
is_unit_prod _ _ (by simp)

@[to_additive]
lemma prod_coe_sort_set [comm_monoid γ] (s : set β) [decidable_pred (∈ s)] (t : finset s)
  (f : β → γ) :
  ∏ (i : s) in t, f i = ∏ (i : β) in (t.map (embedding.subtype _)).filter (∈ s), f i :=
begin
  refine prod_bij (λ x _, x) _ (λ _ _, rfl) (λ _ _ _ _, subtype.ext) _,
  { rintro ⟨b, hb⟩,
    simp only [hb, subtype.coe_mk, mem_filter, finset.mem_map, embedding.coe_subtype, exists_prop,
               subtype.exists, exists_and_distrib_right, exists_eq_right, exists_true_left,
              and_true, imp_self] },
  { simp only [filter_true_of_mem, finset.mem_map, embedding.coe_subtype, exists_prop,
               subtype.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right,
               forall_exists_index, implies_true_iff, set_coe.exists, exists_eq_right']
               {contextual := tt} }
end

end finset

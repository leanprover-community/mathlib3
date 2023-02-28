import topology.algebra.infinite_sum.basic

noncomputable theory
open finset filter function classical
open_locale topology classical big_operators

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

variables [add_comm_monoid α] [topological_space α]

lemma summable_fintype [fintype β] (f : β → α) : summable f :=
begin
  refine ⟨univ.sum f, _⟩,
  simp [has_sum, order_top.at_top_eq, tendsto_pure_left, mem_of_mem_nhds] { contextual := tt }
end

@[simp] lemma summable_subsingleton [subsingleton β] (f : β → α) : summable f :=
begin
  casesI is_empty_or_nonempty β,
  { haveI : fintype β := fintype.of_is_empty,
    exact summable_fintype _ },
  { inhabit β,
    haveI : fintype β := fintype.of_subsingleton default,
    exact summable_fintype _ }
end

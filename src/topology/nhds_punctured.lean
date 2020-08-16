import topology.continuous_on

open set filter
open_locale topological_space filter

variables {α : Type*} {β : Type*}
variables [topological_space α]

localized "notation `𝓝*` x : 100 := nhds_within x ({x}ᶜ)" in topological_space

lemma nhds_punctured_has_basis {p : β → Prop} {s : β → set α} {a : α} (h : (𝓝 a).has_basis p s) :
  (𝓝* a).has_basis p (λ i, s i \ {a}) :=
nhds_within_has_basis h ({a}ᶜ)

lemma nhds_punctured_basis_open (a : α) :
  (𝓝* a).has_basis (λ u, a ∈ u ∧ is_open u) (λ u, u \ {a}) :=
nhds_within_basis_open a ({a}ᶜ)

lemma continuous_at_of_tendsto_punctured [topological_space β] (f : α → β) (a : α) :
  tendsto f (𝓝* a) (𝓝 $ f a) → continuous_at f a :=
begin
  rw [continuous_at, tendsto_nhds, tendsto_nhds],
  intros h s hsopen hsa,
  change (a ∈ f ⁻¹' s) at hsa,
  have := mem_nhds_within_insert (h s hsopen hsa),
  rwa [ compl_eq_univ_diff, insert_diff_singleton, insert_eq_of_mem $ hsa,
        insert_eq_of_mem $ mem_univ a, nhds_within_univ ] at this,
end

lemma continuous_at_iff_tendsto_punctured [topological_space β] (f : α → β) (a : α) :
  tendsto f (𝓝* a) (𝓝 $ f a) ↔ continuous_at f a :=
⟨continuous_at_of_tendsto_punctured f a, tendsto_nhds_within_of_tendsto_nhds⟩

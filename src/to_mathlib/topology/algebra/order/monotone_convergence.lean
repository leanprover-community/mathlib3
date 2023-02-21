import topology.algebra.order.monotone_convergence
import to_mathlib.order.filter.at_top_bot

open filter set function finset
open_locale filter topology classical

variables {α β : Type*}

lemma tendsto_of_antitone {ι α : Type*} [preorder ι] [topological_space α]
  [conditionally_complete_linear_order α] [order_topology α] {f : ι → α} (h_mono : antitone f) :
  tendsto f at_top at_bot ∨ (∃ l, tendsto f at_top (𝓝 l)) :=
if H : bdd_below (range f) then or.inr ⟨_, tendsto_at_top_cinfi h_mono H⟩
else or.inl $ tendsto_at_top_at_bot_of_antitone' h_mono H

lemma tendsto_at_top_iff_tendsto_range_at_top
  [topological_space α] [conditionally_complete_linear_order α] [order_topology α]
  [no_max_order α] {f : finset ℕ → α} {x : α} (hf : monotone f) :
  tendsto f at_top (𝓝 x) ↔ tendsto (λ n : ℕ, f (range n)) at_top (𝓝 x) :=
tendsto_iff_tendsto_subseq_of_monotone hf tendsto_finset_range

lemma tendsto_iff_tendsto_subseq_of_antitone {ι₁ ι₂ α : Type*} [semilattice_sup ι₁] [preorder ι₂]
  [nonempty ι₁] [topological_space α] [conditionally_complete_linear_order α] [order_topology α]
  [no_min_order α] {f : ι₂ → α} {φ : ι₁ → ι₂} {l : α} (hf : antitone f)
  (hg : tendsto φ at_top at_top) :
  tendsto f at_top (𝓝 l) ↔ tendsto (f ∘ φ) at_top (𝓝 l) :=
begin
  split; intro h,
  { exact h.comp hg },
  { rcases tendsto_of_antitone hf with h' | ⟨l', hl'⟩,
    { exact (not_tendsto_at_bot_of_tendsto_nhds h (h'.comp hg)).elim },
    { rwa tendsto_nhds_unique h (hl'.comp hg) } }
end

lemma tendsto_at_top_iff_tendsto_range_at_top'
  [topological_space α] [conditionally_complete_linear_order α] [order_topology α]
  [no_min_order α] {f : finset ℕ → α} {x : α} (hf : antitone f) :
  tendsto f at_top (𝓝 x) ↔ tendsto (λ n : ℕ, f (range n)) at_top (𝓝 x) :=
tendsto_iff_tendsto_subseq_of_antitone hf tendsto_finset_range

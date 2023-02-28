import to_mathlib.data.finset.image
import topology.basic

open finset filter function classical
open_locale topology big_operators filter

variables {α : Type*} {β : Type*} {γ : Type*} {R K E : Type*}

variables [topological_space α]

lemma tendsto_finset_map_subtype_at_top (p : β → Prop) [decidable_pred p]
  (f : finset β → α) (F : filter α)
  (h : tendsto (λ t : finset (subtype p), f (t.map (embedding.subtype p))) at_top F) :
  tendsto (f ∘ finset.filter p) at_top F :=
begin
  classical,
  rw tendsto_at_top' at h ⊢,
  intros t ht,
  obtain ⟨u, hu⟩ := h t ht,
  refine ⟨u.map (embedding.subtype p), λ v hv, _⟩,
  simpa only [subtype_map] using hu (v.subtype p) _,
  rwa [ge_iff_le, ←(finset.subtype_map_gc _)]
end

lemma tendsto_union_map_subtype_at_top [decidable_eq β] (p : β → Prop) :
  tendsto (λ (pq : finset (subtype p) × finset (subtype (λ i, ¬ p i))),
    (pq.1.map (embedding.subtype _)) ∪ (pq.2.map (embedding.subtype _))) at_top at_top :=
begin
  intro,
  simp only [mem_at_top_sets, ge_iff_le, le_eq_subset, filter.mem_map, set.mem_preimage,
             prod.forall, prod.exists, prod.mk_le_mk, and_imp, forall_exists_index],
  intros s hs,
  classical,
  refine ⟨s.subtype p, s.subtype _, λ t u ht hu, hs _ _⟩,
  rw [←filter_union_filter_neg_eq p s, ←subtype_map, ←subtype_map],
  exact union_subset_union (finset.monotone_map _ ht) (finset.monotone_map _ hu)
end

lemma tendsto_prod_mk_subtype_at_top (p : β → Prop) [decidable_pred p] :
  tendsto (λ s : finset β, (s.subtype p, s.subtype (λ i, ¬ p i))) at_top at_top :=
begin
  classical,
  intro,
  simp only [mem_at_top_sets, ge_iff_le, prod.forall, prod.exists, prod.mk_le_mk, le_eq_subset,
             and_imp, filter.mem_map, set.mem_preimage, forall_exists_index],
  intros t u htu,
  refine ⟨t.map (embedding.subtype _) ∪ u.map (embedding.subtype _), λ s hs, htu _ _ _ _⟩,
  { rw ←finset.map_subtype_subtype _ t,
    exact subtype_mono (union_subset_left hs) },
  { rw ←finset.map_subtype_subtype _ u,
    convert subtype_mono (union_subset_right hs) }
end

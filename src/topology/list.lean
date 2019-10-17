/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Topology on lists and vectors.
-/
import topology.constructions

open topological_space set filter

variables {α : Type*} {β : Type*}

instance [topological_space α] : topological_space (list α) :=
topological_space.mk_of_nhds (traverse nhds)

lemma nhds_list [topological_space α] (as : list α) : nhds as = traverse nhds as :=
begin
  refine nhds_mk_of_nhds _ _ _ _,
  { assume l, induction l,
    case list.nil { exact le_refl _ },
    case list.cons : a l ih {
      suffices : list.cons <$> pure a <*> pure l ≤ list.cons <$> nhds a <*> traverse nhds l,
      { simpa only [-filter.pure_def] with functor_norm using this },
      exact filter.seq_mono (filter.map_mono $ pure_le_nhds a) ih } },
  { assume l s hs,
    rcases (mem_traverse_sets_iff _ _).1 hs with ⟨u, hu, hus⟩, clear as hs,
    have : ∃v:list (set α), l.forall₂ (λa s, is_open s ∧ a ∈ s) v ∧ sequence v ⊆ s,
    { induction hu generalizing s,
      case list.forall₂.nil : hs this { existsi [], simpa only [list.forall₂_nil_left_iff, exists_eq_left] },
      case list.forall₂.cons : a s as ss ht h ih t hts {
        rcases mem_nhds_sets_iff.1 ht with ⟨u, hut, hu⟩,
        rcases ih (subset.refl _) with ⟨v, hv, hvss⟩,
        exact ⟨u::v, list.forall₂.cons hu hv,
          subset.trans (set.seq_mono (set.image_subset _ hut) hvss) hts⟩ } },
    rcases this with ⟨v, hv, hvs⟩,
    refine ⟨sequence v, mem_traverse_sets _ _ _, hvs, _⟩,
    { exact hv.imp (assume a s ⟨hs, ha⟩, mem_nhds_sets hs ha) },
    { assume u hu,
      have hu := (list.mem_traverse _ _).1 hu,
      have : list.forall₂ (λa s, is_open s ∧ a ∈ s) u v,
      { refine list.forall₂.flip _,
        replace hv := hv.flip,
        simp only [list.forall₂_and_left, flip] at ⊢ hv,
        exact ⟨hv.1, hu.flip⟩ },
      refine mem_sets_of_superset _ hvs,
      exact mem_traverse_sets _ _ (this.imp $ assume a s ⟨hs, ha⟩, mem_nhds_sets hs ha) } }
end

lemma nhds_nil [topological_space α] : nhds ([] : list α) = pure [] :=
by rw [nhds_list, list.traverse_nil _]; apply_instance

lemma nhds_cons [topological_space α] (a : α) (l : list α) :
  nhds (a :: l) = list.cons <$> nhds a <*> nhds l  :=
by rw [nhds_list, list.traverse_cons _, ← nhds_list]; apply_instance

namespace list
variables [topological_space α] [topological_space β]

lemma tendsto_cons' {a : α} {l : list α} :
  tendsto (λp:α×list α, list.cons p.1 p.2) ((nhds a).prod (nhds l)) (nhds (a :: l)) :=
by rw [nhds_cons, tendsto, map_prod]; exact le_refl _

lemma tendsto_cons {α : Type*} {f : α → β} {g : α → list β}
  {a : _root_.filter α} {b : β} {l : list β} (hf : tendsto f a (nhds b)) (hg : tendsto g a (nhds l)) :
  tendsto (λa, list.cons (f a) (g a)) a (nhds (b :: l)) :=
tendsto_cons'.comp (tendsto.prod_mk hf hg)

lemma tendsto_cons_iff {β : Type*} {f : list α → β} {b : _root_.filter β} {a : α} {l : list α} :
  tendsto f (nhds (a :: l)) b ↔ tendsto (λp:α×list α, f (p.1 :: p.2)) ((nhds a).prod (nhds l)) b :=
have nhds (a :: l) = ((nhds a).prod (nhds l)).map (λp:α×list α, (p.1 :: p.2)),
begin
  simp only
    [nhds_cons, filter.prod_eq, (filter.map_def _ _).symm, (filter.seq_eq_filter_seq _ _).symm],
  simp [-filter.seq_eq_filter_seq, -filter.map_def, (∘)] with functor_norm,
end,
by rw [this, filter.tendsto_map'_iff]

lemma tendsto_nhds {β : Type*} {f : list α → β} {r : list α → _root_.filter β}
  (h_nil : tendsto f (pure []) (r []))
  (h_cons : ∀l a, tendsto f (nhds l) (r l) → tendsto (λp:α×list α, f (p.1 :: p.2)) ((nhds a).prod (nhds l)) (r (a::l))) :
  ∀l, tendsto f (nhds l) (r l)
| []     := by rwa [nhds_nil]
| (a::l) := by rw [tendsto_cons_iff]; exact h_cons l a (tendsto_nhds l)

lemma continuous_at_length :
  ∀(l : list α), continuous_at list.length l :=
begin
  simp only [continuous_at, nhds_discrete],
  refine tendsto_nhds _ _,
  { exact tendsto_pure_pure _ _ },
  { assume l a ih,
    dsimp only [list.length],
    refine tendsto.comp (tendsto_pure_pure (λx, x + 1) _) _,
    refine tendsto.comp ih tendsto_snd }
end

lemma tendsto_insert_nth' {a : α} : ∀{n : ℕ} {l : list α},
  tendsto (λp:α×list α, insert_nth n p.1 p.2) ((nhds a).prod (nhds l)) (nhds (insert_nth n a l))
| 0     l  := tendsto_cons'
| (n+1) [] :=
  suffices tendsto (λa, []) (nhds a) (nhds ([] : list α)),
    by simpa [nhds_nil, tendsto, map_prod, -filter.pure_def, (∘), insert_nth],
  tendsto_const_nhds
| (n+1) (a'::l) :=
  have (nhds a).prod (nhds (a' :: l)) =
    ((nhds a).prod ((nhds a').prod (nhds l))).map (λp:α×α×list α, (p.1, p.2.1 :: p.2.2)),
  begin
    simp only
      [nhds_cons, filter.prod_eq, (filter.map_def _ _).symm, (filter.seq_eq_filter_seq _ _).symm],
    simp [-filter.seq_eq_filter_seq, -filter.map_def, (∘)] with functor_norm
  end,
  begin
    rw [this, tendsto_map'_iff],
    exact tendsto_cons
      (tendsto_fst.comp tendsto_snd)
      ((@tendsto_insert_nth' n l).comp (tendsto.prod_mk tendsto_fst (tendsto_snd.comp tendsto_snd)))
  end

lemma tendsto_insert_nth {β : Type*} {n : ℕ} {a : α} {l : list α} {f : β → α} {g : β → list α}
  {b : _root_.filter β} (hf : tendsto f b (nhds a)) (hg : tendsto g b (nhds l)) :
  tendsto (λb:β, insert_nth n (f b) (g b)) b (nhds (insert_nth n a l)) :=
tendsto_insert_nth'.comp (tendsto.prod_mk hf hg)

lemma continuous_insert_nth {n : ℕ} : continuous (λp:α×list α, insert_nth n p.1 p.2) :=
continuous_iff_continuous_at.mpr $
  assume ⟨a, l⟩, by rw [continuous_at, nhds_prod_eq]; exact tendsto_insert_nth'

lemma tendsto_remove_nth : ∀{n : ℕ} {l : list α},
  tendsto (λl, remove_nth l n) (nhds l) (nhds (remove_nth l n))
| _ []      := by rw [nhds_nil]; exact tendsto_pure_nhds _ _
| 0 (a::l) := by rw [tendsto_cons_iff]; exact tendsto_snd
| (n+1) (a::l) :=
  begin
    rw [tendsto_cons_iff],
    dsimp [remove_nth],
    exact tendsto_cons tendsto_fst ((@tendsto_remove_nth n l).comp tendsto_snd)
  end

lemma continuous_remove_nth {n : ℕ} : continuous (λl : list α, remove_nth l n) :=
continuous_iff_continuous_at.mpr $ assume a, tendsto_remove_nth

end list

namespace vector
open list

instance (n : ℕ) [topological_space α] : topological_space (vector α n) :=
by unfold vector; apply_instance

lemma cons_val {n : ℕ} {a : α} : ∀{v : vector α n}, (a :: v).val = a :: v.val
| ⟨l, hl⟩ := rfl

lemma tendsto_cons [topological_space α] {n : ℕ} {a : α} {l : vector α n}:
  tendsto (λp:α×vector α n, vector.cons p.1 p.2) ((nhds a).prod (nhds l)) (nhds (a :: l)) :=
by
  simp [tendsto_subtype_rng, cons_val];
  exact tendsto_cons tendsto_fst (tendsto.comp continuous_at_subtype_val tendsto_snd)

lemma tendsto_insert_nth
  [topological_space α] {n : ℕ} {i : fin (n+1)} {a:α} :
  ∀{l:vector α n}, tendsto (λp:α×vector α n, insert_nth p.1 i p.2)
    ((nhds a).prod (nhds l)) (nhds (insert_nth a i l))
| ⟨l, hl⟩ :=
begin
  rw [insert_nth, tendsto_subtype_rng],
  simp [insert_nth_val],
  exact list.tendsto_insert_nth tendsto_fst (tendsto.comp continuous_at_subtype_val tendsto_snd : _)
end

lemma continuous_insert_nth' [topological_space α] {n : ℕ} {i : fin (n+1)} :
  continuous (λp:α×vector α n, insert_nth p.1 i p.2) :=
continuous_iff_continuous_at.mpr $ assume ⟨a, l⟩,
  by rw [continuous_at, nhds_prod_eq]; exact tendsto_insert_nth

lemma continuous_insert_nth [topological_space α] [topological_space β] {n : ℕ} {i : fin (n+1)}
  {f : β → α} {g : β → vector α n} (hf : continuous f) (hg : continuous g) :
  continuous (λb, insert_nth (f b) i (g b)) :=
continuous_insert_nth'.comp (continuous.prod_mk hf hg)

lemma continuous_at_remove_nth [topological_space α] {n : ℕ} {i : fin (n+1)} :
  ∀{l:vector α (n+1)}, continuous_at (remove_nth i) l
| ⟨l, hl⟩ :=
--  ∀{l:vector α (n+1)}, tendsto (remove_nth i) (nhds l) (nhds (remove_nth i l))
--| ⟨l, hl⟩ :=
begin
  rw [continuous_at, remove_nth, tendsto_subtype_rng],
  simp [remove_nth_val],
  exact tendsto.comp list.tendsto_remove_nth continuous_at_subtype_val
end

lemma continuous_remove_nth [topological_space α] {n : ℕ} {i : fin (n+1)} :
  continuous (remove_nth i : vector α (n+1) → vector α n) :=
continuous_iff_continuous_at.mpr $ assume ⟨a, l⟩, continuous_at_remove_nth

end vector


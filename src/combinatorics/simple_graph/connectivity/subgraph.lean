/-
Copyright (c) 2023 Kyle Miller, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Rémi Bottinelli
-/

import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.subgraph
/-!
# Connectivity of subgraphs and induced graphs

* `simple_graph.subgraph.connected` gives subgraphs the connectivity
  predicate via `simple_graph.subgraph.coe`.

-/

universes u v

namespace simple_graph

variables {V : Type u} {V' : Type v} {G : simple_graph V} {G' : simple_graph V'}

namespace subgraph

/-- A subgraph is connected if it is connected as a simple graph. -/
@[reducible] def connected (H : G.subgraph) : Prop := H.coe.connected

lemma connected_iff (H : G.subgraph) :
  H.connected ↔ H.coe.preconnected ∧ H.verts.nonempty :=
by rw [subgraph.connected, connected_iff, set.nonempty_coe_sort]


lemma singleton_subgraph_connected {v : V} : (G.singleton_subgraph v).connected :=
begin
  split,
  rintros ⟨a, ha⟩ ⟨b, hb⟩,
  simp only [singleton_subgraph_verts, set.mem_singleton_iff] at ha hb,
  subst_vars
end

@[simp] lemma subgraph_of_adj_connected {v w : V} (hvw : G.adj v w) :
  (G.subgraph_of_adj hvw).connected :=
begin
  split,
  rintro ⟨a, ha⟩ ⟨b, hb⟩,
  simp only [subgraph_of_adj_verts, set.mem_insert_iff, set.mem_singleton_iff] at ha hb,
  obtain (rfl|rfl) := ha; obtain (rfl|rfl) := hb;
    refl <|> { apply adj.reachable, simp },
end

lemma top_induce_pair_connected_of_adj {u v : V} (huv : G.adj u v) :
  ((⊤ : G.subgraph).induce {u, v}).connected :=
begin
  rw ←subgraph.subgraph_of_adj_eq_induce huv,
  exact subgraph_of_adj_connected huv,
end

@[mono]
lemma connected.mono {H H' : G.subgraph}
  (hle : H ≤ H') (hv : H.verts = H'.verts) (h : H.connected) : H'.connected :=
begin
  rw ← subgraph.copy_eq H' H.verts hv H'.adj rfl,
  apply h.mono _,
  rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw,
  exact hle.2 hvw,
end

lemma connected.sup {H K : G.subgraph}
  (hH : H.connected) (hK : K.connected) (hn : (H ⊓ K).verts.nonempty ) :
  (H ⊔ K).connected :=
begin
  rw [subgraph.connected, connected_iff_exists_forall_reachable],
  obtain ⟨u, hu, hu'⟩ := hn,
  use ⟨u, or.inl hu⟩,
  rintro ⟨v, hv|hv⟩,
  { exact reachable.map (subgraph.inclusion (le_sup_left : H ≤ H ⊔ K)) (hH ⟨u, hu⟩ ⟨v, hv⟩), },
  { exact reachable.map (subgraph.inclusion (le_sup_right : K ≤ H ⊔ K)) (hK ⟨u, hu'⟩ ⟨v, hv⟩), },
end

lemma _root_.simple_graph.walk.to_subgraph_connected {u v : V} (p : G.walk u v) :
  p.to_subgraph.connected :=
begin
  induction p with _ u v w a q ih,
  { apply singleton_subgraph_connected, },
  { rw [walk.to_subgraph],
    refine subgraph.connected.sup (subgraph_of_adj_connected a) ih ⟨v, ⟨or.inr _, _⟩⟩;
    simp only [set.mem_singleton, walk.verts_to_subgraph, set.mem_set_of_eq,
               walk.start_mem_support], },
end

lemma induce_union_connected {H : G.subgraph} {s t : set V}
  (sconn : (H.induce s).connected) (tconn : (H.induce t).connected) (sintert : (s ⊓ t).nonempty ) :
  (H.induce $ s ⊔ t).connected :=
begin
  refine (subgraph.connected.sup sconn tconn sintert).mono _ _,
  { apply subgraph.le_induce_sup, },
  { simp, },
end

lemma connected.adj_union {H K : G.subgraph}
  (Hconn : H.connected) (Kconn : K.connected) {u v : V} (uH : u ∈ H.verts) (vK : v ∈ K.verts)
  (huv : G.adj u v) :
  ((⊤ : G.subgraph).induce {u, v} ⊔ H ⊔ K).connected :=
begin
  refine subgraph.connected.sup _ ‹_› _,
  { refine subgraph.connected.sup (subgraph.top_induce_pair_connected_of_adj huv) ‹_› _,
    exact ⟨u, by simp [uH]⟩, },
  { exact ⟨v, by simp [vK]⟩ },
end

lemma connected_iff_forall_exists_walk_subgraph (H : G.subgraph) :
  H.connected ↔ H.verts.nonempty ∧ ∀ {u} (hu : u ∈ H.verts) {v} (hv : v ∈ H.verts),
                  ∃ p : G.walk u v, p.to_subgraph ≤ H :=
begin
  split,
  { rw [subgraph.connected_iff],
    rintro ⟨Hp, Hn⟩,
    refine ⟨Hn, λ u hu v hv, ⟨(Hp ⟨u, hu⟩ ⟨v, hv⟩).some.map (subgraph.hom _), _⟩⟩,
    simp only [walk.to_subgraph_map],
    apply subgraph.coe_subgraph_le, },
  { rintro ⟨Hn,Hw⟩,
    rw [subgraph.connected, connected_iff_exists_forall_reachable],
    refine ⟨⟨Hn.some, Hn.some_spec⟩, λ w, _⟩,
    obtain ⟨w, hw⟩ := w,
    obtain ⟨p, h⟩ := Hw Hn.some_spec hw,
    exact reachable.map (subgraph.inclusion h) (p.to_subgraph_connected
            ⟨_, p.start_mem_verts_to_subgraph⟩ ⟨_, p.end_mem_verts_to_subgraph⟩), },
end

end subgraph

section induced_subgraphs

lemma induce_union_connected {s t : set V}
  (sconn : (G.induce s).connected) (tconn : (G.induce t).connected) (sintert : (s ∩ t).nonempty ) :
  (G.induce $ s ∪ t).connected :=
begin
  rw simple_graph.induce_eq_coe_induce_top at sconn tconn ⊢,
  exact subgraph.induce_union_connected sconn tconn sintert,
end

lemma induce_pair_connected_of_adj {u v : V} (huv : G.adj u v) :
  (G.induce {u, v}).connected :=
begin
  rw simple_graph.induce_eq_coe_induce_top,
  exact subgraph.top_induce_pair_connected_of_adj huv,
end

lemma induce_walk_support_connected {u v : V} (p : G.walk u v) :
  (G.induce {v | v ∈ p.support}).connected :=
begin
  rw induce_eq_coe_induce_top,
  exact (p.to_subgraph_connected).mono p.to_subgraph_le_induce_support p.verts_to_subgraph,
end

lemma induce_connected_adj_union {s t : set V}
  (sconn : (G.induce s).connected) (tconn : (G.induce t).connected) {v w} (hv : v ∈ s) (hw : w ∈ t)
  (a : G.adj v w) : (G.induce $ s ∪ t).connected :=
begin
  have : {v, w} ⊆ s ∪ t, by
  { rw [set.insert_subset, set.singleton_subset_iff], exact ⟨or.inl hv, or.inr hw⟩, },
  rw induce_eq_coe_induce_top at sconn tconn ⊢,
  convert (subgraph.connected.adj_union sconn tconn hv hw a).mono _ _,
  { simp only [subgraph.induce_verts], },
  { rw [sup_assoc, sup_le_iff],
    refine ⟨subgraph.induce_mono_right this, subgraph.le_induce_sup⟩, },
  { simpa only [subgraph.verts_sup, subgraph.induce_verts, set.union_assoc,
                set.union_eq_right_iff_subset], }
end

lemma induce_connected_of_patches {s : set V} {u} (hu : u ∈ s)
  (patches : ∀ {v} (hv : v ∈ s), ∃ (s' : set V) (sub : s' ⊆ s) (hu' : u ∈ s') (hv' : v ∈ s'),
             (G.induce s').reachable ⟨u, hu'⟩ ⟨v, hv'⟩ ) : (G.induce s).connected :=
begin
  rw connected_iff_exists_forall_reachable,
  refine ⟨⟨u, hu⟩, _⟩,
  rintro ⟨v, hv⟩,
  obtain ⟨sv, svs, hu', hv', ⟨uv⟩⟩ := patches hv,
  exact ⟨uv.map (induce_hom_of_le svs)⟩,
end

lemma induce_sUnion_connected_of_pairwise_not_disjoint {S : set (set V)} (Sn : S.nonempty)
  (Snd : ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ S → set.nonempty (s ∩ t))
  (Sc : ∀ ⦃s⦄, s ∈ S → (G.induce s).connected) :
  (G.induce $ ⋃₀ S).connected :=
begin
  obtain ⟨s, sS⟩ := Sn,
  obtain ⟨v, vs⟩ := (Sc sS).nonempty.some,
  fapply induce_connected_of_patches (set.subset_sUnion_of_mem sS vs),
  rintro w hw,
  simp only [set.mem_sUnion, exists_prop] at hw,
  obtain ⟨t, tS, wt⟩ := hw,
  refine ⟨s ∪ t, set.union_subset (set.subset_sUnion_of_mem sS) (set.subset_sUnion_of_mem tS),
          or.inl vs, or.inr wt, induce_union_connected (Sc sS) (Sc tS) (Snd sS tS) _ _⟩,
end

lemma extend_finset_to_connected (Gpc : G.preconnected) {t : finset V} (tn : t.nonempty) :
  ∃ t', t ⊆ t' ∧ (G.induce (t' : set V)).connected :=
begin
  classical,
  obtain ⟨u, ut⟩ := tn,
  refine ⟨finset.bUnion t (λ v, (Gpc u v).some.support.to_finset), λ v vt, _, _⟩,
  { simp only [finset.mem_bUnion, list.mem_to_finset, exists_prop],
    refine ⟨v, vt, walk.end_mem_support _⟩, },
  { apply @induce_connected_of_patches _ G _ u _ (λ v hv, _),
    { simp only [finset.coe_bUnion, finset.mem_coe, list.coe_to_finset, set.mem_Union,
                 set.mem_set_of_eq, walk.start_mem_support, exists_prop, and_true],
      exact ⟨u, ut⟩, },
    simp only [finset.mem_coe, finset.mem_bUnion, list.mem_to_finset, exists_prop] at hv,
    obtain ⟨w, wt, hw⟩ := hv,
    refine ⟨{x | x ∈ (Gpc u w).some.support}, _, _⟩,
    { simp only [finset.coe_bUnion, finset.mem_coe, list.coe_to_finset],
      exact λ x xw, set.mem_Union₂.mpr ⟨w,wt,xw⟩, },
    { simp only [set.mem_set_of_eq, walk.start_mem_support, exists_true_left],
      refine ⟨hw, induce_walk_support_connected _ _ _⟩, }, }
end

end induced_subgraphs

end simple_graph

/-
Copyright (c) 2023 Kyle Miller, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Rémi Bottinelli
-/

import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.subgraph
/-!
# Connectivity of subgraphs
-/

universes u v

namespace simple_graph

variables {V : Type u} {V' : Type v} {G : simple_graph V} {G' : simple_graph V'}

/-- A subgraph is connected if it is connected as a simple graph. -/
@[reducible] def subgraph.connected (H : G.subgraph) : Prop := H.coe.connected

lemma subgraph.connected_iff (H : G.subgraph) :
  H.connected ↔ H.coe.preconnected ∧ H.verts.nonempty :=
begin
  change H.coe.connected ↔ _,
  rw [connected_iff, set.nonempty_coe_sort],
end

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

lemma induce_singleton_connected (v : V) :
  (G.induce {v}).connected :=
begin
  rw [induce_singleton_eq_top],
  apply top_connected,
end

@[mono]
lemma subgraph.connected.mono {H H' : G.subgraph}
  (hle : H ≤ H') (hv : H.verts = H'.verts) (h : H.connected) : H'.connected :=
begin
  rw ← subgraph.copy_eq H' H.verts hv H'.adj rfl,
  apply h.mono _,
  rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw,
  exact hle.2 hvw,
end

lemma subgraph.connected.sup {H K : G.subgraph}
  (hH : H.connected) (hK : K.connected) (hn : (H ⊓ K).verts.nonempty ) :
  (H ⊔ K).connected :=
begin
  change (H ⊔ K).coe.connected,
  rw [connected_iff_exists_forall_reachable],
  obtain ⟨u, hu, hu'⟩ := hn,
  use ⟨u, or.inl hu⟩,
  rintro ⟨v, hv|hv⟩,
  { exact reachable.map (subgraph.inclusion (le_sup_left : H ≤ H ⊔ K)) (hH ⟨u, hu⟩ ⟨v, hv⟩), },
  { exact reachable.map (subgraph.inclusion (le_sup_right : K ≤ H ⊔ K)) (hK ⟨u, hu'⟩ ⟨v, hv⟩), },
end

lemma subgraph.induce_union_connected {H : G.subgraph} {s t : set V}
  (sconn : (H.induce s).connected) (tconn : (H.induce t).connected) (sintert : (s ⊓ t).nonempty ) :
  (H.induce $ s ⊔ t).connected :=
begin
  apply subgraph.connected.mono _ _ (subgraph.connected.sup sconn tconn sintert),
  { apply subgraph.sup_induce_le_induce_sup, },
  { simp, },
end

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
  convert subgraph_of_adj_connected huv,
  rw [simple_graph.induce_eq_coe_induce_top],
  congr,
  exact (subgraph.subgraph_of_adj_eq_induce huv).symm,
end

lemma subgraph.top_induce_pair_connected_of_adj {u v : V} (huv : G.adj u v) :
  ((⊤ : G.subgraph).induce {u, v}).connected :=
begin
  change connected (subgraph.coe _),
  rw ← induce_eq_coe_induce_top,
  exact induce_pair_connected_of_adj huv,
end

lemma subgraph.connected.adj_union {H K : G.subgraph}
  (Hconn : H.connected) (Kconn : K.connected) {u v : V} (uH : u ∈ H.verts) (vK : v ∈ K.verts)
  (huv : G.adj u v) :
  ((⊤ : G.subgraph).induce {u, v} ⊔ H ⊔ K).connected :=
begin
  refine subgraph.connected.sup _ ‹_› _,
  { refine subgraph.connected.sup (subgraph.top_induce_pair_connected_of_adj huv) ‹_› _,
    exact ⟨u, by simp [uH]⟩, },
  { exact ⟨v, by simp [vK]⟩ },
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
    refine ⟨subgraph.induce_mono_right this, subgraph.sup_induce_le_induce_sup⟩, },
  { simpa only [subgraph.verts_sup, subgraph.induce_verts, set.union_assoc,
               set.union_eq_right_iff_subset], }
end

lemma subgraph.connected_of_patches {H : G.subgraph} (u : H.verts)
  (patches : ∀ v : H.verts,
               ∃ (H' : G.subgraph) (sub : H' ≤ H) (u' : ↑u ∈ H'.verts) (v' : ↑v ∈ H'.verts),
                  H'.coe.reachable ⟨u,u'⟩ ⟨v,v'⟩ ) : H.coe.connected :=
begin
  rw connected_iff_exists_forall_reachable,
  refine ⟨u, λ v, _⟩,
  obtain ⟨Hv, HvH, u', v',⟨rv⟩⟩ := patches v,
  convert nonempty.intro (rv.map (subgraph.inclusion HvH));
  rw [←subtype.coe_inj,simple_graph.subgraph.inclusion_apply_coe];
  refl,
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

lemma walk.to_subgraph_connected {u v : V} (p : G.walk u v) :
  p.to_subgraph.connected :=
begin
  induction p with _ u v w a q ih,
  { apply singleton_subgraph_connected, },
  { rw [walk.to_subgraph],
    refine subgraph.connected.sup (subgraph_of_adj_connected a) ih ⟨v, ⟨or.inr _, _⟩⟩;
    simp only [set.mem_singleton, walk.verts_to_subgraph, set.mem_set_of_eq,
               walk.start_mem_support], },
end

lemma induce_walk_support_connected {u v : V} (p : G.walk u v) :
  (G.induce $ {v | v ∈ p.support}).connected :=
begin
  rw induce_eq_coe_induce_top,
  exact (p.to_subgraph_connected).mono p.to_subgraph_le_induce_support p.verts_to_subgraph,
end

lemma induce_sUnion_connected_of_pairwise_not_disjoint {S : set (set V)} (Sn : S.nonempty)
  (Snd : ∀ {s}, s ∈ S → ∀ {t}, t ∈ S → set.nonempty (s ∩ t))
  (Sc : ∀ {s}, s ∈ S → (G.induce s).connected) :
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

end simple_graph

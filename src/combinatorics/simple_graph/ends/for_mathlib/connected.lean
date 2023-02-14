import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.subgraph


open simple_graph

universes u v

namespace simple_graph

variables {V : Type u} {V' : Type v} (G : simple_graph V) (G' : simple_graph V')
variables {G}

lemma induce_singleton_connected (G : simple_graph V) (v : V) :
  (G.induce {v}).connected :=
begin
  rw connected_iff,
  refine ⟨_, by simp⟩,
  rintro ⟨x, hx⟩ ⟨y, hy⟩,
  rw set.mem_singleton_iff at hx hy,
  subst_vars,
end

lemma induce_connected_union {H K : set V}
  (Hconn : (G.induce H).connected) (Kconn : (G.induce K).connected) (HinterK : (H ⊓ K).nonempty ) :
  (G.induce $ H ⊔ K).connected :=
begin
  obtain ⟨u, huH, huK⟩ := HinterK,
  rw connected_iff_basepoint,
  use ⟨u, or.inl huH⟩,
  rintro ⟨v, hv|hv⟩,
  { obtain ⟨p⟩ := (Hconn ⟨u, huH⟩ ⟨v, hv⟩),
    exact ⟨p.map (induce_hom_of_le le_sup_left : (G.induce H) →g (G.induce $ H ⊔ K))⟩, },
  { obtain ⟨p⟩ := (Kconn ⟨u, huK⟩ ⟨v, hv⟩),
    exact ⟨p.map (induce_hom_of_le le_sup_right : (G.induce K) →g (G.induce $ H ⊔ K))⟩, },
end

lemma induce_pair_connected_of_adj {u v : V} (huv : G.adj u v) :
  (G.induce {u, v}).connected :=
begin
  rw connected_iff,
  refine ⟨_, by simp⟩,
  rintro ⟨x, hx⟩ ⟨y, hy⟩,
  simp only [set.mem_insert_iff, set.mem_singleton_iff] at hx hy,
  obtain rfl|rfl := hx; obtain rfl|rfl := hy;
    refl <|> { refine ⟨walk.cons _ walk.nil⟩, simp [huv, huv.symm] }
end

lemma induce_connected_adj_union {H K : set V}
  (Hconn : (G.induce H).connected) (Kconn : (G.induce K).connected) {v w} (hv : v ∈ H) (hw : w ∈ K)
  (a : G.adj v w) : (G.induce $ H ⊔ K).connected :=
begin
  have : H ⊔ K = H ⊔ {v, w} ⊔ K, by
  { rw [set.sup_eq_union, set.union_comm H {v, w}, set.union_assoc], symmetry,
    apply set.union_eq_self_of_subset_left,
    simp only [set.insert_subset, set.singleton_subset_iff, hv, hw, set.mem_union, true_or,
               or_true, and_self], },
  rw this,
  refine induce_connected_union
    (induce_connected_union Hconn (induce_pair_connected_of_adj a) _) Kconn _,
  { refine ⟨v, hv, _⟩, simp, },
  { refine ⟨w, or.inr _, hw⟩, simp, }
end

lemma induce_walk_support_connected [decidable_eq V] :
  ∀ {u v : V} (p : G.walk u v), (G.induce $ (p.support.to_finset : set V)).connected
| _ _ (walk.nil' u) := by { convert induce_singleton_connected G u; simp, }
| _ _ (walk.cons' u v w a p) := by
  begin
    convert induce_connected_union (induce_pair_connected_of_adj a) (induce_walk_support_connected p) _,
    any_goals
    { simp only [walk.support_cons, list.to_finset_cons, finset.coe_insert, list.coe_to_finset,
                 set.sup_eq_union, set.insert_union, set.singleton_union],
      rw @set.insert_eq_of_mem _ v, simp only [set.mem_set_of_eq, walk.start_mem_support], },
    { refine ⟨v,_⟩,
      simp only [list.coe_to_finset, set.inf_eq_inter, set.mem_inter_iff, set.mem_insert_iff,
                 set.mem_singleton, or_true, set.mem_set_of_eq, walk.start_mem_support, and_self], },
  end

lemma induce_connected_of_patches {H : set V} {u} (hu : u ∈ H)
  (patches : ∀ {v} (hv : v ∈ H), ∃ (H' : set V) (sub : H' ⊆ H) (hu' : u ∈ H') (hv' : v ∈ H'),
             (G.induce H').reachable ⟨u,hu'⟩ ⟨v,hv'⟩ ) : (G.induce H).connected :=
begin
  rw connected_iff_basepoint,
  refine ⟨⟨u, hu⟩, _⟩,
  rintro ⟨v, hv⟩,
  obtain ⟨Hv, HvH, hu', hv', ⟨uv⟩⟩ := patches hv,
  exact ⟨uv.map (induce_hom_of_le HvH)⟩,
end

lemma induce_connected_union_of_pairwise_not_disjoint {H : set (set V)} (Hn : H.nonempty)
  (Hnd : ∀ {x}, x ∈ H → ∀ {y}, y ∈ H → set.nonempty (x ∩ y)) (Hc : ∀ {x}, x ∈ H →  (G.induce x).connected) :
  (G.induce H.sUnion).connected :=
begin
  obtain ⟨Hv,HvH⟩ := Hn,
  obtain ⟨v,vHv⟩ := (Hc HvH).nonempty.some,
  fapply induce_connected_of_patches (set.subset_sUnion_of_mem HvH vHv),
  rintro w hw,
  simp only [set.mem_sUnion, exists_prop] at hw,
  obtain ⟨Hw,HwH,wHw⟩ := hw,
  refine ⟨Hw ∪ Hv, set.union_subset (set.subset_sUnion_of_mem HwH) (set.subset_sUnion_of_mem HvH),
          or.inr vHv, or.inl wHw, induce_connected_union (Hc HwH) (Hc HvH) (Hnd HwH HvH) _ _⟩,
end

lemma extend_finset_to_connected [decidable_eq V] {G : simple_graph V}
  (Gpc : G.preconnected) {K : finset V} (Kn : K.nonempty) :
  ∃ K', K ⊆ K' ∧ (G.induce (K' : set V)).connected :=
begin
  obtain ⟨k₀, hk₀⟩ := Kn,
  refine ⟨finset.bUnion K (λ v, (Gpc k₀ v).some.support.to_finset), _, _⟩,
  { rintro k kK,
    simp only [finset.mem_bUnion, list.mem_to_finset, exists_prop],
    refine ⟨k, kK, walk.end_mem_support _⟩, },
  { apply @induce_connected_of_patches _ G _ k₀,
    { simp only [finset.coe_bUnion, finset.mem_coe, list.coe_to_finset, set.mem_Union,
                 set.mem_set_of_eq, walk.start_mem_support, exists_prop, and_true],
      exact ⟨k₀, hk₀⟩, },
    rintro v hv,
    simp only [finset.coe_bUnion, finset.mem_coe, subgraph.induce_verts, set.mem_Union,
               list.mem_to_finset, exists_prop] at hv,
    obtain ⟨k,kK,vk⟩ := hv,
    refine ⟨((Gpc k₀ k).some.support.to_finset : set V), _, _⟩,
    { rw finset.coe_subset, exact finset.subset_bUnion_of_mem _ kK,},
    { simp only [subtype.coe_mk, subgraph.induce_verts, finset.mem_coe, list.mem_to_finset,
                 walk.start_mem_support, exists_true_left],
      refine ⟨vk, induce_walk_support_connected _ _ _⟩, }, }
end

end simple_graph

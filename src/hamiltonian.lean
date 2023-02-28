import combinatorics.simple_graph.matching
import combinatorics.simple_graph.connectivity

.

noncomputable theory

-- note: set.bot_eq_empty is questionable as a simp lemma
@[simp] lemma prop.bot_eq_false : (⊥ : Prop) = false := rfl

variables {V V' : Type*} (G : simple_graph V)

namespace simple_graph

namespace subgraph
variables {G}

lemma adj.edge_vert {H : G.subgraph} {u v : V} (h : H.adj u v) : u ∈ H.verts := H.edge_vert h

end subgraph

lemma verts_singleton_iff_eq (H : G.subgraph) {v : V} :
  H.verts = {v} ↔ H = G.singleton_subgraph v :=
begin
  split,
  { intro h,
    ext,
    { rw h,
      simp, },
    { simp [-set.bot_eq_empty],
      intro ha,
      have ha1 := ha.edge_vert,
      have ha2 := ha.symm.edge_vert,
      rw [h] at ha1 ha2,
      simp at ha1 ha2,
      subst_vars,
      exact ha.ne rfl } },
  { rintro rfl,
    simp, }
end

namespace subgraph
variables {G}

lemma sup_induce_le_induce_union (H : G.subgraph) (s s' : set V) :
  H.induce s ⊔ H.induce s' ≤ H.induce (s ∪ s') :=
begin
  simp,
  split; mono; simp,
end

lemma induce_le_of_subset {H : G.subgraph} {s : set V} (hs : s ⊆ H.verts) :
  H.induce s ≤ H :=
calc H.induce s ≤ H.induce H.verts : induce_mono_right hs
            ... = H : by simp

lemma eq_bot_iff (H : G.subgraph) :
  H = ⊥ ↔ H.verts = ∅ :=
begin
  split,
  { rintro rfl,
    simp, },
  { intro h,
    ext,
    { simp [h] },
    { simp,
      intro h',
      simpa [h] using H.edge_vert h', } }
end

lemma sup_connected {H H' : G.subgraph} (hH : H.connected) (hH' : H'.connected)
  (v : V) (hv : v ∈ (H ⊓ H').verts) :
  (H ⊔ H').connected :=
begin
  let v' : (H ⊔ H').verts := ⟨v, or.inl hv.1⟩,
  haveI : nonempty (H ⊔ H').verts := ⟨v'⟩,
  split,
  rintros ⟨a, ha⟩ ⟨b, hb⟩,
  simp only [verts_sup, set.mem_union] at ha hb,
  obtain (ha|ha) := ha; obtain (hb|hb) := hb,
  { exact reachable.map (subgraph.inclusion (le_sup_left : H ≤ H ⊔ H')) (hH ⟨a, ha⟩ ⟨b, hb⟩) },
  { transitivity v',
    exact reachable.map (subgraph.inclusion (le_sup_left : H ≤ H ⊔ H')) (hH ⟨a, ha⟩ ⟨v, hv.1⟩),
    exact reachable.map (subgraph.inclusion (le_sup_right : H' ≤ H ⊔ H')) (hH' ⟨v, hv.2⟩ ⟨b, hb⟩) },
  { transitivity v',
    exact reachable.map (subgraph.inclusion (le_sup_right : H' ≤ H ⊔ H')) (hH' ⟨a, ha⟩ ⟨v, hv.2⟩),
    exact reachable.map (subgraph.inclusion (le_sup_left : H ≤ H ⊔ H')) (hH ⟨v, hv.1⟩ ⟨b, hb⟩), },
  { exact reachable.map (subgraph.inclusion (le_sup_right : H' ≤ H ⊔ H')) (hH' ⟨a, ha⟩ ⟨b, hb⟩) }
end

/-! ### Connected components of a subgraph as subgraphs -/

/-- The subgraph associated to a connected component. -/
def mk_component (H : G.subgraph) (c : H.coe.connected_component) : G.subgraph :=
H.induce (coe '' (H.coe.connected_component_mk ⁻¹' {c}))

@[simp] lemma mem_mk_component_verts (H : G.subgraph) (c : H.coe.connected_component) (v : V) :
  v ∈ (H.mk_component c).verts ↔ ∃ (hv : v ∈ H.verts), H.coe.connected_component_mk ⟨v, hv⟩ = c :=
by simp only [mk_component, induce_verts, set.mem_image, set.mem_preimage, set.mem_singleton_iff,
  set_coe.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right]

@[simp] lemma mk_component_adj (H : G.subgraph) (c : H.coe.connected_component) {v w : V} :
  (H.mk_component c).adj v w ↔
  H.adj v w ∧ ∃ (hv : v ∈ H.verts), H.coe.connected_component_mk ⟨v, hv⟩ = c :=
begin
  simp only [mk_component, induce_adj, set.mem_image, set.mem_preimage, set.mem_singleton_iff,
    set_coe.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right],
  split,
  { simp { contextual := tt }, },
  { simp { contextual := tt },
    rintro hvw hv rfl,
    existsi H.edge_vert hvw.symm,
    simpa using hvw.symm.coe.reachable, }
end

/-- The connected components of a subgraph as a set of subgraphs. -/
def components (H : G.subgraph) : set G.subgraph :=
{(H.mk_component c) | (c : H.coe.connected_component)}

@[simp] lemma mk_component_mem_components (H : G.subgraph) (c : H.coe.connected_component) :
  H.mk_component c ∈ H.components :=
by simp [mk_component, components]

lemma components_le {H C : G.subgraph} (hC : C ∈ H.components) : C ≤ H :=
begin
  obtain ⟨c, rfl⟩ := hC,
  apply induce_le_of_subset,
  simp only [set.image_subset_iff, subtype.coe_preimage_self, set.subset_univ],
end

lemma components_nonempty_verts {H C : G.subgraph} (hC : C ∈ H.components) :
  C.verts.nonempty :=
begin
  obtain ⟨c, rfl⟩ := hC,
  induction c using simple_graph.connected_component.ind with v,
  use v,
  simp,
end

lemma components_ne_bot {H C : G.subgraph} (hC : C ∈ H.components) :
  C ≠ ⊥ :=
begin
  intro h,
  rw [eq_bot_iff, ← set.not_nonempty_iff_eq_empty] at h,
  exact absurd (components_nonempty_verts hC) h,
end

lemma components.mem_verts_of_adj {H C : G.subgraph} (hC : C ∈ H.components)
  {v w : V} (hv : v ∈ C.verts) (hvw : H.adj v w) : w ∈ C.verts :=
begin
  obtain ⟨c, rfl⟩ := hC,
  simp only [mem_mk_component_verts, induce_verts, set.mem_image, set.mem_preimage,
    set.mem_singleton_iff, set_coe.exists,
    subtype.coe_mk, exists_and_distrib_right, exists_eq_right] at hv ⊢,
  obtain ⟨hv, rfl⟩ := hv,
  existsi H.edge_vert hvw.symm,
  simp only [connected_component.eq],
  exact hvw.symm.coe.reachable,
end

lemma components.lift_adj {H C : G.subgraph} (hC : C ∈ H.components)
  {u v : V} (hu : u ∈ C.verts) (hv : v ∈ C.verts)
  (ha : H.adj u v) : C.adj u v :=
begin
  obtain ⟨c, rfl⟩ := hC,
  rw [mem_mk_component_verts] at hu,
  simp [ha, hu],
end

def components.lift_walk {H C : G.subgraph} (hC : C ∈ H.components) :
  Π {u v : V} (hu : u ∈ C.verts) (hv : v ∈ C.verts)
  (p : H.coe.walk ⟨u, (components_le hC).1 hu⟩ ⟨v, (components_le hC).1 hv⟩),
  C.coe.walk ⟨u, hu⟩ ⟨v, hv⟩
| _ _ hu _ walk.nil := walk.nil
| u v hu hv (walk.cons' _ w _ ha p) :=
  have hw : w.1 ∈ C.verts := components.mem_verts_of_adj hC hu ha,
  walk.cons' _ ⟨w, hw⟩ _ (components.lift_adj hC hu hw ha)
    (components.lift_walk _ _ (p.copy (by simp) rfl))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, walk.length x.2.2.2.2)⟩]}

lemma components.lift_reachable {H C : G.subgraph} (hC : C ∈ H.components)
  {u v : V} (hu : u ∈ C.verts) (hv : v ∈ C.verts)
  (hr : H.coe.reachable ⟨u, (components_le hC).1 hu⟩ ⟨v, (components_le hC).1 hv⟩) :
  C.coe.reachable ⟨u, hu⟩ ⟨v, hv⟩ :=
begin
  refine hr.elim (λ p, _),
  exact ⟨components.lift_walk hC hu hv p⟩,
end

lemma components_connected {H C : G.subgraph} (hC : C ∈ H.components) : C.connected :=
begin
  haveI hn : nonempty C.verts,
  { obtain ⟨v, hv⟩ := components_nonempty_verts hC,
    exact ⟨⟨v, hv⟩⟩ },
  split,
  clear hn,
  rintros ⟨a, ha⟩ ⟨b, hb⟩,
  apply components.lift_reachable hC ha hb,
  obtain ⟨c, rfl⟩ := hC,
  simp only [mem_mk_component_verts, induce_verts, set.mem_image, set.mem_preimage,
    set.mem_singleton_iff, set_coe.exists,
    subtype.coe_mk, exists_and_distrib_right, exists_eq_right] at ha hb,
  obtain ⟨hb, rfl⟩ := hb,
  obtain ⟨ha, h⟩ := ha,
  rw [connected_component.eq] at h,
  exact h,
end

lemma components_maximal_aux {H C C' : G.subgraph} (hC : C ∈ H.components)
  (hC' : C' ≤ H)
  (hCC' : C ≤ C') (hc : C'.connected) : C'.verts ⊆ C.verts :=
begin
  intros v hv,
  obtain ⟨w, hw⟩ := components_nonempty_verts hC,
  have hw' := hCC'.1 hw,
  have := hc ⟨v, hv⟩ ⟨w, hw'⟩,
  have hCH := components_le hC,
  obtain ⟨c, h⟩ := hC,
  rw ← h,
  simp only [mem_mk_component_verts, hC'.1 hv, induce_verts, set.mem_image, set.mem_preimage,
    set.mem_singleton_iff,
    set_coe.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right, exists_true_left],
  rw ← h at hw,
  simp only [mem_mk_component_verts, induce_verts, set.mem_image, set.mem_preimage,
    set.mem_singleton_iff, set_coe.exists,
    subtype.coe_mk, exists_and_distrib_right, exists_eq_right] at hw,
  obtain ⟨hw₀, hw''⟩ := hw,
  rw ← hw'',
  rw connected_component.eq,
  refine this.elim (λ p, _),
  have := p.map (inclusion hC'),
  simp only [inclusion, subtype.coe_mk, rel_hom.coe_fn_mk] at this,
  exact ⟨this⟩,
end

lemma components_maximal {H C C' : G.subgraph} (hC : C ∈ H.components)
  (hC' : C' ≤ H)
  (hCC' : C ≤ C') (hc : C'.connected) : C' = C :=
begin
  have key := components_maximal_aux hC hC' hCC' hc,
  refine le_antisymm _ hCC',
  split,
  { exact key },
  { intros v w hvw,
    obtain ⟨c, rfl⟩ := hC,
    simp [H.edge_vert (hC'.2 hvw), H.edge_vert (hC'.2 hvw.symm), hC'.2 hvw],
    have := key (C'.edge_vert hvw),
    simp at this, obtain ⟨h, this⟩ := this, simp [this], },
end

lemma components.le_of_mem_verts {H C C' : G.subgraph}
  (hC : C ∈ H.components) (hC' : C' ∈ H.components)
  {v : V} (h : v ∈ C.verts) (h' : v ∈ C'.verts) : C ≤ C' :=
begin
  obtain ⟨c, rfl⟩ := hC,
  obtain ⟨c', rfl⟩ := hC',
  simp only [mem_mk_component_verts, subgraph.induce_verts, set.mem_preimage,
    set.mem_singleton_iff] at h h',
  obtain ⟨hv, rfl⟩ := h,
  obtain ⟨hv', rfl⟩ := h',
  trivial,
end

lemma components.eq_of_mem_verts {H C C' : G.subgraph}
  (hC : C ∈ H.components) (hC' : C' ∈ H.components)
  {v : V} (h : v ∈ C.verts) (h' : v ∈ C'.verts) : C = C' :=
by apply le_antisymm; apply components.le_of_mem_verts; assumption

lemma components_disjoint {H C C' : G.subgraph}
  (hC : C ∈ H.components) (hC' : C' ∈ H.components)
  (h : C ≠ C') : disjoint C C' :=
begin
  rw [disjoint_iff, subgraph.eq_bot_iff],
  contrapose! h,
  rw [← set.nonempty_iff_ne_empty] at h,
  obtain ⟨v, h, h'⟩ := h,
  apply components.eq_of_mem_verts hC hC' h h',
end

lemma Sup_components (H : G.subgraph) :
  (⨆ (C ∈ H.components), C) = H :=
begin
  ext,
  { simp only [verts_supr, set.mem_Union, exists_prop],
    split,
    { rintro ⟨C, hC, h⟩,
      exact (components_le hC).1 h },
    { intro hx,
      use H.mk_component (H.coe.connected_component_mk ⟨x, hx⟩),
      simp [hx], } },
  { simp only [supr_adj, exists_prop],
    split,
    { rintro ⟨C, hC, ha⟩,
      exact (components_le hC).2 ha },
    { intro h,
      use H.mk_component (H.coe.connected_component_mk ⟨x, H.edge_vert h⟩),
      simp [h, H.edge_vert h], } }
end

end subgraph

section connected
/-! ### Connected components of a graph as subgraphs -/

/-- The set of maximal connected subgraphs. -/
@[reducible] def components : set G.subgraph := (⊤ : G.subgraph).components

lemma components.mem_verts_of_adj {G : simple_graph V} {H} (hH : H ∈ G.components)
  {v w : V} (hv : v ∈ H.verts) (hvw : G.adj v w) : w ∈ H.verts :=
subgraph.components.mem_verts_of_adj hH hv hvw

lemma components_nonempty_verts {H} (hH : H ∈ G.components) :
  H.verts.nonempty :=
subgraph.components_nonempty_verts hH

lemma components_ne_bot {H} (hH : H ∈ G.components) : H ≠ ⊥ :=
subgraph.components_ne_bot hH

lemma components_connected {H} (hH : H ∈ G.components) : H.connected :=
subgraph.components_connected hH

lemma components_maximal {H H'} (hH : H ∈ G.components)
  (hHH' : H ≤ H') (hc : H'.connected) : H' = H :=
subgraph.components_maximal hH le_top hHH' hc

lemma components.eq_of_mem_verts {H H'}
  (hH : H ∈ G.components) (hH' : H' ∈ G.components)
  {v : V} (h : v ∈ H.verts) (h' : v ∈ H'.verts) : H = H' :=
subgraph.components.eq_of_mem_verts hH hH' h h'

lemma components_disjoint {H H'}
  (hH : H ∈ G.components) (hH' : H' ∈ G.components)
  (h : H ≠ H') : disjoint H H' :=
subgraph.components_disjoint hH hH' h

lemma Sup_components : (⨆ (C ∈ G.components), C) = ⊤ :=
subgraph.Sup_components (⊤ : G.subgraph)

end connected


namespace walk
variables {G}

instance {u v : V} (p : G.walk u v) : nonempty p.to_subgraph.verts :=
⟨⟨u, by simp⟩⟩

lemma finite_verts_to_subgraph {u v : V} (p : G.walk u v) :
  p.to_subgraph.verts.finite :=
by { rw [verts_to_subgraph], exact p.support.finite_to_set }

instance fintype_neighbor_set_to_subgraph [decidable_eq V] {u v w : V} (p : G.walk u v) :
  fintype (p.to_subgraph.neighbor_set w) :=
begin
  induction p,
  { convert_to fintype (∅ : set V),
    apply_instance, },
  { simp [subgraph.neighbor_set_sup],
    apply' set.fintype_union,
    apply' set.fintype_subset _ (neighbor_set_subgraph_of_adj_subset p_h),
    simp, apply_instance,
    assumption, },
end

lemma get_vert_mem_support {u v : V} (p : G.walk u v) (i : ℕ) :
  p.get_vert i ∈ p.support :=
by { induction p generalizing i; cases i; simp [get_vert, *] }

lemma get_vert_eq_start_iff_of_nodup_support {u v : V} (p : G.walk u v) (hp : p.support.nodup)
  {i : ℕ} (hi : i ≤ p.length):
  p.get_vert i = u ↔ i = 0 :=
begin
  cases p,
  { simp at hi, subst i, simp },
  { cases i,
    { simp, },
    { simp only [get_vert, nat.succ_ne_zero, iff_false],
      simp only [support_cons, list.nodup_cons] at hp,
      obtain ⟨hp, hp'⟩ := hp,
      contrapose! hp,
      rw ← hp,
      apply get_vert_mem_support, } }
end

@[simp] lemma get_vert_append_add {u v w : V} (p : G.walk u v) (q : G.walk v w) (i : ℕ) :
  (p.append q).get_vert (p.length + i) = q.get_vert i :=
begin
  induction p,
  { simp, },
  { simp only [cons_append, length_cons],
    rw [add_assoc, add_comm 1, ← add_assoc],
    simp [get_vert, p_ih] }
end

lemma get_vert_append_of_le_length {u v w : V} (p : G.walk u v) (q : G.walk v w)
  {i : ℕ} (hi : i ≤ p.length) :
  (p.append q).get_vert i = p.get_vert i :=
begin
  induction p generalizing i q,
  { simp at hi,
    subst i,
    simp, },
  { cases i,
    { simp },
    { simp [get_vert],
      apply p_ih,
      simpa [← nat.add_one] using hi, } }
end

lemma get_vert_reverse {u v : V} (p : G.walk u v) (i : ℕ) :
  p.reverse.get_vert i = p.get_vert (p.length - i) :=
begin
  by_cases hi : i ≤ p.length,
  swap,
  { simp at hi,
    rw tsub_eq_zero_of_le hi.le,
    simp,
    rw [get_vert_of_length_le],
    simp [hi.le], },
  induction p generalizing i,
  { simp [get_vert] },
  { simp at hi,
    obtain (hi' | rfl) := nat.of_le_succ hi,
    { simp,
      have : p_p.length + 1 - i = p_p.length - i + 1 := nat.succ_sub hi',
      rw get_vert_append_of_le_length,
      rw p_ih,
      simp [this, get_vert],
      assumption,
      simpa, },
    { simp [← nat.add_one],
      rw [←length_reverse, get_vert_append_add],
      simp [get_vert] }
  }
end

lemma get_vert_eq_end_iff_of_nodup_support {u v : V} (p : G.walk u v) (hp : p.support.nodup)
  {i : ℕ} (hi : i ≤ p.length) :
  p.get_vert i = v ↔ i = p.length :=
begin
  have := get_vert_eq_start_iff_of_nodup_support p.reverse
    (by simp [hp]) (by simp [hi] : p.length - i ≤ p.reverse.length),
  simp only [get_vert_reverse, tsub_eq_zero_iff_le] at this,
  convert this,
  rwa [nat.sub_sub_self],
  simp [hi],
  split,
  { rintro rfl,
    refl, },
  { intro h,
    apply le_antisymm hi h, }
end

lemma get_vert_inj_of_nodup_support {u v : V} (p : G.walk u v) (hp : p.support.nodup)
  {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) :
  p.get_vert i = p.get_vert j ↔ i = j :=
begin
  induction p generalizing i j,
  { simp at hi hj,
    subst_vars,
    simp, },
  { simp at hp,
    obtain ⟨hp, hp'⟩ := hp,
    simp at hi hj,
    cases i; cases j,
    { simp, },
    { rw @eq_comm _ 0,
      simp [get_vert],
      contrapose! hp,
      rw hp,
      apply get_vert_mem_support, },
    { simp [get_vert],
      contrapose! hp,
      rw ← hp,
      apply get_vert_mem_support, },
    { simp [get_vert],
      simp [← nat.add_one] at hi hj,
      apply p_ih,
      assumption,
      assumption,
      assumption, } },
end

lemma get_vert_inj_of_is_cycle {v : V} (c : G.walk v v) (hc : c.is_cycle)
  {i j : ℕ} (hi : i < c.length) (hj : j < c.length) :
  c.get_vert i = c.get_vert j ↔ i = j :=
begin
  obtain ⟨⟨ht, hn⟩, hc⟩ := hc,
  cases c,
  { exact absurd rfl hn },
  simp at hc,
  cases i; cases j,
  { simp, },
  { simp [@eq_comm _ 0, get_vert],
    simp [← nat.add_one] at hj,
    rw eq_comm,
    rw get_vert_eq_end_iff_of_nodup_support _ hc hj.le,
    exact hj.ne },
  { simp [get_vert],
    simp [← nat.add_one] at hi,
    rw get_vert_eq_end_iff_of_nodup_support _ hc hi.le,
    exact hi.ne },
  { simp [get_vert],
    simp [← nat.add_one] at hi hj,
    apply get_vert_inj_of_nodup_support _ hc hi.le hj.le, },
end

lemma is_cycle.three_le_length {v : V} {c : G.walk v v} (hc : c.is_cycle) :
  3 ≤ c.length :=
begin
  obtain ⟨⟨hc, hc'⟩, hc''⟩ := hc,
  obtain (_|_) := c,
  { simpa using hc', },
  obtain (_|_) := c_p,
  { simpa using c_h, },
  obtain (_|_) := c_p_p,
  { simpa using hc, },
  apply nat.succ_le_succ,
  apply nat.succ_le_succ,
  apply nat.succ_le_succ,
  apply nat.zero_le,
end

lemma exists_eq_append_cons {v w : V} (p : G.walk v w) (h : 0 < p.length) :
  ∃ u (q : G.walk v u) (huw : G.adj u w), p = q.append (cons huw nil) :=
begin
  induction p,
  { simpa using h },
  { cases p_p,
    { refine ⟨_, nil, p_h, _⟩,
      simp, },
    { obtain ⟨u, q, huw, h⟩ := p_ih (by simp),
      refine ⟨_, cons p_h q, huw, _⟩,
      simp [h], } }
end

example (p q : Prop) (h : ¬ p → q) : p ∨ q := or_iff_not_imp_left.mpr h

lemma cases_end {v w : V} (p : G.walk v w) :
  (∃ (h : v = w), p = nil.copy rfl h)
    ∨ ∃ u (q : G.walk v u) (huw : G.adj u w), p = q.append (cons huw nil) :=
begin
  cases p,
  { left, simp, },
  { right,
    apply exists_eq_append_cons,
    simp, },
end

lemma degree_to_subgraph_of_is_cycle' {v : V} (c : G.walk v v) (hc : c.is_cycle)
  [fintype (c.to_subgraph.neighbor_set v)] :
  c.to_subgraph.degree v = 2 :=
begin
  classical,
  have three : 3 ≤ c.length := hc.three_le_length,
  have pos_len := pos_of_gt (nat.lt_of_succ_le three),
  obtain ⟨⟨hc, hc'⟩, hc''⟩ := hc,
  unfreezingI
  { obtain ⟨u, q, huv, rfl⟩ := exists_eq_append_cons c pos_len,
    cases q with _ _ w _ hvw q, },
  { norm_num at three },
  rw [← subgraph.finset_card_neighbor_set_eq_degree],
  convert_to finset.card ({w, u} : set V).to_finset = 2,
  { congr' 1,
    rw set.to_finset_inj,
    have : q.to_subgraph.neighbor_set v = ∅,
    { simp [support_append, list.nodup_append_comm] at hc'',
      ext w,
      simp,
      intro h,
      apply hc''.1,
      simpa using q.to_subgraph.edge_vert h, },
    simp [subgraph.neighbor_set_sup, this],
    exact set.pair_comm u w, },
  { simp,
    rw finset.card_insert_of_not_mem,
    { convert_to 1 + 1 = 2, simp, },
    simp,
    unfreezingI { rintro rfl },
    simp at hc'',
    rw [support_append] at hc'',
    simp at hc'',
    rw [list.nodup_append_comm] at hc'',
    simp at hc'',
    simp at three,
    replace three := nat.le_of_succ_le_succ (nat.le_of_succ_le_succ three),
    unfreezingI { cases q with _ _ a _ hwa q },
    { simpa using three },
    simpa using hc'', }
end

/-lemma degree_to_subgraph_of_is_cycle' [decidable_eq V] {v : V} (c : G.walk v v) (hc : c.is_cycle) :
  c.to_subgraph.degree v = 2 :=
begin
  classical,
  rw [← subgraph.finset_card_neighbor_set_eq_degree],
  convert_to finset.card {c.get_vert 1, c.get_vert (c.length - 1)} = _,
  swap,
  { rw finset.card_eq_two,
    refine ⟨c.get_vert 1, c.get_vert (c.length - 1), _, rfl⟩,
    have three : 3 ≤ c.length := hc.three_le_length,
    intro h,
    have := pos_of_gt (nat.lt_of_succ_le three),
    rw get_vert_inj_of_is_cycle c hc at h,
    { have : c.length = 1 + 1,
      { nth_rewrite 0 h, rw [nat.sub_add_cancel], exact this, },
      rw this at three,
      norm_num at three, },
    { apply nat.le_of_succ_le,
      exact three, },
    { exact nat.sub_lt this (nat.succ_pos 0), }, },
  congr' 1,
  ext u,
  simp,
  cases c, { simpa using hc, },
  simp [get_vert],
end-/

lemma degree_to_subgraph_of_is_cycle {v w : V} (c : G.walk v v) (hc : c.is_cycle)
  (hw : w ∈ c.support)
  [fintype (c.to_subgraph.neighbor_set w)] :
  c.to_subgraph.degree w = 2 :=
begin
  classical,
  haveI : fintype ((c.rotate hw).to_subgraph.neighbor_set w) := by simpa,
  convert_to (c.rotate hw).to_subgraph.degree w = 2,
  { congr' 1,
    rw c.to_subgraph_rotate hw,
    have : c.to_subgraph.neighbor_set w = (c.rotate hw).to_subgraph.neighbor_set w := by simp,
    apply subsingleton.helim (congr_arg fintype (congr_arg coe_sort this)), },
  apply degree_to_subgraph_of_is_cycle',
  apply hc.rotate,
end

end walk

namespace subgraph
variables {G}

lemma degree_eq_zero_iff {H : G.subgraph} (v : V) [fintype (H.neighbor_set v)] :
  H.degree v = 0 ↔ H.neighbor_set v = ∅ :=
begin
  simp [←finset_card_neighbor_set_eq_degree, -set.to_finset_card],
end

lemma degree_eq_one_iff {H : G.subgraph} (v : V) [fintype (H.neighbor_set v)] :
  H.degree v = 1 ↔ ∃ w, H.neighbor_set v = {w} :=
begin
  simp [←finset_card_neighbor_set_eq_degree, -set.to_finset_card],
  rw finset.card_eq_one,
  simp [← set.to_finset_singleton],
end

lemma degree_eq_two_iff {H : G.subgraph} (u : V) [fintype (H.neighbor_set u)] :
  H.degree u = 2 ↔ ∃ v w, v ≠ w ∧ H.neighbor_set u = {v, w} :=
begin
  classical,
  simp [←finset_card_neighbor_set_eq_degree, -set.to_finset_card],
  rw finset.card_eq_two,
  simp [← set.to_finset_singleton, ← set.to_finset_insert],
end

/-- A subgraph is a path if there exists a path representing it. -/
protected def is_path (H : G.subgraph) : Prop :=
∃ u v (p : G.walk u v), p.is_path ∧ H = p.to_subgraph

/-- Vertices of `H` that have at most one neighbor. -/
def leaves (H : G.subgraph) : set V :=
{v : V | v ∈ H.verts ∧ (H.neighbor_set v).subsingleton}

lemma _root_.simple_graph.walk.is_path.to_subgraph {u v : V} {p : G.walk u v} (hp : p.is_path) :
  p.to_subgraph.is_path :=
⟨u, v, p, hp, rfl⟩

lemma _root_.simple_graph.walk.to_subgraph_mem_of_adj {u v : V} (p : G.walk u v) {x y : V}
  (h : p.to_subgraph.adj x y) : x ∈ p.support :=
begin
  rw [← walk.mem_verts_to_subgraph],
  exact h.fst_mem,
end

lemma _root_.simple_graph.walk.is_path.degree_to_subgraph_start_le [decidable_eq V]
  {u v : V} {p : G.walk u v} (hp : p.is_path) :
  p.to_subgraph.degree u ≤ 1 :=
begin
  cases p,
  { suffices : walk.nil.to_subgraph.degree u = 0,
    { rw this, simp },
    rw subgraph.degree_eq_zero_iff,
    simp, },
  { suffices : (walk.cons p_h p_p).to_subgraph.degree u = 1,
    { rw this },
    rw subgraph.degree_eq_one_iff,
    existsi p_v,
    ext x,
    simp,
    intro h,
    exfalso,
    simp at hp,
    apply hp.2,
    apply walk.to_subgraph_mem_of_adj _ h, },
end

lemma _root_.simple_graph.walk.is_path.degree_to_subgraph_end_le [decidable_eq V]
  {u v : V} {p : G.walk u v} (hp : p.is_path) :
  p.to_subgraph.degree v ≤ 1 :=
by simpa [←finset_card_neighbor_set_eq_degree, ← nat.card_eq_fintype_card] -- hack...
  using hp.reverse.degree_to_subgraph_start_le

lemma neighbor_set_eq_empty_of_not_mem (H : G.subgraph) {v : V} (hv : ¬ v ∈ H.verts) :
  H.neighbor_set v = ∅ :=
begin
  ext w,
  simp,
  contrapose! hv,
  exact hv.edge_vert
end

lemma _root_.set.subsingleton_union_left {α : Type*} {s t : set α} (h : (s ∪ t).subsingleton) :
  s.subsingleton :=
begin
  intros x hx y hy,
  apply h,
  exact set.mem_union_left t hx,
  exact set.mem_union_left t hy,
end

lemma _root_.set.subsingleton_union_right {α : Type*} {s t : set α} (h : (s ∪ t).subsingleton) :
  t.subsingleton :=
begin
  rw set.union_comm at h,
  exact set.subsingleton_union_left h
end

lemma _root_.simple_graph.walk.is_path.leaves_eq {u v : V} {p : G.walk u v} (hp : p.is_path) :
  p.to_subgraph.leaves = {u, v} :=
begin
  ext x,
  simp [leaves],
  split,
  { rintro ⟨hx, h⟩,
    induction p,
    { simp at hx,
      exact or.inl hx, },
    { simp at hp,
      specialize p_ih hp.1,
      simp at hx,
      obtain (rfl|hx) := hx,
      { exact or.inl rfl },
      simp [neighbor_set_sup] at h,
      obtain (rfl|rfl) := p_ih hx (set.subsingleton_union_right h),
      { cases p_p,
        { exact or.inr rfl },
        exfalso,
        classical,
        simp [neighbor_set_sup, neighbor_set_subgraph_of_adj] at h,
        simp [p_h.symm.ne, p_p_h.ne] at h,
        specialize @h p_u (by simp) p_p_v (by simp),
        subst h,
        simpa [not_or_distrib] using hp, },
      { exact or.inr rfl } } },
  { rintro (rfl|rfl),
    { cases p,
      { simp, },
      { simp [neighbor_set_sup],
        simp at hp,
        have : p_p.to_subgraph.neighbor_set x = ∅,
        { ext y,
          simp,
          intro h,
          apply hp.2,
          simpa using h.edge_vert, },
        simp [this], } },
    { obtain (⟨rfl, rfl⟩|⟨c,q,hc,rfl,rfl⟩) := p.cases_end,
      { simp, },
      { simp [neighbor_set_sup],
        rw [← walk.is_path_reverse_iff] at hp,
        simp at hp,
        have : q.to_subgraph.neighbor_set x = ∅,
        { ext y,
          simp,
          intro h,
          apply hp.2,
          simpa using h.edge_vert, },
        simp [this] } } }
end

lemma _root_.simple_graph.walk.is_path.of_to_subgraph_eq' {u v v' : V}
  {p : G.walk u v} {p' : G.walk u v'} (hp : p.is_path) (hp' : p'.is_path)
  (h : p.to_subgraph = p'.to_subgraph) :
  ∃ (hv : v = v'), p.copy rfl hv = p' :=
begin
  induction p with _ a b c hab pbc ih generalizing p',
  { cases p',
    { simp },
    { apply_fun subgraph.edge_set at h,
      simp at h,
      rw [eq_comm, ← set.not_nonempty_iff_eq_empty ] at h,
      exfalso, simpa using h } },
  { cases p' with _ d e _ hde p'ev',
    { apply_fun subgraph.edge_set at h,
      simp at h,
      rw [← set.not_nonempty_iff_eq_empty] at h,
      exfalso, simpa using h },
    { obtain (rfl|hnbe) := eq_or_ne b e,
      { simp at hp,
        simp at hp',
        suffices he : pbc.to_subgraph = p'ev'.to_subgraph,
        { obtain ⟨rfl, rfl⟩ := ih hp.1 hp'.1 he,
          exact ⟨rfl, rfl⟩ },
        simp at h,
        ext,
        { simp,
          apply_fun (λ H, x ∈ H.verts) at h,
          simp at h,
          split,
          { intro h',
            obtain ((rfl|rfl)|h) := h.mp (or.inr h'),
            { exact absurd h' hp.2 },
            { apply simple_graph.walk.start_mem_support },
            { exact h } },
          { intro h',
            obtain ((rfl|rfl)|h) := h.mpr (or.inr h'),
            { exact absurd h' hp'.2 },
            { apply simple_graph.walk.start_mem_support },
            { exact h } } },
        { apply_fun (λ H, H.adj x x_1) at h,
          simp at h,
          split,
          { intro h',
            obtain ((⟨rfl,rfl⟩|⟨rfl,rfl⟩)|h) := h.mp (or.inr h'),
            { exfalso, apply hp.2, simpa using h'.edge_vert },
            { exfalso, apply hp.2, simpa using h'.symm.edge_vert },
            { exact h } },
          { intro h',
            obtain ((⟨rfl,rfl⟩|⟨rfl,rfl⟩)|h) := h.mpr (or.inr h'),
            { exfalso, apply hp'.2, simpa using h'.edge_vert },
            { exfalso, apply hp'.2, simpa using h'.symm.edge_vert },
            { exact h } } } },
      { exfalso,
        apply_fun (λ H, H.adj a e) at h,
        simp [hnbe] at h,
        obtain (⟨rfl,rfl⟩|h) := h,
        { exact hab.ne rfl },
        { simp at hp,
          apply hp.2, simpa using h.edge_vert } } } }
end

lemma _root_.simple_graph.walk.is_path.to_subgraph_eq_iff {u v u' v' : V}
  {p : G.walk u v} {p' : G.walk u' v'} (hp : p.is_path) (hp' : p'.is_path) :
  p.to_subgraph = p'.to_subgraph ↔
  (∃ (hu : u = u') (hv : v = v'), p.copy hu hv = p')
    ∨ (∃ (hu : u = v') (hv : v = u'), p.reverse.copy hv hu = p') :=
begin
  split,
  { intro h,
    obtain (rfl|hn) := eq_or_ne u u',
    { left,
      existsi rfl,
      exact hp.of_to_subgraph_eq' hp' h, },
    { obtain (rfl|hn') := eq_or_ne u v',
      { right,
        existsi rfl,
        obtain ⟨rfl, rfl⟩ := hp'.reverse.of_to_subgraph_eq' hp (by simpa using h.symm),
        simp, },
      { exfalso,
        have := hp.leaves_eq,
        rw [h, hp'.leaves_eq] at this,
        apply_fun (λ s, u ∈ s) at this,
        simpa [hn, hn'] using this, } } },
  { rintro (⟨rfl, rfl, rfl⟩|⟨rfl, rfl, rfl⟩);
      simp only [walk.copy_rfl_rfl, walk.to_subgraph_reverse], }
end

lemma _root_.simple_graph.walk.is_path.degree_to_subgraph_le [decidable_eq V]
  {u v w : V} {p : G.walk u v} (hp : p.is_path) :
  p.to_subgraph.degree w ≤ 2 :=
begin -- a brute-force proof...
  induction p with _ a b c hab p ih,
  { simp [←finset_card_neighbor_set_eq_degree, ← nat.card_eq_fintype_card], },
  { simp at hp,
    specialize ih hp.1,
    cases p with _ d e f hde p,
    { simp [←finset_card_neighbor_set_eq_degree, ← nat.card_eq_fintype_card, neighbor_set_sup],
      simp [neighbor_set_subgraph_of_adj],
      split_ifs; subst_vars; simp, },
    { simp [←finset_card_neighbor_set_eq_degree, ← nat.card_eq_fintype_card, neighbor_set_sup,
        neighbor_set_subgraph_of_adj],
      simp [←finset_card_neighbor_set_eq_degree, ← nat.card_eq_fintype_card, neighbor_set_sup,
        neighbor_set_subgraph_of_adj] at ih,
      split_ifs; subst_vars,
      { exfalso, exact G.loopless _ hde },
      { exfalso, exact G.loopless _ hab },
      { simpa [h_1] using ih, },
      { rw neighbor_set_eq_empty_of_not_mem,
        { simp, },
        simp [not_or_distrib] at hp,
        simpa using hp.2.2, },
      { exfalso, exact G.loopless _ hde },
      { rw neighbor_set_eq_empty_of_not_mem,
        { simp only [set.union_empty, set.empty_union, set.singleton_union],
          simp only [nat.card_eq_fintype_card, fintype.card_of_finset],
          apply finset.card_insert_le, },
        simp [not_or_distrib] at hp,
        simpa using hp.1.2, },
      { simpa [h_1] using ih, },
      { simpa [h_1, h_2] using ih, } } }
end

@[simp] lemma singleton_subgraph_is_path {v : V} : (G.singleton_subgraph v).is_path :=
begin
  existsi [v, v, walk.nil],
  simp,
end

@[simp] lemma subgraph_of_adj_is_path {u v : V} (huv : G.adj u v) :
  (G.subgraph_of_adj huv).is_path :=
begin
  existsi [u, v, walk.cons huv walk.nil],
  simp [huv.ne],
end

lemma is_path.degree_le (H : G.subgraph) (hH : H.is_path) (u : V) [fintype (H.neighbor_set u)] :
  H.degree u ≤ 2 :=
begin
  classical,
  unfreezingI { obtain ⟨v, w, p, hp, rfl⟩ := hH },
  convert hp.degree_to_subgraph_le,
end

@[simp] lemma _root_.simple_graph.walk.to_subgraph_connected {u v : V} (p : G.walk u v) :
  p.to_subgraph.connected :=
begin
  induction p,
  { simp [singleton_subgraph_connected], },
  { rw [walk.to_subgraph],
    apply sup_connected _ _ p_v; simp [p_ih], }
end

lemma is_path.connected {H : G.subgraph} (hH : H.is_path) : H.connected :=
begin
  obtain ⟨v, w, p, hp, rfl⟩ := hH,
  simp,
end

@[simp] lemma _root_.set.to_finset_eq_singleton_iff {α : Type*} (s : set α) [fintype s] (v : α) :
  s.to_finset = {v} ↔ s = {v} :=
begin
  split,
  { intro h,
    ext x,
    apply_fun (λ t, x ∈ t) at h,
    simpa using h, },
  { intro h,
    ext x,
    simp [h], }
end

lemma is_path_iff (H : G.subgraph) [∀ v, fintype (H.neighbor_set v)] :
  H.is_path ↔ H.verts.finite ∧ H.connected ∧ (∃ v, H.degree v ≤ 1) ∧ ∀ v, H.degree v ≤ 2 :=
begin
  classical,
  split,
  { rintro hp,
    unfreezingI { obtain ⟨v, w, p, hp, rfl⟩ := hp },
    refine ⟨walk.finite_verts_to_subgraph p, p.to_subgraph_connected, _⟩,
    split,
    { existsi v,
      convert hp.degree_to_subgraph_start_le, },
    { intro v,
      apply is_path.degree_le,
      exact hp.to_subgraph, } },
  { rintro ⟨hi, hc, hone, htwo⟩,
    unfreezingI { induction hn : nat.card H.verts generalizing H },
    { haveI : fintype H.verts := set.finite.fintype hi,
      simp only [nat.card_eq_fintype_card, set.to_finset_eq_empty, nat.nat_zero_eq_zero,
        finset.card_eq_zero, ← set.to_finset_card] at hn,
      cases hc, rw hn at hc_nonempty, simpa using hc_nonempty, },
    { haveI : fintype H.verts := set.finite.fintype hi,
      obtain ⟨v, hv⟩ := hone,
      cases n,
      { simp [nat.card_eq_fintype_card, ← set.to_finset_card, finset.card_eq_one, verts_singleton_iff_eq] at hn,
        obtain ⟨a, ha⟩ := hn,
        rw ha,
        apply singleton_subgraph_is_path, },
      -- other case: v has a neighbor
      haveI : Π (w : V), fintype ↥((H.delete_verts {v}).neighbor_set w),
      { intro w,
        apply set.fintype_subset (H.neighbor_set w),
        intro x,
        simp,
        apply_instance },
      specialize ih (H.delete_verts {v}) _ _,
      { apply hi.subset,
        intro x,
        simp { contextual := tt } },
      { sorry

      },
      sorry
    },
  },
end

/-- A subgraph is a cycle if there exists a cyclic walk representing it. -/
protected def is_cycle (H : G.subgraph) : Prop :=
∃ u (c : G.walk u u), c.is_cycle ∧ H = c.to_subgraph

lemma is_cycle.degree_eq {H : G.subgraph} (Hc : H.is_cycle)
  {v : V} [fintype (H.neighbor_set v)] (hv : v ∈ H.verts) :
  H.degree v = 2 :=
begin
  classical,
  unfreezingI { obtain ⟨u, c, hc, rfl⟩ := Hc },
  apply walk.degree_to_subgraph_of_is_cycle,
  assumption,
  simpa using hv,
end

lemma is_cycle_iff (H : G.subgraph) [fintype H.verts] [decidable_rel H.adj] (hc : H.connected) :
  H.is_cycle ↔ ∀ v, v ∈ H.verts → H.degree v = 2 :=
begin
  classical,
  refine ⟨λ h v hv, h.degree_eq hv, _⟩,
  intro h,
  simp [subgraph.degree_eq_two_iff] at h,
  obtain ⟨⟨v, hv⟩⟩ := hc.nonempty,
  obtain ⟨a, b, hnab, hve⟩ := h v hv,
  --simp_rw [← finset_card_neighbor_set_eq_degree, finset.card_eq_two] at h,
  sorry -- need to construct cycle
end

namespace is_perfect_matching
variables {G} {M : G.subgraph} (m : M.is_perfect_matching)

protected def other (v : V) : V :=
(M.is_perfect_matching_iff.mp m v).some

lemma other_spec (v : V) : M.adj v (m.other v) :=
(M.is_perfect_matching_iff.mp m v).some_spec.1

lemma other_eq_of_adj {v w : V} (ha : M.adj v w) : m.other v = w :=
((M.is_perfect_matching_iff.mp m v).some_spec.2 w ha).symm

lemma other_involutive : function.involutive m.other :=
λ v, m.other_eq_of_adj (m.other_spec v).symm

@[simp] lemma other_other (v : V) : m.other (m.other v) = v :=
m.other_involutive v

end is_perfect_matching

end subgraph

/-
namespace walk
variables {G}

/-- A path that alternates between edges of the two given subgraphs.
The path can have vertices outside the subgraphs. -/
def alternating : G.subgraph → G.subgraph → Π {u v : V}, G.walk u v → Prop
| M M' u _ nil := true
| M M' _ _ (cons' u v _ _ p) := M.adj u v ∧ alternating M' M p

def extendable

variables {M M' : G.subgraph}

variables (hd : disjoint M.edge_set M'.edge_set)
  (m : M.is_perfect_matching) (m' : M'.is_perfect_matching)

lemma mk_walk {u v : V} (p q : G.walk u v)

#check is_cycle

end walk
-/

end simple_graph

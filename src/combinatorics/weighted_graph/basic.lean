/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.simple_graph.basic

/-!
# Weighted graphs

This file defines weighted adirected graphs.
-/

variables {ι α β W W' : Type*} {σ : ι → Type*}

section ite
variables {p q : Prop} [decidable p] {a b : α}

lemma imp_iff_not {a b : Prop} (hb : ¬ b) : a → b ↔ ¬ a := imp_congr_right $ λ _, iff_false_intro hb

@[simp] lemma ite_ne_left_iff : ite p a b ≠ a ↔ ¬ p ∧ a ≠ b :=
by { convert not_congr ite_eq_left_iff, rw [ne_comm, not_imp] }

@[simp] lemma ite_ne_right_iff : ite p a b ≠ b ↔ p ∧ a ≠ b :=
by { convert not_congr ite_eq_right_iff, rw not_imp }

protected lemma ne.ite_ne_left_iff (h : a ≠ b) : ite p a b ≠ a ↔ ¬ p :=
ite_ne_left_iff.trans $ and_iff_left h

protected lemma ne.ite_ne_right_iff (h : a ≠ b) : ite p a b ≠ b ↔ p :=
ite_ne_right_iff.trans $ and_iff_left h

end ite

namespace option
variables {o : option α} {a : α}

lemma ne_none_of_mem (h : a ∈ o) : o ≠ none :=
begin
  rintro rfl,
  exact not_mem_none _ h,
end

alias ne_none_of_mem ← has_mem.mem.ne_none

end option

/-- `W`-weighted graphs on `α`. `weight a b = some w` represents an edge between `a, b : α` of
weight `w : W`. `weight a b = none` represents no edge between `a` and `b`. -/
@[ext] structure weighted_graph (α : Type*) (W : Type*) :=
(weight : α → α → option W)
(weight_self (a : α) : weight a a = none)
(weight_comm (a b : α) : weight a b = weight b a)

namespace weighted_graph
variables (G : weighted_graph α W) (a b : α)

/-- Two vertices of a weighted graph are adjacent if their weight is not `none`. -/
def adj : Prop := G.weight a b ≠ none

lemma adj_comm {a b : α} : G.adj a b ↔ G.adj b a := by { unfold adj, rw G.weight_comm }
lemma adj_symm {a b : α} (h : G.adj a b) : G.adj b a := G.adj_comm.1 h

lemma adj_irrefl : ¬ G.adj a a := λ h, h $ G.weight_self a

instance : decidable_rel G.adj := λ a b, @not.decidable _ option.decidable_eq_none

/-- Turns a weighted graph into a simple graph by forgetting the weights. -/
def to_simple_graph (G : weighted_graph α W) : simple_graph α :=
{ adj := G.adj,
  symm := λ a b, G.adj_symm,
  loopless := G.adj_irrefl }

instance to_simple_graph.adj.decidable_rel (G : weighted_graph α W) :
  decidable_rel G.to_simple_graph.adj :=
adj.decidable_rel G

/-- Weights a simple graph. -/
def _root_.simple_graph.to_weighted_graph (G : simple_graph α) [decidable_rel G.adj]
  (f : sym2 α → W) :
  weighted_graph α W :=
{ weight := λ a b, if G.adj a b then f ⟦(a, b)⟧ else none,
  weight_self := λ a, if_neg (G.loopless a),
  weight_comm := λ a b, by { simp_rw G.adj_comm a b, congr' 3, rw sym2.eq_swap } }

lemma _root_.simple_graph.to_weighted_graph_to_simple_graph (G : simple_graph α)
  [decidable_rel G.adj] (f : sym2 α → W) :
  (G.to_weighted_graph f).to_simple_graph = G :=
by { ext a b, exact (option.some_ne_none _).ite_ne_right_iff }

section constructions

/-- The disjoint sum of two weighted graphs. -/
protected def sum (G : weighted_graph α W) (H : weighted_graph β W) : weighted_graph (α ⊕ β) W :=
{ weight := λ a b, a.elim (λ a', b.elim (G.weight a') $ λ b', none)
                          (λ a', b.elim (λ b', none) $ λ b', H.weight a' b'),
  weight_self := begin
    rintro (a | a),
    { exact G.weight_self a },
    { exact H.weight_self a }
  end,
  weight_comm := begin
    rintro (a | a) (b | b),
    { exact G.weight_comm a b },
    { refl },
    { refl },
    { exact H.weight_comm a b }
  end }

/-- The disjoint sum of weighted graphs. -/
protected def sigma [decidable_eq ι] (G : Π i, weighted_graph (σ i) W) :
  weighted_graph (Σ i, σ i) W :=
{ weight := λ a b, if h : a.1 = b.1 then ((G a.1).weight a.2 $ (congr_arg _ h).mpr b.2) else none,
  weight_self := λ a, (dif_pos rfl).trans ((G a.1).weight_self _),
  weight_comm := λ a b, begin
    split_ifs with h h' h' h',
    sorry,
    { exact (h' h.symm).elim },
    { exact (h h'.symm).elim },
    { refl }
  end }

/-- The product of two weighted graphs. -/
protected def prod (G : weighted_graph α W) (H : weighted_graph β W') :
  weighted_graph (α × β) (W × W') :=
{ weight := λ a b, (G.weight a.1 b.1).elim none (λ w, (H.weight a.2 b.2).elim none $ λ w', (w, w')),
  weight_self := λ a, by { rw G.weight_self, refl },
  weight_comm := λ a b, by rw [G.weight_comm, H.weight_comm] }

open_locale classical

/-- The product of weighted graphs. -/
protected noncomputable def pi [nonempty ι] {W : ι → Type*} (G : Π i, weighted_graph (σ i) (W i)) :
  weighted_graph (Π i, σ i) (Π i, W i) :=
{ weight := λ a b, begin
    refine if h : (∀ i, (G i).weight (a i) (b i) ≠ none) then
      (some $ λ i, ((G i).weight (a i) (b i)).elim _ id) else none,
    sorry
  end,
  weight_self := λ a, dif_neg (λ h, h (classical.arbitrary ι) ((G _).weight_self _)),
  weight_comm := λ a b, begin
    split_ifs with h h' h' h',
    { ext i,
      rw (G i).weight_comm },
    { exact h' (λ i, λ H, h i $ ((G i).weight_comm _ _).trans H) },
    { exact h (λ i, λ H, h' i $ ((G i).weight_comm _ _).trans H) },
    { refl }
  end }

end constructions

section order
variables (α W) {G₁ G₂ : weighted_graph α W}

/-- `G₁ ≤ G₂` means that the edges of `G₁` are edges of `G₂` and have the same weight. -/
instance : has_le (weighted_graph α W) :=
⟨λ G₁ G₂, ∀ ⦃a b⦄, G₁.adj a b → G₁.weight a b = G₂.weight a b⟩

variables {α W} {a b}

lemma le_def : G₁ ≤ G₂ ↔ ∀ ⦃a b⦄, G₁.adj a b → G₁.weight a b = G₂.weight a b := iff.rfl

lemma adj_mono (h : G₁ ≤ G₂) (hab : G₁.adj a b) : G₂.adj a b := λ h', hab $ (h hab).trans h'

variables (α W) [decidable_eq W]

/-- The infimum `G₁ ⊓ G₂`of two weighted graphs has the edges which have the same weight in `G₁` and
`G₂`. -/
instance : has_inf (weighted_graph α W) :=
⟨λ G₁ G₂,
  { weight := λ a b, if G₁.weight a b = G₂.weight a b then G₁.weight a b else none,
    weight_self := λ a, by rw [G₁.weight_self, if_t_t],
    weight_comm := λ a b, by { simp_rw weight_comm _ a, congr } }⟩

@[simp] lemma inf_adj_iff (G₁ G₂ : weighted_graph α W) {a b : α} :
  (G₁ ⊓ G₂).adj a b ↔ G₁.weight a b = G₂.weight a b ∧ G₁.adj a b ∧ G₂.adj a b :=
ite_ne_right_iff.trans $ and_congr_right $ λ h, (and_iff_left_of_imp $ by { rw h, exact id }).symm

/-- The difference of two graphs `x / y` has the edges of `x` with the edges of `y` removed. -/
instance : has_sdiff (weighted_graph α W) := ⟨λ x y,
  { adj := x.adj \ y.adj,
    symm := λ a b h, by change x.adj w v ∧ ¬ y.adj w v; rwa [x.adj_comm, y.adj_comm] }⟩

@[simp] lemma sdiff_adj (x y : weighted_graph α W) (a b : α) :
  (x \ y).adj a b ↔ (x.adj a b ∧ ¬ y.adj a b) := iff.rfl

instance : partial_order (weighted_graph α W) :=
{ le_refl := λ G a b _, rfl,
  le_trans := λ G₁ G₂ G₃ h₁₂ h₂₃ a b h, (h₁₂ h).trans $ h₂₃ $ adj_mono h₁₂ h,
  le_antisymm := λ G₁ G₂ h₁ h₂, begin
    ext a b o,
    exact ⟨λ h, by rwa ←h₁ h.ne_none, λ h, by rwa ←h₂ h.ne_none⟩,
  end,
  .. weighted_graph.has_le α W }

#exit

instance : boolean_algebra (weighted_graph α W) :=
{ le := (≤),
  sup := (⊔),
  inf := (⊓),
  compl := has_compl.compl,
  sdiff := (\),
  top := complete_graph V,
  bot := empty_graph V,
  le_top := λ x a b h, x.ne_of_adj h,
  bot_le := λ x a b h, h.elim,
  sup_le := λ x y z hxy hyz a b h, h.cases_on (λ h, hxy h) (λ h, hyz h),
  sdiff_eq := λ x y, by { ext a b, refine ⟨λ h, ⟨h.1, ⟨_, h.2⟩⟩, λ h, ⟨h.1, h.2.2⟩⟩,
                          rintro rfl, exact x.irrefl h.1 },
  sup_inf_sdiff := λ a b, by { ext a b, refine ⟨λ h, _, λ h', _⟩,
                               obtain ⟨ha, _⟩|⟨ha, _⟩ := h; exact ha,
                               by_cases b.adj a b; exact or.inl ⟨h', h⟩ <|> exact or.inr ⟨h', h⟩ },
  inf_inf_sdiff := λ a b, by { ext a b, exact ⟨λ ⟨⟨_, hb⟩,⟨_, hb'⟩⟩, hb' hb, λ h, h.elim⟩ },
  le_sup_left := λ x y a b h, or.inl h,
  le_sup_right := λ x y a b h, or.inr h,
  le_inf := λ x y z hxy hyz a b h, ⟨hxy h, hyz h⟩,
  le_sup_inf := λ a b c a b h, or.dcases_on h.2 or.inl $
    or.dcases_on h.1 (λ h _, or.inl h) $ λ hb hc, or.inr ⟨hb, hc⟩,
  inf_compl_le_bot := λ a a b h, false.elim $ h.2.2 h.1,
  top_le_sup_compl := λ a a b ne, by { by_cases a.adj a b, exact or.inl h, exact or.inr ⟨ne, h⟩ },
  inf_le_left := λ x y a b h, h.1,
  inf_le_right := λ x y a b h, h.2,
  .. partial_order.lift adj ext }

end order

/-- `G.support` is the set of vertices that form edges in `G`. -/
def support : set V := rel.dom G.adj

lemma mem_support {v : α} : v ∈ G.support ↔ ∃ w, G.adj a b := iff.rfl

lemma support_mono {G G' : weighted_graph α W} (h : G ≤ G') : G.support ⊆ G'.support :=
rel.dom_mono h

/-- `G.neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def neighbor_set (v : α) : set V := set_of (G.adj v)

instance neighbor_set.mem_decidable (v : α) [decidable_rel G.adj] :
  decidable_pred (∈ G.neighbor_set v) := by { unfold neighbor_set, apply_instance }

/--
The edges of G consist of the unordered pairs of vertices related by
`G.adj`.

The way `edge_set` is defined is such that `mem_edge_set` is proved by `refl`.
(That is, `⟦(v, w)⟧ ∈ G.edge_set` is definitionally equal to `G.adj a b`.)
-/
def edge_set : set (sym2 V) := sym2.from_rel G.symm

/--
The `incidence_set` is the set of edges incident to a given vertex.
-/
def incidence_set (v : α) : set (sym2 V) := {e ∈ G.edge_set | v ∈ e}

lemma incidence_set_subset (v : α) : G.incidence_set v ⊆ G.edge_set :=
λ _ h, h.1

@[simp]
lemma mem_edge_set {a b : α} : ⟦(v, w)⟧ ∈ G.edge_set ↔ G.adj a b :=
iff.rfl

/--
Two vertices are adjacent iff there is an edge between them.  The
condition `v ≠ w` ensures they are different endpoints of the edge,
which is necessary since when `v = w` the existential
`∃ (e ∈ G.edge_set), v ∈ e ∧ w ∈ e` is satisfied by every edge
incident to `v`.
-/
lemma adj_iff_exists_edge {a b : α} :
  G.adj a b ↔ v ≠ w ∧ ∃ (e ∈ G.edge_set), v ∈ e ∧ w ∈ e :=
begin
  refine ⟨λ _, ⟨G.ne_of_adj ‹_›, ⟦(v,w)⟧, _⟩, _⟩,
  { simpa },
  { rintro ⟨hne, e, he, hv⟩,
    rw sym2.elems_iff_eq hne at hv,
    subst e,
    rwa mem_edge_set at he }
end

lemma edge_other_ne {e : sym2 V} (he : e ∈ G.edge_set) {v : α} (h : v ∈ e) : h.other ≠ v :=
begin
  erw [← sym2.mem_other_spec h, sym2.eq_swap] at he,
  exact G.ne_of_adj he,
end

instance decidable_mem_edge_set [decidable_rel G.adj] :
  decidable_pred (∈ G.edge_set) := sym2.from_rel.decidable_pred _

instance edges_fintype [decidable_eq V] [fintype V] [decidable_rel G.adj] :
  fintype G.edge_set := subtype.fintype _

instance decidable_mem_incidence_set [decidable_eq V] [decidable_rel G.adj] (v : α) :
  decidable_pred (∈ G.incidence_set v) := λ e, and.decidable

/--
The `edge_set` of the graph as a `finset`.
-/
def edge_finset [decidable_eq V] [fintype V] [decidable_rel G.adj] : finset (sym2 V) :=
set.to_finset G.edge_set

@[simp] lemma mem_edge_finset [decidable_eq V] [fintype V] [decidable_rel G.adj] (e : sym2 V) :
  e ∈ G.edge_finset ↔ e ∈ G.edge_set :=
set.mem_to_finset

@[simp] lemma edge_set_univ_card [decidable_eq V] [fintype V] [decidable_rel G.adj] :
  (univ : finset G.edge_set).card = G.edge_finset.card :=
fintype.card_of_subtype G.edge_finset (mem_edge_finset _)

@[simp] lemma mem_neighbor_set (a b : α) : w ∈ G.neighbor_set v ↔ G.adj a b :=
iff.rfl

@[simp] lemma mem_incidence_set (a b : α) : ⟦(v, w)⟧ ∈ G.incidence_set v ↔ G.adj a b :=
by simp [incidence_set]

lemma mem_incidence_iff_neighbor {a b : α} : ⟦(v, w)⟧ ∈ G.incidence_set v ↔ w ∈ G.neighbor_set v :=
by simp only [mem_incidence_set, mem_neighbor_set]

lemma adj_incidence_set_inter {v : α} {e : sym2 V} (he : e ∈ G.edge_set) (h : v ∈ e) :
  G.incidence_set v ∩ G.incidence_set h.other = {e} :=
begin
  ext e',
  simp only [incidence_set, set.mem_sep_eq, set.mem_inter_eq, set.mem_singleton_iff],
  split,
  { intro h', rw ←sym2.mem_other_spec h,
    exact (sym2.elems_iff_eq (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩, },
  { rintro rfl, use [he, h, he], apply sym2.mem_other_mem, },
end

lemma compl_neighbor_set_disjoint (G : weighted_graph α W) (v : α) :
  disjoint (G.neighbor_set v) (Gᶜ.neighbor_set v) :=
begin
  rw set.disjoint_iff,
  rintro w ⟨h, h'⟩,
  rw [mem_neighbor_set, compl_adj] at h',
  exact h'.2 h,
end

lemma neighbor_set_union_compl_neighbor_set_eq (G : weighted_graph α W) (v : α) :
  G.neighbor_set v ∪ Gᶜ.neighbor_set v = {v}ᶜ :=
begin
  ext w,
  have h := @ne_of_adj _ G,
  simp_rw [set.mem_union, mem_neighbor_set, compl_adj, set.mem_compl_eq, set.mem_singleton_iff],
  tauto,
end

/--
The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`.
-/
def common_neighbors (a b : α) : set V := G.neighbor_set v ∩ G.neighbor_set w

lemma common_neighbors_eq (a b : α) :
  G.common_neighbors a b = G.neighbor_set v ∩ G.neighbor_set w := rfl

lemma mem_common_neighbors {u a b : α} : u ∈ G.common_neighbors a b ↔ G.adj v u ∧ G.adj w u :=
iff.rfl

lemma common_neighbors_symm (a b : α) : G.common_neighbors a b = G.common_neighbors w v :=
set.inter_comm _ _

lemma not_mem_common_neighbors_left (a b : α) : v ∉ G.common_neighbors a b :=
λ h, ne_of_adj G h.1 rfl

lemma not_mem_common_neighbors_right (a b : α) : w ∉ G.common_neighbors a b :=
λ h, ne_of_adj G h.2 rfl

lemma common_neighbors_subset_neighbor_set_left (a b : α) :
  G.common_neighbors a b ⊆ G.neighbor_set v :=
set.inter_subset_left _ _

lemma common_neighbors_subset_neighbor_set_right (a b : α) :
  G.common_neighbors a b ⊆ G.neighbor_set w :=
set.inter_subset_right _ _

instance decidable_mem_common_neighbors [decidable_rel G.adj] (a b : α) :
  decidable_pred (∈ G.common_neighbors a b) :=
λ a, and.decidable

section incidence
variable [decidable_eq V]

/--
Given an edge incident to a particular vertex, get the other vertex on the edge.
-/
def other_vertex_of_incident {v : α} {e : sym2 V} (h : e ∈ G.incidence_set v) : α := h.2.other'

lemma edge_mem_other_incident_set {v : α} {e : sym2 V} (h : e ∈ G.incidence_set v) :
  e ∈ G.incidence_set (G.other_vertex_of_incident h) :=
by { use h.1, simp [other_vertex_of_incident, sym2.mem_other_mem'] }

lemma incidence_other_prop {v : α} {e : sym2 V} (h : e ∈ G.incidence_set v) :
  G.other_vertex_of_incident h ∈ G.neighbor_set v :=
by { cases h with he hv, rwa [←sym2.mem_other_spec' hv, mem_edge_set] at he }

@[simp]
lemma incidence_other_neighbor_edge {a b : α} (h : w ∈ G.neighbor_set v) :
  G.other_vertex_of_incident (G.mem_incidence_iff_neighbor.mpr h) = w :=
sym2.congr_right.mp (sym2.mem_other_spec' (G.mem_incidence_iff_neighbor.mpr h).right)

/--
There is an equivalence between the set of edges incident to a given
vertex and the set of vertices adjacent to the vertex.
-/
@[simps] def incidence_set_equiv_neighbor_set (v : α) : G.incidence_set v ≃ G.neighbor_set v :=
{ to_fun := λ e, ⟨G.other_vertex_of_incident e.2, G.incidence_other_prop e.2⟩,
  inv_fun := λ w, ⟨⟦(v, w.1)⟧, G.mem_incidence_iff_neighbor.mpr w.2⟩,
  left_inv := λ x, by simp [other_vertex_of_incident],
  right_inv := λ ⟨w, hw⟩, by simp }

end incidence

section finite_at

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`fintype (G.neighbor_set v)`.

We define `G.neighbor_finset v` to be the `finset` version of `G.neighbor_set v`.
Use `neighbor_finset_eq_filter` to rewrite this definition as a `filter`.
-/

variables (v : α) [fintype (G.neighbor_set v)]
/--
`G.neighbors v` is the `finset` version of `G.adj v` in case `G` is
locally finite at `v`.
-/
def neighbor_finset : finset V := (G.neighbor_set v).to_finset

@[simp] lemma mem_neighbor_finset (w : α) :
  w ∈ G.neighbor_finset v ↔ G.adj a b :=
set.mem_to_finset

/--
`G.degree v` is the number of vertices adjacent to `v`.
-/
def degree : ℕ := (G.neighbor_finset v).card

@[simp]
lemma card_neighbor_set_eq_degree : fintype.card (G.neighbor_set v) = G.degree v :=
(set.to_finset_card _).symm

lemma degree_pos_iff_exists_adj : 0 < G.degree v ↔ ∃ w, G.adj a b :=
by simp only [degree, card_pos, finset.nonempty, mem_neighbor_finset]

instance incidence_set_fintype [decidable_eq V] : fintype (G.incidence_set v) :=
fintype.of_equiv (G.neighbor_set v) (G.incidence_set_equiv_neighbor_set v).symm

/--
This is the `finset` version of `incidence_set`.
-/
def incidence_finset [decidable_eq V] : finset (sym2 V) := (G.incidence_set v).to_finset

@[simp]
lemma card_incidence_set_eq_degree [decidable_eq V] :
  fintype.card (G.incidence_set v) = G.degree v :=
by { rw fintype.card_congr (G.incidence_set_equiv_neighbor_set v), simp }

@[simp]
lemma mem_incidence_finset [decidable_eq V] (e : sym2 V) :
  e ∈ G.incidence_finset v ↔ e ∈ G.incidence_set v :=
set.mem_to_finset

end finite_at

section locally_finite

/--
A graph is locally finite if every vertex has a finite neighbor set.
-/
@[reducible]
def locally_finite := Π (v : α), fintype (G.neighbor_set v)

variable [locally_finite G]

/--
A locally finite simple graph is regular of degree `d` if every vertex has degree `d`.
-/
def is_regular_of_degree (d : ℕ) : Prop := ∀ (v : α), G.degree v = d

lemma is_regular_of_degree_eq {d : ℕ} (h : G.is_regular_of_degree d) (v : α) : G.degree v = d := h v

end locally_finite

section finite

variable [fintype V]

instance neighbor_set_fintype [decidable_rel G.adj] (v : α) : fintype (G.neighbor_set v) :=
@subtype.fintype _ _ (by { simp_rw mem_neighbor_set, apply_instance }) _

lemma neighbor_finset_eq_filter {v : α} [decidable_rel G.adj] :
  G.neighbor_finset v = finset.univ.filter (G.adj v) :=
by { ext, simp }

@[simp]
lemma complete_graph_degree [decidable_eq V] (v : α) :
  (⊤ : weighted_graph α W).degree v = fintype.card V - 1 :=
begin
  convert univ.card.pred_eq_sub_one,
  erw [degree, neighbor_finset_eq_filter, filter_ne, card_erase_of_mem (mem_univ v)],
end

lemma complete_graph_is_regular [decidable_eq V] :
  (⊤ : weighted_graph α W).is_regular_of_degree (fintype.card V - 1) :=
by { intro v, simp }

/--
The minimum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_minimal_degree_vertex`, `min_degree_le_degree`
and `le_min_degree_of_forall_le_degree`.
-/
def min_degree [decidable_rel G.adj] : ℕ :=
option.get_or_else (univ.image (λ v, G.degree v)).min 0

/--
There exists a vertex of minimal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex.
-/
lemma exists_minimal_degree_vertex [decidable_rel G.adj] [nonempty V] :
  ∃ v, G.min_degree = G.degree v :=
begin
  obtain ⟨t, ht : _ = _⟩ := min_of_nonempty (univ_nonempty.image (λ v, G.degree v)),
  obtain ⟨v, _, rfl⟩ := mem_image.mp (mem_of_min ht),
  refine ⟨v, by simp [min_degree, ht]⟩,
end

/-- The minimum degree in the graph is at most the degree of any particular vertex. -/
lemma min_degree_le_degree [decidable_rel G.adj] (v : α) : G.min_degree ≤ G.degree v :=
begin
  obtain ⟨t, ht⟩ := finset.min_of_mem (mem_image_of_mem (λ v, G.degree v) (mem_univ v)),
  have := finset.min_le_of_mem (mem_image_of_mem _ (mem_univ v)) ht,
  rw option.mem_def at ht,
  rwa [min_degree, ht, option.get_or_else_some],
end

/--
In a nonempty graph, if `k` is at most the degree of every vertex, it is at most the minimum
degree. Note the assumption that the graph is nonempty is necessary as long as `G.min_degree` is
defined to be a natural.
-/
lemma le_min_degree_of_forall_le_degree [decidable_rel G.adj] [nonempty V] (k : ℕ)
  (h : ∀ v, k ≤ G.degree v) :
  k ≤ G.min_degree :=
begin
  rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩,
  rw hv,
  apply h
end

/--
The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_max_degree`
and `max_degree_le_of_forall_degree_le`.
-/
def max_degree [decidable_rel G.adj] : ℕ :=
option.get_or_else (univ.image (λ v, G.degree v)).max 0

/--
There exists a vertex of maximal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex.
-/
lemma exists_maximal_degree_vertex [decidable_rel G.adj] [nonempty V] :
  ∃ v, G.max_degree = G.degree v :=
begin
  obtain ⟨t, ht⟩ := max_of_nonempty (univ_nonempty.image (λ v, G.degree v)),
  have ht₂ := mem_of_max ht,
  simp only [mem_image, mem_univ, exists_prop_of_true] at ht₂,
  rcases ht₂ with ⟨v, rfl⟩,
  rw option.mem_def at ht,
  refine ⟨v, _⟩,
  rw [max_degree, ht],
  refl
end

/-- The maximum degree in the graph is at least the degree of any particular vertex. -/
lemma degree_le_max_degree [decidable_rel G.adj] (v : α) : G.degree v ≤ G.max_degree :=
begin
  obtain ⟨t, ht : _ = _⟩ := finset.max_of_mem (mem_image_of_mem (λ v, G.degree v) (mem_univ v)),
  have := finset.le_max_of_mem (mem_image_of_mem _ (mem_univ v)) ht,
  rwa [max_degree, ht, option.get_or_else_some],
end

/--
In a graph, if `k` is at least the degree of every vertex, then it is at least the maximum
degree.
-/
lemma max_degree_le_of_forall_degree_le [decidable_rel G.adj] (k : ℕ)
  (h : ∀ v, G.degree v ≤ k) :
  G.max_degree ≤ k :=
begin
  by_cases hV : (univ : finset V).nonempty,
  { haveI : nonempty V := univ_nonempty_iff.mp hV,
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex,
    rw hv,
    apply h },
  { rw not_nonempty_iff_eq_empty at hV,
    rw [max_degree, hV, image_empty],
    exact zero_le k },
end

lemma degree_lt_card_verts [decidable_rel G.adj] (v : α) : G.degree v < fintype.card V :=
begin
  classical,
  apply finset.card_lt_card,
  rw finset.ssubset_iff,
  exact ⟨v, by simp, finset.subset_univ _⟩,
end

/--
The maximum degree of a nonempty graph is less than the number of vertices. Note that the assumption
that `V` is nonempty is necessary, as otherwise this would assert the existence of a
natural number less than zero.
-/
lemma max_degree_lt_card_verts [decidable_rel G.adj] [nonempty V] : G.max_degree < fintype.card V :=
begin
  cases G.exists_maximal_degree_vertex with v hv,
  rw hv,
  apply G.degree_lt_card_verts v,
end

lemma card_common_neighbors_le_degree_left [decidable_rel G.adj] (a b : α) :
  fintype.card (G.common_neighbors a b) ≤ G.degree v :=
begin
  rw [←card_neighbor_set_eq_degree],
  exact set.card_le_of_subset (set.inter_subset_left _ _),
end

lemma card_common_neighbors_le_degree_right [decidable_rel G.adj] (a b : α) :
  fintype.card (G.common_neighbors a b) ≤ G.degree w :=
begin
  convert G.card_common_neighbors_le_degree_left w v using 3,
  apply common_neighbors_symm,
end

lemma card_common_neighbors_lt_card_verts [decidable_rel G.adj] (a b : α) :
  fintype.card (G.common_neighbors a b) < fintype.card V :=
nat.lt_of_le_of_lt (G.card_common_neighbors_le_degree_left _ _) (G.degree_lt_card_verts v)

/--
If the condition `G.adj a b` fails, then `card_common_neighbors_le_degree` is
the best we can do in general.
-/
lemma adj.card_common_neighbors_lt_degree {G : weighted_graph α W} [decidable_rel G.adj]
  {a b : α} (h : G.adj a b) :
  fintype.card (G.common_neighbors a b) < G.degree v :=
begin
  classical,
  erw [←set.to_finset_card],
  apply finset.card_lt_card,
  rw finset.ssubset_iff,
  use w,
  split,
  { rw set.mem_to_finset,
    apply not_mem_common_neighbors_right },
  { rw finset.insert_subset,
    split,
    { simpa, },
    { rw [neighbor_finset, ← set.subset_iff_to_finset_subset],
      exact G.common_neighbors_subset_neighbor_set_left _ _ } }
end

end finite

end weighted_graph

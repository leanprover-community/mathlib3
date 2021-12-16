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

/-- `W`-weighted graphs on `α`. `weight a b = some b` represents an edge between `a, b : α` of
weight `b : W`. `weight a b = none` represents no edge between `a` and `b`. -/
@[ext] structure weighted_graph (α : Type*) (W : Type*) :=
(weight : α → α → option W)
(weight_self (a : α) : weight a a = none)
(weight_comm (a b : α) : weight a b = weight b a)

namespace weighted_graph
variables (G : weighted_graph α W) (a b c : α)

/-- Two vertices of a weighted graph are adjacent if their weight is not `none`. -/
def adj : Prop := G.weight a b ≠ none

lemma adj_comm {a b : α} : G.adj a b ↔ G.adj b a := by { unfold adj, rw G.weight_comm }
lemma adj_symm : symmetric (G.adj) := λ _ _, G.adj_comm.1

lemma adj_irrefl : ¬ G.adj a a := λ h, h $ G.weight_self a

protected lemma adj.ne {G : weighted_graph α W} {a b : α} (h : G.adj a b) : a ≠ b :=
by { rintro rfl, exact G.adj_irrefl _ h }

instance : decidable_rel G.adj := λ a b, @not.decidable _ option.decidable_eq_none

/-- Turns a weighted graph into a simple graph by forgetting the weights. -/
def to_simple_graph (G : weighted_graph α W) : simple_graph α :=
{ adj := G.adj,
  symm := G.adj_symm,
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

end constructions

variables {a b c} {e : sym2 α}

/-- `G.neighbor_set a` is the set of vertices adjacent to `a` in `G`. -/
def neighbor_set (a : α) : set α := {b | G.adj a b}

lemma not_mem_neighbor_set (a : α) : a ∉ G.neighbor_set a := G.adj_irrefl _

instance neighbor_set.mem_decidable (a : α) [decidable_rel G.adj] :
  decidable_pred (∈ G.neighbor_set a) :=
by { unfold neighbor_set, apply_instance }

/-- The edges of G consist of the unordered pairs of vertices related by `G.adj`.

The way `edge_set` is defined is such that `mem_edge_set` is proved by `refl`.
That is, `⟦(a, b)⟧ ∈ G.edge_set` is definitionally equal to `G.adj a b`.-/
def edge_set : set (sym2 α) := sym2.from_rel G.adj_symm

/-- The `incidence_set` is the set of edges incident to a given vertex. -/
def incidence_set (a : α) : set (sym2 α) := {e ∈ G.edge_set | a ∈ e}

lemma incidence_set_subset (a : α) : G.incidence_set a ⊆ G.edge_set := λ _ h, h.1

@[simp] lemma mk_mem_edge_set : ⟦(a, b)⟧ ∈ G.edge_set ↔ G.adj a b := iff.rfl

/-- Two vertices are adjacent iff there is an edge between them.  The condition `a ≠ b` ensures they
are different endpoints of the edge, which is necessary since when `a = b` the existential
`∃ a ∈ G.edge_set, a ∈ e ∧ b ∈ e` is satisfied by every edge incident to `a`. -/
lemma adj_iff_exists_edge : G.adj a b ↔ a ≠ b ∧ ∃ e ∈ G.edge_set, a ∈ e ∧ b ∈ e :=
begin
  refine ⟨λ h, ⟨h.ne, ⟦(a, b)⟧, h, by simp⟩, _⟩,
  rintro ⟨hne, e, he, hv⟩,
  rw sym2.elems_iff_eq hne at hv,
  subst e,
  rwa mk_mem_edge_set at he,
end

lemma edge_other_ne (he : e ∈ G.edge_set) (h : a ∈ e) : h.other ≠ a :=
begin
  erw [← sym2.mem_other_spec h, sym2.eq_swap] at he,
  exact he.ne,
end

instance decidable_mem_edge_set [decidable_rel G.adj] : decidable_pred (∈ G.edge_set) :=
sym2.from_rel.decidable_pred _

instance edges_fintype [decidable_eq α] [fintype α] [decidable_rel G.adj] : fintype G.edge_set :=
subtype.fintype _

instance decidable_mem_incidence_set [decidable_eq α] [decidable_rel G.adj] (a : α) :
  decidable_pred (∈ G.incidence_set a) :=
λ e, and.decidable

/-- The `edge_set` of the graph as a `finset`. -/
def edge_finset [decidable_eq α] [fintype α] [decidable_rel G.adj] : finset (sym2 α) :=
set.to_finset G.edge_set

@[simp] lemma mem_edge_finset [decidable_eq α] [fintype α] [decidable_rel G.adj] (e : sym2 α) :
  e ∈ G.edge_finset ↔ e ∈ G.edge_set :=
set.mem_to_finset

@[simp] lemma edge_set_univ_card [decidable_eq α] [fintype α] [decidable_rel G.adj] :
  (finset.univ : finset G.edge_set).card = G.edge_finset.card :=
fintype.card_of_subtype G.edge_finset $ mem_edge_finset _

@[simp] lemma mem_neighbor_set : b ∈ G.neighbor_set a ↔ G.adj a b := iff.rfl

@[simp] lemma mk_mem_incidence_set : ⟦(a, b)⟧ ∈ G.incidence_set a ↔ G.adj a b :=
by simp [incidence_set]

lemma mk_mem_incidence_iff_neighbor : ⟦(a, b)⟧ ∈ G.incidence_set a ↔ b ∈ G.neighbor_set a :=
G.mk_mem_incidence_set.trans G.mem_neighbor_set.symm

lemma adj_incidence_set_inter {a : α} {e : sym2 α} (he : e ∈ G.edge_set) (h : a ∈ e) :
  G.incidence_set a ∩ G.incidence_set h.other = {e} :=
begin
  ext e',
  simp only [incidence_set, set.mem_sep_eq, set.mem_inter_eq, set.mem_singleton_iff],
  refine ⟨λ h', _, _⟩,
  { rw ←sym2.mem_other_spec h,
    exact (sym2.elems_iff_eq (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩, },
  { rintro rfl,
    exact ⟨⟨he, h⟩, he, sym2.mem_other_mem _⟩ }
end

/-- The set of common neighbors between two vertices `a` and `b` in a graph `G` is the
intersection of the neighbor sets of `a` and `b`. -/
def common_neighbors (a b : α) : set α := G.neighbor_set a ∩ G.neighbor_set b

lemma common_neighbors_eq (a b : α) :
  G.common_neighbors a b = G.neighbor_set a ∩ G.neighbor_set b := rfl

lemma mem_common_neighbors : c ∈ G.common_neighbors a b ↔ G.adj a c ∧ G.adj b c := iff.rfl

lemma common_neighbors_symm (a b : α) : G.common_neighbors a b = G.common_neighbors b a :=
set.inter_comm _ _

lemma not_mem_common_neighbors_left (a b : α) : a ∉ G.common_neighbors a b := λ h, h.1.ne rfl

lemma not_mem_common_neighbors_right (a b : α) : b ∉ G.common_neighbors a b := λ h, h.2.ne rfl

lemma common_neighbors_subset_neighbor_set_left (a b : α) :
  G.common_neighbors a b ⊆ G.neighbor_set a :=
set.inter_subset_left _ _

lemma common_neighbors_subset_neighbor_set_right (a b : α) :
  G.common_neighbors a b ⊆ G.neighbor_set b :=
set.inter_subset_right _ _

instance decidable_mem_common_neighbors [decidable_rel G.adj] (a b : α) :
  decidable_pred (∈ G.common_neighbors a b) :=
λ a, and.decidable

section incidence
variable [decidable_eq α]

/-- Given an edge incident to a particular vertex, get the other vertex on the edge. -/
def other_vertex_of_incident {a : α} {e : sym2 α} (h : e ∈ G.incidence_set a) : α := h.2.other'

lemma edge_mem_other_incident_set {a : α} {e : sym2 α} (h : e ∈ G.incidence_set a) :
  e ∈ G.incidence_set (G.other_vertex_of_incident h) :=
by { use h.1, simp [other_vertex_of_incident, sym2.mem_other_mem'] }

lemma incidence_other_prop {a : α} {e : sym2 α} (h : e ∈ G.incidence_set a) :
  G.other_vertex_of_incident h ∈ G.neighbor_set a :=
by { cases h with he ha, rwa [←sym2.mem_other_spec' ha, mk_mem_edge_set] at he }

@[simp] lemma incidence_other_neighbor_edge (h : b ∈ G.neighbor_set a) :
  G.other_vertex_of_incident (G.mk_mem_incidence_iff_neighbor.mpr h) = b :=
sym2.congr_right.mp (sym2.mem_other_spec' (G.mk_mem_incidence_iff_neighbor.mpr h).right)

/-- There is an equivalence between the set of edges incident to a given vertex and the set of
vertices adjacent to the vertex. -/
@[simps] def incidence_set_equiv_neighbor_set (a : α) : G.incidence_set a ≃ G.neighbor_set a :=
{ to_fun := λ e, ⟨G.other_vertex_of_incident e.2, G.incidence_other_prop e.2⟩,
  inv_fun := λ b, ⟨⟦(a, b.1)⟧, G.mk_mem_incidence_iff_neighbor.mpr b.2⟩,
  left_inv := λ x, by simp [other_vertex_of_incident],
  right_inv := λ ⟨b, hb⟩, by simp }

end incidence

section finite_at

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`fintype (G.neighbor_set a)`.

We define `G.neighbor_finset a` to be the `finset` version of `G.neighbor_set a`.
Use `neighbor_finset_eq_filter` to rewrite this definition as a `filter`.
-/

variables (a) [fintype (G.neighbor_set a)]

/-- `G.neighbors a` is the `finset` version of `G.adj a` in case `G` is
locally finite at `a`. -/
def neighbor_finset : finset α := (G.neighbor_set a).to_finset

@[simp] lemma mem_neighbor_finset (b : α) : b ∈ G.neighbor_finset a ↔ G.adj a b :=
set.mem_to_finset

lemma not_mem_neighbor_finset : a ∉ G.neighbor_finset a :=
λ h, G.not_mem_neighbor_set _ $ set.mem_to_finset.1 h

/-- `G.degree a` is the number of vertices adjacent to `a`. -/
def degree : ℕ := (G.neighbor_finset a).card

@[simp]
lemma card_neighbor_set_eq_degree : fintype.card (G.neighbor_set a) = G.degree a :=
(set.to_finset_card _).symm

lemma degree_pos_iff_exists_adj : 0 < G.degree a ↔ ∃ b, G.adj a b :=
by simp only [degree, finset.card_pos, finset.nonempty, mem_neighbor_finset]

instance incidence_set_fintype [decidable_eq α] : fintype (G.incidence_set a) :=
fintype.of_equiv (G.neighbor_set a) (G.incidence_set_equiv_neighbor_set a).symm

/--
This is the `finset` version of `incidence_set`.
-/
def incidence_finset [decidable_eq α] : finset (sym2 α) := (G.incidence_set a).to_finset

@[simp]
lemma card_incidence_set_eq_degree [decidable_eq α] :
  fintype.card (G.incidence_set a) = G.degree a :=
by { rw fintype.card_congr (G.incidence_set_equiv_neighbor_set a), simp }

@[simp]
lemma mem_incidence_finset [decidable_eq α] (e : sym2 α) :
  e ∈ G.incidence_finset a ↔ e ∈ G.incidence_set a :=
set.mem_to_finset

end finite_at

section locally_finite

/--
A graph is locally finite if every vertex has a finite neighbor set.
-/
@[reducible]
def locally_finite := Π (a : α), fintype (G.neighbor_set a)

variable [locally_finite G]

/--
A locally finite simple graph is regular of degree `d` if every vertex has degree `d`.
-/
def is_regular_of_degree (d : ℕ) : Prop := ∀ (a : α), G.degree a = d

lemma is_regular_of_degree_eq {d : ℕ} (h : G.is_regular_of_degree d) (a : α) : G.degree a = d := h a

end locally_finite

section finite
variable [fintype α]

open finset

instance neighbor_set_fintype [decidable_rel G.adj] (a : α) : fintype (G.neighbor_set a) :=
@subtype.fintype _ _ (by { simp_rw mem_neighbor_set, apply_instance }) _

lemma neighbor_finset_eq_filter {a : α} [decidable_rel G.adj] :
  G.neighbor_finset a = univ.filter (G.adj a) :=
by { ext, simp }

/-- The minimum degree of all vertices (and `0` if there are no vertices). The key properties of
this are given in `exists_minimal_degree_vertex`, `min_degree_le_degree` and
`le_min_degree_of_forall_le_degree`. -/
def min_degree [decidable_rel G.adj] : ℕ :=
option.get_or_else (univ.image (λ a, G.degree a)).min 0

/--
There exists a vertex of minimal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex.
-/
lemma exists_minimal_degree_vertex [decidable_rel G.adj] [nonempty α] :
  ∃ a, G.min_degree = G.degree a :=
begin
  obtain ⟨t, ht : _ = _⟩ := min_of_nonempty (univ_nonempty.image (λ a, G.degree a)),
  obtain ⟨a, _, rfl⟩ := mem_image.mp (mem_of_min ht),
  refine ⟨a, by simp [min_degree, ht]⟩,
end

/-- The minimum degree in the graph is at most the degree of any particular vertex. -/
lemma min_degree_le_degree [decidable_rel G.adj] (a : α) : G.min_degree ≤ G.degree a :=
begin
  obtain ⟨t, ht⟩ := min_of_mem (mem_image_of_mem (λ a, G.degree a) (mem_univ a)),
  have := min_le_of_mem (mem_image_of_mem _ (mem_univ a)) ht,
  rw option.mem_def at ht,
  rwa [min_degree, ht, option.get_or_else_some],
end

/--
In a nonempty graph, if `k` is at most the degree of every vertex, it is at most the minimum
degree. Note the assumption that the graph is nonempty is necessary as long as `G.min_degree` is
defined to be a natural.
-/
lemma le_min_degree_of_forall_le_degree [decidable_rel G.adj] [nonempty α] (k : ℕ)
  (h : ∀ a, k ≤ G.degree a) :
  k ≤ G.min_degree :=
begin
  rcases G.exists_minimal_degree_vertex with ⟨a, hv⟩,
  rw hv,
  apply h
end

/--
The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_max_degree`
and `max_degree_le_of_forall_degree_le`.
-/
def max_degree [decidable_rel G.adj] : ℕ :=
option.get_or_else (univ.image (λ a, G.degree a)).max 0

/--
There exists a vertex of maximal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex.
-/
lemma exists_maximal_degree_vertex [decidable_rel G.adj] [nonempty α] :
  ∃ a, G.max_degree = G.degree a :=
begin
  obtain ⟨t, ht⟩ := max_of_nonempty (univ_nonempty.image (λ a, G.degree a)),
  have ht₂ := mem_of_max ht,
  simp only [mem_image, mem_univ, exists_prop_of_true] at ht₂,
  rcases ht₂ with ⟨a, rfl⟩,
  rw option.mem_def at ht,
  refine ⟨a, _⟩,
  rw [max_degree, ht],
  refl
end

/-- The maximum degree in the graph is at least the degree of any particular vertex. -/
lemma degree_le_max_degree [decidable_rel G.adj] (a : α) : G.degree a ≤ G.max_degree :=
begin
  obtain ⟨t, ht : _ = _⟩ := max_of_mem (mem_image_of_mem (λ a, G.degree a) (mem_univ a)),
  have := le_max_of_mem (mem_image_of_mem _ (mem_univ a)) ht,
  rwa [max_degree, ht, option.get_or_else_some],
end

/--
In a graph, if `k` is at least the degree of every vertex, then it is at least the maximum
degree.
-/
lemma max_degree_le_of_forall_degree_le [decidable_rel G.adj] (k : ℕ)
  (h : ∀ a, G.degree a ≤ k) :
  G.max_degree ≤ k :=
begin
  by_cases hα : (univ : finset α).nonempty,
  { haveI : nonempty α := univ_nonempty_iff.mp hα,
    obtain ⟨a, hv⟩ := G.exists_maximal_degree_vertex,
    rw hv,
    apply h },
  { rw not_nonempty_iff_eq_empty at hα,
    rw [max_degree, hα, image_empty],
    exact zero_le k },
end

lemma degree_lt_card_verts [decidable_rel G.adj] (a : α) : G.degree a < fintype.card α :=
begin
  classical,
  apply card_lt_card,
  rw ssubset_iff,
  exact ⟨a, by convert G.not_mem_neighbor_finset _, finset.subset_univ _⟩,
end

/-- The maximum degree of a nonempty graph is less than the number of vertices. Note that the
assumption that `α` is nonempty is necessary, as otherwise this would assert the existence of a natural number less than zero. -/
lemma max_degree_lt_card_verts [decidable_rel G.adj] [nonempty α] : G.max_degree < fintype.card α :=
begin
  cases G.exists_maximal_degree_vertex with a hv,
  rw hv,
  apply G.degree_lt_card_verts a,
end

lemma card_common_neighbors_le_degree_left [decidable_rel G.adj] (a b : α) :
  fintype.card (G.common_neighbors a b) ≤ G.degree a :=
begin
  rw [←card_neighbor_set_eq_degree],
  exact set.card_le_of_subset (set.inter_subset_left _ _),
end

lemma card_common_neighbors_le_degree_right [decidable_rel G.adj] (a b : α) :
  fintype.card (G.common_neighbors a b) ≤ G.degree b :=
begin
  convert G.card_common_neighbors_le_degree_left b a using 3,
  apply common_neighbors_symm,
end

lemma card_common_neighbors_lt_card_verts [decidable_rel G.adj] (a b : α) :
  fintype.card (G.common_neighbors a b) < fintype.card α :=
nat.lt_of_le_of_lt (G.card_common_neighbors_le_degree_left _ _) (G.degree_lt_card_verts a)

/-- If the condition `G.adj a b` fails, then `card_common_neighbors_le_degree` is
the best we can do in general. -/
lemma adj.card_common_neighbors_lt_degree {G : weighted_graph α W} [decidable_rel G.adj]
  (h : G.adj a b) :
  fintype.card (G.common_neighbors a b) < G.degree a :=
begin
  classical,
  erw [←set.to_finset_card],
  apply card_lt_card,
  rw ssubset_iff,
  use b,
  split,
  { rw set.mem_to_finset,
    apply not_mem_common_neighbors_right },
  { rw insert_subset,
    split,
    { simpa, },
    { rw [neighbor_finset, ← set.subset_iff_to_finset_subset],
      exact G.common_neighbors_subset_neighbor_set_left _ _ } }
end

end finite

end weighted_graph

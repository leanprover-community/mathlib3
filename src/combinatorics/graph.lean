import data.rel
import data.set.finite
import data.sym.sym2

open finset

universes u v w

variables {γ : Type u}

/-- Adjacency relation for graphs -/
class has_adj (G : γ) (V : out_param $ Type v) :=
(adj : V → V → Prop)

/-- That `adj` is symmetric (for unoriented graphs) -/
class is_adj_symmetric (G : γ) (V : out_param $ Type v) [has_adj G V] : Prop :=
(adj_symm [] : symmetric (has_adj.adj G))

/-- That `adj` is irreflexive (for loopless graphs) -/
class is_adj_loopless (G : γ) (V : out_param $ Type v) [has_adj G V] : Prop :=
(adj_loopless [] : irreflexive (has_adj.adj G))

/-- That `adj` is reflexive (for so-called "reflexive" graphs) -/
class is_adj_reflexive (G : γ) (V : out_param $ Type v) [has_adj G V] : Prop :=
(adj_reflexive [] : reflexive (has_adj.adj G))

/-- That `adj` is antisymmetric (for oriented graphs) -/
class is_adj_anti_symmetric (G : γ) (V : out_param $ Type v) [has_adj G V] : Prop :=
(adj_antisymm [] : anti_symmetric (has_adj.adj G))

/-- Edge sets between pairs of vertices. Similar to `has_hom`.
Should implement either `has_undirected_edges` or `has_directed_edges`.

The `edge_set` is given explicitly so that graph implementations can give it a good definition. -/
class has_edges (G : γ) (V : out_param $ Type v) (E : out_param $ Type w) extends has_adj G V :=
(edges : V → V → set E)
(edge_set : set E)
(incidence_set : V → set E) /-^ Set of edges in incident to `v`.
(If the graph is directed, this is edges *from* the vertex.) -/
(coincidence_set : V → set E) /-^ Set of edges in incident to `v`.
(If the graph is directed, this is edges *to* the vertex.) -/
(nonempty_edges_iff_adj : ∀ (v w : V), (edges v w).nonempty ↔ adj v w)
(edge_set_eq : edge_set = ⋃(v w : V), edges v w)
(incidence_set_eq : ∀ v, incidence_set v = ⋃ (w : V), edges v w)
(coincidence_set_eq : ∀ v, coincidence_set v = ⋃ (w : V), edges w v)

/-- Undirected edges have the property that they appear in both an edge set and its reverse. -/
class has_undirected_edges (G : γ) (V : out_param $ Type v) (E : out_param $ Type w)
  extends has_edges G V E, is_adj_symmetric G V :=
(edges_symm [] : ∀ v w, edges v w ⊆ edges w v)
(undir_edges_disjoint : ∀ {v w v' w' e}, e ∈ edges v w → e ∈ edges v' w' →
  (v = v' ∧ w = w') ∨ (v = w' ∧ w = v'))
(edge_ends : edge_set → sym2 V)
(edge_ends_prop : ∀ v w e, edge_ends e = ⟦(v, w)⟧ → (e : E) ∈ edges v w)

/-- Class for graphs with at most one edge between pairs of vertices, encoded using `sym2 V`. -/
class has_simple_undirected_edges (G : γ) (V : out_param $ Type v)
  extends has_undirected_edges G V (sym2 V) :=
(edges_prop' : ∀ (v w : V) (e : sym2 V), e ∈ edges v w → e = ⟦(v, w)⟧)

/-- Directed edges have the property that they appear in exactly one edge set. -/
class has_directed_edges (G : γ) (V : out_param $ Type v) (E : out_param $ Type w)
  extends has_edges G V E :=
(dir_edges_disjoint : ∀ {v w v' w' e}, e ∈ edges v w → e ∈ edges v' w' → v = v' ∧ w = w')
(edge_fst : edge_set → V)
(edge_snd : edge_set → V)
(edge_fst_snd_prop : ∀ (e : edge_set), (e : E) ∈ edges (edge_fst e) (edge_snd e))

namespace graph

export has_adj is_adj_symmetric is_adj_loopless is_adj_reflexive is_adj_anti_symmetric
export has_edges has_undirected_edges has_simple_undirected_edges has_directed_edges

section basic

variables (G : γ) {V : Type v} [has_adj G V] {u v : V}

@[simp] lemma adj_irrefl [is_adj_loopless G V] : ¬ adj G u u := adj_loopless G u

lemma adj_comm [is_adj_symmetric G V] (u v : V) : adj G u v ↔ adj G v u :=
⟨λ h, adj_symm G h, λ h, adj_symm G h⟩

@[symm] lemma adj_symm' [is_adj_symmetric G V] (h : adj G u v) : adj G v u := adj_symm G h

/-- The version of `adj` lifted to `sym2 V`. -/
def adj_sym2 [is_adj_symmetric G V] : sym2 V → Prop :=
sym2.from_rel (adj_symm G)

@[simp] lemma adj_sym2_iff [is_adj_symmetric G V] (v w : V) :
  adj_sym2 G ⟦(v, w)⟧ ↔ adj G v w :=
iff.rfl

lemma ne_of_adj [is_adj_loopless G V] (h : adj G u v) : u ≠ v :=
by { rintro rfl, exact adj_irrefl G h }

variables {G}

protected lemma _root_.has_adj.adj.ne [is_adj_loopless G V] (h : adj G u v) :
  u ≠ v := ne_of_adj G h

protected lemma _root_.has_adj.adj.ne' [is_adj_loopless G V] (h : adj G u v) :
  v ≠ u := h.ne.symm

variables (G)

/-- `G.support` is the set of vertices `v` such that `adj G v w` for some vertex `w`. -/
def support : set V := rel.dom (adj G)

/-- `G.cosupport` is the set of vertices `v` such that `adj G w v` for some vertex `w`. -/
def cosupport : set V := rel.codom (adj G)

lemma mem_support {v : V} : v ∈ support G ↔ ∃ w, adj G v w := iff.rfl

lemma mem_cosupport {v : V} : v ∈ cosupport G ↔ ∃ w, adj G w v := iff.rfl

lemma cosupport_eq_of_symm [is_adj_symmetric G V] : cosupport G = support G :=
by { ext v, simp [mem_support, mem_cosupport, adj_comm] }

/-- `G.neighbor_set v` is the set of vertices `w` such that `adj G v w`. -/
def neighbor_set (v : V) : set V := {w | adj G v w}

/-- `G.coneighbor_set v` is the set of vertices `w` such that `adj G w v`. -/
def coneighbor_set (v : V) : set V := {w | adj G w v}

@[simp] lemma mem_neighbor_set (v w : V) : w ∈ neighbor_set G v ↔ adj G v w :=
iff.rfl

@[simp] lemma mem_coneighbor_set (v w : V) : w ∈ coneighbor_set G v ↔ adj G w v :=
iff.rfl

lemma coneighbor_set_eq_of_symm [is_adj_symmetric G V] : coneighbor_set G v = neighbor_set G v :=
by { ext, simp [adj_comm] }

instance neighbor_set.mem_decidable (v : V) [decidable_rel (adj G)] :
  decidable_pred (∈ neighbor_set G v) := by { unfold neighbor_set, apply_instance }

instance coneighbor_set.mem_decidable (v : V) [decidable_rel (adj G)] :
  decidable_pred (∈ coneighbor_set G v) := by { unfold coneighbor_set, apply_instance }

/--
The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`.
-/
def common_neighbors (v w : V) : set V := neighbor_set G v ∩ neighbor_set G w

lemma common_neighbors_eq (v w : V) :
  common_neighbors G v w = neighbor_set G v ∩ neighbor_set G w := rfl

lemma mem_common_neighbors {u v w : V} : u ∈ common_neighbors G v w ↔ adj G v u ∧ adj G w u :=
iff.rfl

lemma common_neighbors_symm (v w : V) : common_neighbors G v w = common_neighbors G w v :=
set.inter_comm _ _

lemma not_mem_common_neighbors_left [is_adj_loopless G V] (v w : V) :
  v ∉ common_neighbors G v w :=
λ h, h.1.ne rfl

lemma not_mem_common_neighbors_right [is_adj_loopless G V] (v w : V) :
  w ∉ common_neighbors G v w :=
λ h, h.2.ne rfl

lemma common_neighbors_subset_neighbor_set_left (v w : V) :
  common_neighbors G v w ⊆ neighbor_set G v :=
set.inter_subset_left _ _

lemma common_neighbors_subset_neighbor_set_right (v w : V) :
  common_neighbors G v w ⊆ neighbor_set G w :=
set.inter_subset_right _ _

instance decidable_mem_common_neighbors [decidable_rel (adj G)] (v w : V) :
  decidable_pred (∈ common_neighbors G v w) :=
λ a, and.decidable


section finite_at

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`fintype (neighbor_set G v)`.

We define `neighbor_finset G v` to be the `finset` version of `G.neighbor_set v`.
Use `neighbor_finset_eq_filter` to rewrite this definition as a `filter`.
-/

variables (v) [fintype (neighbor_set G v)]
/--
`neighbor_set G v` is the `finset` version of `G.neighbor_set v` in case `G` is
locally finite at `v`.
-/
def neighbor_finset : finset V := (neighbor_set G v).to_finset

@[simp] lemma mem_neighbor_finset (w : V) :
  w ∈ neighbor_finset G v ↔ adj G v w :=
set.mem_to_finset

/--
`G.degree v` is the number of vertices adjacent to `v`.
-/
def degree : ℕ := (neighbor_finset G v).card

@[simp]
lemma card_neighbor_set_eq_degree : fintype.card (neighbor_set G v) = degree G v :=
(set.to_finset_card _).symm

lemma degree_pos_iff_exists_adj : 0 < degree G v ↔ ∃ w, adj G v w :=
by simp only [degree, card_pos, finset.nonempty, mem_neighbor_finset]

end finite_at

section locally_finite

/--
A graph is locally finite if every vertex has a finite neighbor set.
-/
@[reducible]
def locally_finite := Π (v : V), fintype (neighbor_set G v)

variable [locally_finite G]

/--
A locally finite simple graph is regular of degree `d` if every vertex has degree `d`.
-/
def is_regular_of_degree (d : ℕ) : Prop := ∀ (v : V), degree G v = d

lemma is_regular_of_degree_eq {d : ℕ} (h : is_regular_of_degree G d) (v : V) : degree G v = d := h v

end locally_finite

section finite

variable [fintype V]

instance neighbor_set_fintype [decidable_rel (adj G)] (v : V) : fintype (neighbor_set G v) :=
@subtype.fintype _ _ (by { simp_rw mem_neighbor_set, apply_instance }) _

lemma neighbor_finset_eq_filter {v : V} [decidable_rel (adj G)] :
  neighbor_finset G v = finset.univ.filter (adj G v) :=
by { ext, simp }

/--
The minimum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_minimal_degree_vertex`, `min_degree_le_degree`
and `le_min_degree_of_forall_le_degree`.
-/
def min_degree [decidable_rel (adj G)] : ℕ :=
option.get_or_else (univ.image (λ (v : V), degree G v)).min 0

/--
There exists a vertex of minimal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex.
-/
lemma exists_minimal_degree_vertex [decidable_rel (adj G)] [nonempty V] :
  ∃ v, min_degree G = degree G v :=
begin
  obtain ⟨t, ht : _ = _⟩ := min_of_nonempty (univ_nonempty.image (λ v, degree G v)),
  obtain ⟨v, _, rfl⟩ := mem_image.mp (mem_of_min ht),
  refine ⟨v, by simp [min_degree, ht]⟩,
end

/-- The minimum degree in the graph is at most the degree of any particular vertex. -/
lemma min_degree_le_degree [decidable_rel (adj G)] (v : V) : min_degree G ≤ degree G v :=
begin
  obtain ⟨t, ht⟩ := finset.min_of_mem (mem_image_of_mem (λ v, degree G v) (mem_univ v)),
  have := finset.min_le_of_mem (mem_image_of_mem _ (mem_univ v)) ht,
  rw option.mem_def at ht,
  rwa [min_degree, ht, option.get_or_else_some],
end

/--
In a nonempty graph, if `k` is at most the degree of every vertex, it is at most the minimum
degree. Note the assumption that the graph is nonempty is necessary as long as `G.min_degree` is
defined to be a natural.
-/
lemma le_min_degree_of_forall_le_degree [decidable_rel (adj G)] [nonempty V] (k : ℕ)
  (h : ∀ v, k ≤ degree G v) :
  k ≤ min_degree G :=
begin
  obtain ⟨v, hv⟩ := exists_minimal_degree_vertex G,
  rw hv,
  apply h
end

/--
The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_max_degree`
and `max_degree_le_of_forall_degree_le`.
-/
def max_degree [decidable_rel (adj G)] : ℕ :=
option.get_or_else (univ.image (λ (v : V), degree G v)).max 0

/--
There exists a vertex of maximal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex.
-/
lemma exists_maximal_degree_vertex [decidable_rel (adj G)] [nonempty V] :
  ∃ v, max_degree G = degree G v :=
begin
  obtain ⟨t, ht⟩ := max_of_nonempty (univ_nonempty.image (λ v, degree G v)),
  have ht₂ := mem_of_max ht,
  simp only [mem_image, mem_univ, exists_prop_of_true] at ht₂,
  rcases ht₂ with ⟨v, rfl⟩,
  rw option.mem_def at ht,
  refine ⟨v, _⟩,
  rw [max_degree, ht],
  refl
end

/-- The maximum degree in the graph is at least the degree of any particular vertex. -/
lemma degree_le_max_degree [decidable_rel (adj G)] (v : V) : degree G v ≤ max_degree G :=
begin
  obtain ⟨t, ht : _ = _⟩ := finset.max_of_mem (mem_image_of_mem (λ v, degree G v) (mem_univ v)),
  have := finset.le_max_of_mem (mem_image_of_mem _ (mem_univ v)) ht,
  rwa [max_degree, ht, option.get_or_else_some],
end

/--
In a graph, if `k` is at least the degree of every vertex, then it is at least the maximum
degree.
-/
lemma max_degree_le_of_forall_degree_le [decidable_rel (adj G)] (k : ℕ)
  (h : ∀ (v : V), degree G v ≤ k) :
  max_degree G ≤ k :=
begin
  by_cases hV : (univ : finset V).nonempty,
  { haveI : nonempty V := univ_nonempty_iff.mp hV,
    obtain ⟨v, hv⟩ := exists_maximal_degree_vertex G,
    rw hv,
    apply h },
  { rw not_nonempty_iff_eq_empty at hV,
    rw [max_degree, hV, image_empty],
    exact zero_le k },
end

lemma degree_lt_card_verts [is_adj_loopless G V] [decidable_rel (adj G)] (v : V) :
  degree G v < fintype.card V :=
begin
  classical,
  apply finset.card_lt_card,
  rw finset.ssubset_iff,
  refine ⟨v, by simp, finset.subset_univ _⟩,
end

/--
The maximum degree of a nonempty graph is less than the number of vertices. Note that the assumption
that `V` is nonempty is necessary, as otherwise this would assert the existence of a
natural number less than zero.
-/
lemma max_degree_lt_card_verts [is_adj_loopless G V] [decidable_rel (adj G)] [nonempty V] :
  max_degree G < fintype.card V :=
begin
  cases exists_maximal_degree_vertex G with v hv,
  rw hv,
  apply degree_lt_card_verts G v,
end

lemma card_common_neighbors_le_degree_left [decidable_rel (adj G)] (v w : V) :
  fintype.card (common_neighbors G v w) ≤ degree G v :=
begin
  rw [←card_neighbor_set_eq_degree],
  exact set.card_le_of_subset (set.inter_subset_left _ _),
end

lemma card_common_neighbors_le_degree_right [decidable_rel (adj G)] (v w : V) :
  fintype.card (common_neighbors G v w) ≤ degree G w :=
begin
  convert card_common_neighbors_le_degree_left G w v using 3,
  apply common_neighbors_symm,
end

lemma card_common_neighbors_lt_card_verts [is_adj_loopless G V] [decidable_rel (adj G)] (v w : V) :
  fintype.card (common_neighbors G v w) < fintype.card V :=
nat.lt_of_le_of_lt (card_common_neighbors_le_degree_left G _ _) (degree_lt_card_verts G v)

/--
If the condition `G.adj v w` fails, then `card_common_neighbors_le_degree` is
the best we can do in general.
-/
lemma adj.card_common_neighbors_lt_degree [is_adj_loopless G V] [decidable_rel (adj G)]
  {v w : V} (h : adj G v w) :
  fintype.card (common_neighbors G v w) < degree G v :=
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
      exact common_neighbors_subset_neighbor_set_left G _ _ } }
end

end finite

end basic

section has_edges

variables (G : γ) {V : Type v} {E : Type w} [has_edges G V E]

lemma adj_of_mem_edges {v w : V} {e : E} (h : e ∈ edges G v w) : adj G v w :=
(nonempty_edges_iff_adj _ _).mp ⟨e, h⟩

lemma mem_edge_set_of_mem_edges {v w : V} {e : E} (h : e ∈ edges G v w) : e ∈ edge_set G :=
begin
  simp_rw [edge_set_eq, set.mem_Union],
  exact ⟨v, w, h⟩,
end

lemma incidence_set_subset (v : V) : incidence_set G v ⊆ (edge_set G : set E) :=
begin
  simp only [incidence_set_eq, edge_set_eq, set.Union_subset_iff],
  intros w e he,
  simp only [set.mem_Union],
  exact ⟨_, _, he⟩,
end

lemma coincidence_set_subset (v : V) : coincidence_set G v ⊆ (edge_set G : set E) :=
begin
  simp only [coincidence_set_eq, edge_set_eq, set.Union_subset_iff],
  intros w e he,
  simp only [set.mem_Union],
  exact ⟨_, _, he⟩,
end

end has_edges

section has_undir_edge

variables (G : γ) {V : Type v} {E : Type w} [has_undirected_edges G V E]

lemma adj_iff_exists_edge [is_adj_loopless G V] {v w : V} :
  adj G v w ↔ v ≠ w ∧ ∃ (e : E), e ∈ edges G v w :=
begin
  split,
  { intro ha,
    split,
    { exact ne_of_adj G ha },
    rwa [←set.nonempty_def, nonempty_edges_iff_adj], },
  { rintro ⟨hn, ha⟩,
    rwa [←nonempty_edges_iff_adj, set.nonempty_def], },
end

lemma edges_comm {v w : V} : (edges G v w : set E) = edges G w v :=
by { ext e, split; apply edges_symm }

lemma coincidence_set_eq (v : V) :
  (coincidence_set G v : set E) = incidence_set G v :=
begin
  simp only [coincidence_set_eq, incidence_set_eq],
  congr',
  ext w,
  rw edges_comm G,
end

lemma mem_edge_ends_of_mem_incidence_set {v : V} {e : E}
  (h : e ∈ incidence_set G v)
  (h' : e ∈ edge_set G) :
  v ∈ edge_ends ⟨e, h'⟩ :=
begin
  generalize hs : edge_ends ⟨e, incidence_set_subset G _ h⟩ = s,
  refine sym2.ind (λ v' w' hs, _) s hs,
  have := edge_ends_prop _ _ _ hs,
  simp only [incidence_set_eq, set.mem_Union] at h,
  obtain ⟨w, h⟩ := h,
  obtain (⟨rfl,rfl⟩|⟨rfl,rfl⟩) := undir_edges_disjoint h this;
  simp,
end

lemma edge_ends_eq_of_mem_edges {v w : V} {e : E}
  (h : e ∈ edges G v w)
  (h' : e ∈ edge_set G) :
  edge_ends ⟨e, h'⟩ = ⟦(v, w)⟧ :=
begin
  generalize hs : edge_ends ⟨e, mem_edge_set_of_mem_edges G h⟩ = s,
  refine sym2.ind (λ v' w' hs, _) s hs,
  have := edge_ends_prop _ _ ⟨e, mem_edge_set_of_mem_edges G h⟩ hs,
  obtain (⟨rfl,rfl⟩|⟨rfl,rfl⟩) := undir_edges_disjoint h this,
  { refl },
  { rw sym2.eq_swap },
end

variable [decidable_eq V]

/--
Given an edge incident to a particular vertex, get the other vertex on the edge.
-/
def other_vertex_of_incident {v : V} {e : E} (h : e ∈ incidence_set G v) : V :=
(mem_edge_ends_of_mem_incidence_set G h (incidence_set_subset G _ h)).other'

lemma edge_ends_eq_other_vertex_of_incident {v : V} {e : E}
  (h : e ∈ incidence_set G v) (h' : e ∈ edge_set G) :
  edge_ends ⟨e, h'⟩ = ⟦(v, other_vertex_of_incident G h)⟧ :=
by simp [other_vertex_of_incident]

lemma edge_other_incident_set {v : V} {e : E} (h : e ∈ incidence_set G v) :
  e ∈ incidence_set G (other_vertex_of_incident G h) :=
begin
  simp only [incidence_set_eq, set.mem_Union] at h ⊢,
  obtain ⟨w, he⟩ := h,
  use v,
  rw edges_comm,
  convert he,
  have h' := sym2.other_spec' (mem_edge_ends_of_mem_incidence_set G h (incidence_set_subset G _ h)),
  have h'' := edge_ends_eq_of_mem_edges G he (incidence_set_subset G _ h),
  rw ←h' at h'',
  rw sym2.eq_iff at h'',
  obtain (⟨-,rfl⟩|⟨rfl,h''⟩) := h'',
  { refl, },
  { conv_rhs { rw ←h'' },
    refl, }
end

lemma incidence_other_prop {v : V} {e : E} (h : e ∈ incidence_set G v) :
  other_vertex_of_incident G h ∈ neighbor_set G v :=
begin
  have := edge_ends_eq_other_vertex_of_incident G h (incidence_set_subset G _ h),
  have := edge_ends_prop _ _ _ this,
  simp only [mem_neighbor_set],
  apply adj_of_mem_edges _ this,
end

end has_undir_edge

section default_undirected_edges

/-- A `has_simple_undirected_edges` instance using `sym2 V` to provide the edges.

The way `edge_set` is defined is such that `mem_edge_set` is proved by `refl`.
(That is, `⟦(v, w)⟧ ∈ G.edge_set` is definitionally equal to `G.adj v w`.) -/
def default_simple_undirected_edges (G : γ) {V : Type v}
  (adj' : V → V → Prop) (symm' : symmetric adj') :
  has_simple_undirected_edges G V :=
{ adj := adj',
  adj_symm := symm',
  edges := λ v w, {e | adj' v w ∧ e = ⟦(v, w)⟧},
  edge_set := sym2.from_rel symm',
  incidence_set := λ v, {e ∈ sym2.from_rel symm' | v ∈ e},
  coincidence_set := λ v, {e ∈ sym2.from_rel symm' | v ∈ e},
  nonempty_edges_iff_adj := λ v w,
    ⟨by { rintro ⟨e, he, -⟩, exact he }, λ h, ⟨_, h, rfl⟩⟩,
  edge_set_eq := begin
    ext e,
    refine sym2.ind (λ v w, _) e,
    simp only [set.mem_Union, sym2.from_rel_prop, set.mem_set_of_eq],
    split,
    { exact λ h, ⟨v, w, h, rfl⟩, },
    { rintro ⟨v', w', h', he⟩,
      rw sym2.eq_iff at he,
      cases he; rw [he.1, he.2];
      simp [h', symm' h'], }
  end,
  edges_symm := λ v w e, begin
    simp only [sym2.eq_swap, and_imp, set.mem_set_of_eq],
    intro h,
    simp [symm' h],
  end,
  undir_edges_disjoint := λ v w v' w' e, begin
    refine sym2.ind (λ v'' w'', _) e,
    simp only [and_imp, set.mem_set_of_eq],
    rintro - h - h',
    rw [←sym2.eq_iff, ←h, ←h'],
  end,
  edge_ends := λ e, e,
  edge_ends_prop := begin
    rintro v w ⟨e, he⟩ h',
    simp only [subtype.coe_mk] at *,
    subst e,
    use [he],
  end,
  edges_prop' := λ v w e h, h.2,
  incidence_set_eq := λ v, begin
    ext e,
    refine sym2.ind (λ v' w', _) e,
    simp only [set.mem_Union, set.mem_sep_eq, sym2.mem_iff, sym2.from_rel_prop, set.mem_set_of_eq],
    split,
    { rintro ⟨h, (rfl|rfl)⟩,
      { use [w', h] },
      { use [v', symm' h],
        rw sym2.eq_swap } },
    { simp_rw sym2.eq_iff,
      rintro ⟨u, h, (⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩;
      simp [h, symm' h], }
  end,
  coincidence_set_eq := λ v, begin
    ext e,
    refine sym2.ind (λ v' w', _) e,
    simp only [set.mem_Union, set.mem_sep_eq, sym2.mem_iff, sym2.from_rel_prop, set.mem_set_of_eq],
    split,
    { rintro ⟨h, (rfl|rfl)⟩,
      { use [w', symm' h],
        rw sym2.eq_swap },
      { use [v', h] } },
    { simp_rw sym2.eq_iff,
      rintro ⟨u, h, (⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩;
      simp [h, symm' h], }
  end }

end default_undirected_edges

section has_simple_undirected_edges
variables (G : γ) {V : Type v} [has_simple_undirected_edges G V]

lemma edges_prop (v w : V) (e : sym2 V) : e ∈ edges G v w → e = ⟦(v, w)⟧ :=
edges_prop' v w e

@[simp]
lemma mem_edges_iff (v w : V) (e : sym2 V) : e ∈ edges G v w ↔ adj G v w ∧ e = ⟦(v, w)⟧ :=
begin
  rw ← nonempty_edges_iff_adj,
  split,
  { exact λ h, ⟨⟨e, h⟩, edges_prop G _ _ _ h⟩ },
  { rintro ⟨⟨e', h⟩, rfl⟩,
    have := edges_prop G _ _ _ h,
    rwa this at h, },
end

/-- For the `default_undirected_edges` instance, this can be proved by `refl`. -/
@[simp] lemma mem_edge_set {v w : V} : ⟦(v, w)⟧ ∈ edge_set G ↔ adj G v w :=
begin
  rw edge_set_eq,
  simp only [set.mem_Union, ←nonempty_edges_iff_adj],
  split,
  { rintro ⟨v', w', h⟩,
    use ⟦(v, w)⟧,
    have := edges_prop G v' w' ⟦(v, w)⟧ h,
    rw sym2.eq_iff at this,
    obtain (⟨rfl,rfl⟩|⟨rfl,rfl⟩) := this,
    { exact h, },
    { exact edges_symm G _ _ h, } },
  { rintro ⟨e, he⟩,
    refine sym2.ind (λ v' w' he, _) e he,
    rw ← edges_prop G v w ⟦(v', w')⟧ he,
    use [v, w, he], }
end

instance decidable_mem_edge_set [h : decidable_rel (adj G)] :
  decidable_pred ((∈ edge_set G) : sym2 V → Prop) :=
begin
  haveI := @sym2.from_rel.decidable_pred _ _ (adj_symm G) h,
  intro e,
  by_cases h : e ∈ sym2.from_rel (adj_symm G),
  { apply decidable.is_true,
    refine sym2.ind (λ v w h, _) e h,
    simpa using h, },
  { apply decidable.is_false,
    refine sym2.ind (λ v w h, _) e h,
    simpa using h, }
end

/--
Two vertices are adjacent iff there is an edge between them.  The
condition `v ≠ w` ensures they are different endpoints of the edge,
which is necessary since when `v = w` the existential
`∃ (e ∈ G.edge_set), v ∈ e ∧ w ∈ e` is satisfied by every edge
incident to `v`.
-/
lemma adj_iff_exists_edge' [is_adj_loopless G V] {v w : V} :
  adj G v w ↔ v ≠ w ∧ ∃ (e ∈ edge_set G), v ∈ e ∧ w ∈ e :=
begin
  refine ⟨λ _, ⟨ne_of_adj G ‹_›, ⟦(v,w)⟧, _⟩, _⟩,
  { simpa },
  { rintro ⟨hne, e, he, hv⟩,
    rw sym2.mem_and_mem_iff hne at hv,
    subst e,
    rwa mem_edge_set at he }
end

lemma adj_iff_exists_edge_coe {v w : V} : adj G v w ↔ ∃ (e : edge_set G), ↑e = ⟦(v, w)⟧ :=
by simp only [mem_edge_set, exists_prop, set_coe.exists, exists_eq_right, subtype.coe_mk]

lemma edge_other_ne [is_adj_loopless G V]
  {e : sym2 V} (he : e ∈ edge_set G) {v : V} (h : v ∈ e) : h.other ≠ v :=
begin
  erw [← sym2.other_spec h, sym2.eq_swap, mem_edge_set] at he,
  exact ne_of_adj G he,
end

instance edges_fintype [decidable_eq V] [fintype V] [decidable_rel (adj G)] :
  fintype (edge_set G) := subtype.fintype _

lemma incidence_set_eq' (v : V) :
  incidence_set G v = {e ∈ edge_set G | v ∈ e} :=
begin
  ext e,
  refine sym2.ind (λ v' w', _) e,
  simp only [incidence_set_eq, set.mem_Union, set.mem_sep_eq,
    sym2.mem_iff, mem_edges_iff, mem_edge_set, sym2.eq_iff],
  split,
  { rintro ⟨u, h, (⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩;
    simpa [adj_comm] using h, },
  { rintro ⟨h, (rfl|rfl)⟩,
    { use [w', h],
      simp, },
    { use [v', adj_symm' G h],
      simp, } }
end

instance decidable_mem_incidence_set [decidable_eq V] [h : decidable_rel (adj G)] (v : V) :
  decidable_pred (∈ incidence_set G v) :=
λ e, by { rw incidence_set_eq', apply and.decidable  }

/--
The `edge_set` of the graph as a `finset`.
-/
def edge_finset [decidable_eq V] [fintype V] [decidable_rel (adj G)] : finset (sym2 V) :=
set.to_finset (edge_set G)

@[simp] lemma mem_edge_finset [decidable_eq V] [fintype V] [decidable_rel (adj G)] (e : sym2 V) :
  e ∈ edge_finset G ↔ e ∈ edge_set G :=
set.mem_to_finset

@[simp] lemma edge_set_univ_card [decidable_eq V] [fintype V] [decidable_rel (adj G)] :
  (finset.univ : finset (edge_set G)).card = (edge_finset G).card :=
fintype.card_of_subtype (edge_finset G) (mem_edge_finset _)

end has_simple_undirected_edges

section maps

variables (G : γ) {V : Type*} [has_adj G V]
variables {γ' : Type*} (G' : γ') {V' : Type*} [has_adj G' V']

/--
A graph homomorphism is a map on vertex types that preserves the `has_adj` structure.

The notation `G →g G'` represents the type of graph homomorphisms.
-/
abbreviation hom := rel_hom (adj G : V → V → Prop) (adj G' : V' → V' → Prop)

/--
A graph embedding is an embedding `f` such that for vertices `v w : V`,
`adj G (f v) (f w) ↔ adj G v w `. Its image is an induced subgraph of G'.

The notation `G ↪g G'` represents the type of graph embeddings.
-/
abbreviation embedding := rel_embedding (adj G : V → V → Prop) (adj G' : V' → V' → Prop)

/--
A graph isomorphism is an bijective map on vertex sets that respects adjacency relations.

The notation `G ≃g G'` represents the type of graph isomorphisms.
-/
abbreviation iso := rel_iso (adj G : V → V → Prop) (adj G' : V' → V' → Prop)

infix ` →g ` : 50 := hom
infix ` ↪g ` : 50 := embedding
infix ` ≃g ` : 50 := iso

namespace hom
variables {G G'} (f : G →g G')

/-- The identity homomorphism from a graph to itself. -/
abbreviation id : G →g G := rel_hom.id (adj G : V → V → Prop)

lemma map_adj {v w : V} (h : adj G v w) : adj G' (f v) (f w) := f.map_rel' h

lemma apply_mem_neighbor_set {v w : V} (h : w ∈ neighbor_set G v) : f w ∈ neighbor_set G' (f v) :=
map_adj f h

/-- The map between neighbor sets induced by a homomorphism. -/
@[simps] def map_neighbor_set (v : V) (w : neighbor_set G v) : neighbor_set G' (f v) :=
⟨f w, f.apply_mem_neighbor_set w.property⟩

variables {γ'' : Type*} {G'' : γ'} {V'' : Type*} [has_adj G'' V'']
include V V' V''

/-- Composition of graph homomorphisms. -/
abbreviation comp (f' : G' →g G'') (f : G →g G') : G →g G'' := f'.comp f

@[simp] lemma coe_comp (f' : G' →g G'') (f : G →g G') : ⇑(f'.comp f) = f' ∘ f := rfl

end hom

namespace embedding
variables {G G'} (f : G ↪g G')
include V

/-- The identity embedding from a graph to itself. -/
abbreviation refl : G ↪g G := rel_embedding.refl _

/-- An embedding of graphs gives rise to a homomorphism of graphs. -/
abbreviation to_hom : G →g G' := f.to_rel_hom

lemma map_adj_iff {v w : V} : adj G' (f v) (f w) ↔ adj G v w := f.map_rel_iff

lemma apply_mem_neighbor_set_iff {v w : V} : f w ∈ neighbor_set G' (f v) ↔ w ∈ neighbor_set G v :=
map_adj_iff f

/-- A graph embedding induces an embedding of neighbor sets. -/
@[simps] def map_neighbor_set (v : V) : neighbor_set G v ↪ neighbor_set G' (f v) :=
{ to_fun := λ w, ⟨f w, f.apply_mem_neighbor_set_iff.mpr w.2⟩,
  inj' := begin
    rintros ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h,
    rw subtype.mk_eq_mk at h ⊢,
    exact f.inj' h,
  end }

variables {γ'' : Type*} {G'' : γ'} {V'' : Type*} [has_adj G'' V'']
include V' V''

/-- Composition of graph embeddings. -/
abbreviation comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' := f.trans f'

@[simp] lemma coe_comp (f' : G' ↪g G'') (f : G ↪g G') : ⇑(f'.comp f) = f' ∘ f := rfl

end embedding

namespace iso
variables {G G'} (f : G ≃g G')
include V

/-- The identity isomorphism of a graph with itself. -/
abbreviation refl : G ≃g G := rel_iso.refl _

/-- An isomorphism of graphs gives rise to an embedding of graphs. -/
abbreviation to_embedding : G ↪g G' := f.to_rel_embedding

/-- An isomorphism of graphs gives rise to a homomorphism of graphs. -/
abbreviation to_hom : G →g G' := f.to_embedding.to_hom

/-- The inverse of a graph isomorphism. --/
abbreviation symm : G' ≃g G := f.symm

lemma map_adj_iff {v w : V} : adj G' (f v) (f w) ↔ adj G v w := f.map_rel_iff

lemma apply_mem_neighbor_set_iff {v w : V} : f w ∈ neighbor_set G' (f v) ↔ w ∈ neighbor_set G v :=
map_adj_iff f

/-- A graph isomorphism induces an equivalence of neighbor sets. -/
@[simps] def map_neighbor_set (v : V) : neighbor_set G v ≃ neighbor_set G' (f v) :=
{ to_fun := λ w, ⟨f w, f.apply_mem_neighbor_set_iff.mpr w.2⟩,
  inv_fun := λ w, ⟨f.symm w, begin
    convert f.symm.apply_mem_neighbor_set_iff.mpr w.2,
    simp only [rel_iso.symm_apply_apply],
  end⟩,
  left_inv := λ w, by simp,
  right_inv := λ w, by simp }

lemma card_eq_of_iso [fintype V] [fintype V'] (f : G ≃g G') : fintype.card V = fintype.card V' :=
by convert (fintype.of_equiv_card f.to_equiv).symm

variables {γ'' : Type*} {G'' : γ'} {V'' : Type*} [has_adj G'' V'']
include V' V''

/-- Composition of graph isomorphisms. -/
abbreviation comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' := f.trans f'

@[simp] lemma coe_comp (f' : G' ≃g G'') (f : G ≃g G') : ⇑(f'.comp f) = f' ∘ f := rfl

end iso

end maps

end graph

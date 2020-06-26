/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller.
-/

--import data.equiv.basic
import combinatorics.graphs.sym2
--import combinatorics.graphs.multigraphs
import data.fintype.basic
import order.bounded_lattice
import tactic
open function (hiding graph)
--open equiv

namespace graph
universes u v

-- A link with vertex type α and edge type β represents a directed
-- path through a given edge.  Caveat: loop edges are directionless.
structure link (α : Type u) (β : Type v) :=
(src : α) (via : β) (dest : α)

namespace link
variables {α : Type u} {β : Type v}

def rev (x : link α β) : link α β := ⟨x.dest, x.via, x.src⟩

lemma rev.involutive : involutive (@link.rev α β) :=
begin intro x, cases x, simp [rev], end

@[simp] lemma rev_src (x : link α β) : x.rev.src = x.dest := rfl
@[simp] lemma rev_via (x : link α β) : x.rev.via = x.via := rfl
@[simp] lemma rev_dest (x : link α β) : x.rev.dest = x.src := rfl
@[simp] lemma rev_rev (x : link α β) : x.rev.rev = x := by cases x; simp only [link.rev, eq_self_iff_true, and_self]

-- Since we are modeling undirected graphs, two links correspond to
-- the same edge if they are the same up to orientation reversal.
def same_edge : link α β → link α β → Prop :=
λ x y, x = y ∨ x = y.rev

@[refl] def same_edge.refl (x : link α β) : same_edge x x := or.inl rfl

@[symm] def same_edge.symm {x y : link α β} (h : same_edge x y) : same_edge y x :=
begin cases h; rw h, right, rw link.rev_rev, end

@[trans] def same_edge.trans {x y z : link α β}
(xy : same_edge x y) (yz : same_edge y z) : same_edge x z :=
begin cases xy; cases yz; subst x; subst y; try {right, refl}, simp, end

end link

-- This is the type for multigraphs with vertex and edge sets that are
-- drawn from some given types.  Exposing the types lets you more
-- easily have labeled vertex and edge sets.
--
-- If you want to deal with graphs all with the same vertex type then
-- you might want to use subgraphs of some fixed multigraph.
--
-- The links field carries the edges and attaches them to the
-- vertices.  For non-loop edges, they come in pairs and represent the
-- two possible orientations of the edge.  For loop edges, there is
-- only a single link.
--
-- This definition is drawn from [Chou94].
--
-- [Chou94] Chou, Ching-Tsun. "A formal theory of undirected graphs in
-- Higher-Order Logic." (1994)
-- https://doi.org/10.1007/3-540-58450-1_40
structure multigraph (α : Type u) (β : Type v) :=
(vertices : set α) (links : set (link α β))
(link_src : link.src '' links ⊆ vertices)
(link_rev : link.rev '' links ⊆ links)
(efficient : ∀ ⦃x y : link α β⦄, x ∈ links → y ∈ links → x.via = y.via → link.same_edge x y)

-- The set of edges
def multigraph.edges {α : Type u} {β : Type v} (g : multigraph α β) : set β := link.via '' g.links

-- We only required `link.src '' links ⊆ vertices` since `link.dest '' links ⊆ vertices` follows from the axioms. 
lemma multigraph.link_dest {α : Type u} {β : Type v} (g : multigraph α β) : link.dest '' g.links ⊆ g.vertices :=
begin
  rintros v ⟨x, xel, xdest⟩,
  rw ←xdest,
  exact g.link_src ⟨x.rev, g.link_rev ⟨x, xel, rfl⟩, rfl⟩,
end

-- We only required `link.rev '' links ⊆ links` since `link.rev` is an involution.
lemma multigraph.link_rev_eq {α : Type u} {β : Type v} (g : multigraph α β) : link.rev '' g.links = g.links :=
begin
  rw set.subset.antisymm_iff,
  split,
  exact g.link_rev,
  intros x xel,
  use [x.rev, g.link_rev ⟨x, xel, rfl⟩],
  simp only [link.rev_rev],
end

namespace multigraph
variables {α : Type u} {β : Type v}

def links_between (g : multigraph α β) (v w : α) : set (link α β) := {x : link α β | x ∈ g.links ∧ x.src = v ∧ x.dest = w}

lemma links_between_subset (g : multigraph α β) (v w : α) : g.links_between v w ⊆ g.links :=
λ x h, h.1

lemma links_between_rev_iff (g : multigraph α β) (v w : α) (x : link α β)
: x ∈ g.links_between v w ↔ x.rev ∈ g.links_between w v :=
begin
  tidy,
  refine g.link_rev ⟨x, _, rfl⟩, assumption,
  rw ←link.rev_rev x,
  refine g.link_rev ⟨x.rev, _, rfl⟩, assumption,
end

lemma links_between_rev_eq (g : multigraph α β) (v w : α)
: link.rev '' g.links_between v w = g.links_between w v :=
begin
  ext x,
  split,
  rintros ⟨y,h,rfl⟩,
  rwa ←links_between_rev_iff,
  intro h,
  use x.rev,
  simp [links_between_rev_iff, h],
end

-- A Type-valued predicate that a given edge is incident to a given
-- vertex.  (Note: the definition is *already* a subsingleton due to
-- the multigraph axioms, so this does not need to be a `trunc`.)
def edge_incident (g : multigraph α β) (e : β) (v : α) : Type (max u v) :=
{x : link α β // x ∈ g.links ∧ x.via = e ∧ x.src = v}

instance edge_incident.subsingleton {g : multigraph α β} (e : β) (v : α) : subsingleton (edge_incident g e v) :=
begin
  constructor,
  rintros ⟨x, xel, xvia, xsrc⟩ ⟨y, yel, yvia, ysrc⟩,
  have h := g.efficient xel yel (by cc),
  cases x, cases y,
  tidy,
end

-- The link at an edge leaving a particular vertex.
def edge_link_out (g : multigraph α β) {e : β} {v : α} (h : g.edge_incident e v) : link α β := h.1

-- The link at an edge entering a particular vertex.
def edge_link_in (g : multigraph α β) {e : β} {v : α} (h : g.edge_incident e v) : link α β :=
(g.edge_link_out h).rev

-- Get the vertex opposite a given vertex over a given edge.
def edge_opp (g : multigraph α β) {e : β} {v : α} (h : g.edge_incident e v) : α :=
(g.edge_link_out h).dest

section edge_link_properties
variables {g : multigraph α β} {e : β} {v : α} (h : g.edge_incident e v)

lemma edge_link_out.well_defined_in_links : g.edge_link_out h ∈ g.links := h.2.1

@[simp]
lemma edge_link_out.well_defined_src : (g.edge_link_out h).src = v := h.2.2.2

@[simp]
lemma edge_link_out.well_defined_via : (g.edge_link_out h).via = e := h.2.2.1

lemma edge_link_out.uniqueness {x : link α β} (hx : x ∈ g.links) (hs : x.src = v) (hv : x.via = e) :
x = g.edge_link_out h :=
begin
  have key : h = ⟨x, hx, hv, hs⟩ := subsingleton.elim _ _,
  rw key,
  simp only [edge_link_out],
end

lemma edge_link_out_in_links_between : g.edge_link_out h ∈ g.links_between v (g.edge_opp h) :=
by tidy

end edge_link_properties


def edges_between (g : multigraph α β) (v w : α) : set β := link.via '' g.links_between v w

lemma edges_between_subset_edge_set (g : multigraph α β) (v w : α) : g.edges_between v w ⊆ g.edges :=
begin
  rintros e ⟨x, ⟨xel, h⟩, xvia⟩,
  exact ⟨x, xel, xvia⟩,
end

lemma edges_between_reversible (g : multigraph α β) : ∀ v w, g.edges_between v w = g.edges_between w v :=
begin
  intros v w,
  dunfold edges_between,
  rw ←links_between_rev_eq g v w,
  rw set.image_image,
  simp only [link.rev_via],
end

lemma edges_have_ends {g : multigraph α β} {x y x' y' : α} {e : β}
(h : e ∈ g.edges_between x y) (h' : e ∈ g.edges_between x' y') :
(x = x' ∧ y = y') ∨ (x = y' ∧ y = x') :=
begin
  tidy,
  cases g.efficient h_h_left_left h'_h_left_left h_h_right,
  tidy, right, cases h_w, cases h'_w, simp only [link.rev] at h, tidy,
end

-- A trivial lemma with the formulation of multigraphs, but perhaps it is nice to explicitly specify this property.
lemma edge_has_link (g : multigraph α β) {e : β} (h : e ∈ g.edges) : ∃ (x : link α β), x ∈ g.links ∧ x.via = e := h

def links_out (g : multigraph α β) (v : α) : set (link α β) := {x : link α β | x ∈ g.links ∧ x.src = v}

def links_in (g : multigraph α β) (v : α) : set (link α β) := {x : link α β | x ∈ g.links ∧ x.dest = v}

lemma links_in_is_rev_links_out (g : multigraph α β) (v : α) : g.links_in v = link.rev '' g.links_out v :=
begin
  ext,
  dsimp only [links_out, links_in],
  split,
  intro h, use x.rev, use g.link_rev ⟨x, h.1, rfl⟩, rw ←h.2, simp, simp,
  rintros ⟨x',h,rfl⟩, use g.link_rev ⟨x', h.1, rfl⟩, rw ←h.2, simp,
end

lemma links_between_subset_links_out (g : multigraph α β) (v w : α) : g.links_between v w ⊆ g.links_out v :=
by tidy

lemma edge_link_out_in_links_out (g : multigraph α β) {v : α} {e : β} (h : g.edge_incident e v) : g.edge_link_out h ∈ g.links_out v :=
by tidy

-- The set of edges incident to a given vertex.  You might want
-- `links_at` if you are traversing a graph.  This doubles as the
-- incidence relation between vertices and edges.
def incident (g : multigraph α β) (v : α) : set β := link.via '' links_out g v

-- The set of vertices adjacent to a given vertex. This doubles as the
-- adjacency relation between vertices.
def adjacent (g : multigraph α β) (v : α) : set α := link.dest '' links_out g v

noncomputable
def edge_link (g : multigraph α β) {e : β} (h : e ∈ g.edges) : link α β := classical.some h

noncomputable
def edge_incident_from_incident (g : multigraph α β) {e : β} {v : α} (h : e ∈ g.incident v) : g.edge_incident e v :=
begin
  let x := classical.some h,
  have p := classical.some_spec h,
  exact ⟨x, p.1.1, p.2, p.1.2⟩,
end

noncomputable
def link_between_from_edge_between (g : multigraph α β) {e : β} {v w : α} (h : e ∈ g.edges_between v w) : g.links_between v w :=
begin
  let x := classical.some h,
  have p := classical.some_spec h,
  exact ⟨x, p.1⟩,
end

-- If you want the computable version, use `edge_opp`.  Gives the
-- vertex opposite a given vertex across an edge.
noncomputable
def edge_opp' {g : multigraph α β} (v : α) {e} (h : e ∈ g.incident v) : α :=
g.edge_opp (g.edge_incident_from_incident h)

section noncomputable_properties

@[simp]
lemma edge_link_via (g : multigraph α β) {e : β} (h : e ∈ g.edges) : (g.edge_link h).via = e :=
(classical.some_spec h).2

@[simp]
def edge_incident_from_incident_via (g : multigraph α β) {e : β} {v : α} (h : e ∈ g.incident v) :
(g.edge_link_out (g.edge_incident_from_incident h)).via = e :=
by simp

@[simp]
def link_between_from_edge_between_via (g : multigraph α β) {e : β} {v w : α} (h : e ∈ g.edges_between v w) :
(g.link_between_from_edge_between h).val.via = e :=
(classical.some_spec h).2

end noncomputable_properties


end multigraph


section subgraphs
variables {α : Type u} {β : Type v}
open multigraph

-- `subgraph g` is the type of all subgraphs of a given multigraph.
-- These are not multigraphs per se, but they can be converted to
-- multigraphs using `subgraph.to_graph`.  There is an instance to
-- coerce subgraphs to multigraphs.
structure subgraph (g : multigraph α β) :=
(vertices : set α) (edges : set β)
(subset_vertices : vertices ⊆ g.vertices)
(subset_edges : edges ⊆ g.edges)
(has_verts : ∀ {e}, e ∈ edges → ∀ {x : link α β}, x ∈ g.links → e = x.via → x.src ∈ vertices)

section subgraph_props
variables {g : multigraph α β} (g' : subgraph g)

-- In this section, we add the properties of a multigraph.

def subgraph.links : set (link α β) := {x : link α β | x ∈ g.links ∧ x.via ∈ g'.edges}

lemma subgraph.link_src : link.src '' g'.links ⊆ g'.vertices :=
begin
  rintros v ⟨h, ⟨he, hv⟩, rfl⟩,
  exact g'.has_verts hv he rfl,
end

lemma subgraph.link_rev : link.rev '' g'.links ⊆ g'.links :=
begin
  rintros _ ⟨x, ⟨he, hv⟩, rfl⟩,
  use g.link_rev ⟨x, he, rfl⟩,
  rwa link.rev_via,
end

lemma subgraph.efficient : ∀ ⦃x y : link α β⦄, x ∈ g'.links → y ∈ g'.links → x.via = y.via → link.same_edge x y :=
begin
  rintros x y ⟨xe, xv⟩ ⟨ye, yv⟩ vias,
  exact g.efficient xe ye vias,
end

end subgraph_props

-- Construct a multigraph from the given subgraph.
def subgraph.to_graph {g : multigraph α β} (g' : subgraph g) : multigraph α β := {
  vertices := g'.vertices,
  links := g'.links,
  link_src := g'.link_src,
  link_rev := g'.link_rev,
  efficient := g'.efficient
}

instance subgraph.to_graph.lift (g : multigraph α β) : has_lift (subgraph g) (multigraph α β) :=
⟨subgraph.to_graph⟩

section from_relations

-- Use a symmetric relation to select a subgraph of a given multigraph.
def subgraph.from_relation (g : multigraph α β) {r : α → α → Prop} (h : symmetric r) : subgraph g := {
  vertices := g.vertices,
  edges := link.via '' {x : link α β | x ∈ g.links ∧ r x.src x.dest},
  subset_vertices := set.subset.refl _,
  subset_edges := begin
    rintros _ ⟨x, ⟨hl, _⟩, rfl⟩,
    exact ⟨x, hl, rfl⟩,
  end,
  has_verts := begin
    rintros _ _ x hx _,
    exact g.link_src ⟨x, hx, rfl⟩,
  end
}

--set_option trace.class_instances true
lemma subgraph.from_relation_prop (g : multigraph α β) {r : α → α → Prop} (h : symmetric r) :
∀ (v w : α), multigraph.adjacent ↑(subgraph.from_relation g h) v w :=
begin
  have g' := subgraph.from_relation g h,
  have g'' := (g'.to_graph : multigraph α β),
  have h''' := (↑g' : multigraph α β),
end

end from_relations

@[ext]
def subgraph.ext {g : multigraph α β} (x y : subgraph g) : x.vertices = y.vertices → x.edges = y.edges → x = y :=
begin intros hv he, cases x, cases y, congr, exact hv, exact he, end

section subgraph_lattice

variables {g : multigraph α β}

def subgraph.is_subgraph (x y : subgraph g) := x.vertices ⊆ y.vertices ∧ x.edges ⊆ y.edges

def subgraph.is_ssubgraph (x y : subgraph g) := x.is_subgraph y ∧ (x.vertices ⊂ y.vertices ∨ x.edges ⊂ y.edges)

def subgraph.union (x y : subgraph g) : subgraph g := {
  vertices := x.vertices ∪ y.vertices,
  edges := x.edges ∪ y.edges,
  subset_vertices := set.union_subset x.subset_vertices y.subset_vertices,
  subset_edges := set.union_subset x.subset_edges y.subset_edges,
  has_verts := begin
    rintros e h l lel rfl,
    cases h with h h,
    exact or.inl (x.has_verts h lel rfl),
    exact or.inr (y.has_verts h lel rfl),
  end
}

def subgraph.inter (x y : subgraph g) : subgraph g := {
  vertices := x.vertices ∩ y.vertices,
  edges := x.edges ∩ y.edges,
  subset_vertices := set.subset.trans (set.inter_subset_left _ _) x.subset_vertices,
  subset_edges := set.subset.trans (set.inter_subset_left _ _) x.subset_edges,
  has_verts := begin
    rintros e h l lel rfl,
    exact ⟨x.has_verts h.1 lel rfl, y.has_verts h.2 lel rfl⟩,
  end
}

instance : has_subset (subgraph g) := ⟨subgraph.is_subgraph⟩
instance : has_ssubset (subgraph g) := ⟨subgraph.is_ssubgraph⟩
instance : has_union (subgraph g) := ⟨subgraph.union⟩
instance : has_inter (subgraph g) := ⟨subgraph.inter⟩

def subgraph.top : subgraph g := {
  vertices := g.vertices,
  edges := g.edges,
  subset_vertices := set.subset.refl _,
  subset_edges := set.subset.refl _,
  has_verts := by rintros e h l lel rfl; exact g.link_src ⟨l, lel, rfl⟩
}
def subgraph.bot : subgraph g := {
  vertices := ∅,
  edges := ∅,
  subset_vertices := set.empty_subset _,
  subset_edges := set.empty_subset _,
  has_verts := by rintros e h l lel rfl; tauto
}

instance : bounded_lattice (subgraph g) := {
  top := subgraph.top,
  bot := subgraph.bot,
  le := subgraph.is_subgraph,
  le_refl := by intro a; exact ⟨set.subset.refl _, set.subset.refl _⟩,
  le_trans := by intros x y z hxy hyz;
                 exact ⟨set.subset.trans hxy.1 hyz.1,
                        set.subset.trans hxy.2 hyz.2⟩,
  le_antisymm := begin
    intros x y hxy hyx,
    cases x, cases y, congr,
    exact set.subset.antisymm hxy.1 hyx.1,
    exact set.subset.antisymm hxy.2 hyx.2,
  end,
  le_top := λ x, ⟨x.subset_vertices, x.subset_edges⟩,
  bot_le := by intro a; split; exact set.empty_subset _,
  sup := subgraph.union,
  inf := subgraph.inter,
  sup_le := by intros x y z hxy hyz;
               exact ⟨set.union_subset hxy.1 hyz.1, set.union_subset hxy.2 hyz.2⟩,
  le_sup_left :=
    by intros x y;
       exact ⟨set.subset_union_left x.vertices y.vertices, set.subset_union_left x.edges y.edges⟩,
  le_sup_right :=
    by intros x y;
       exact ⟨set.subset_union_right x.vertices y.vertices, set.subset_union_right x.edges y.edges⟩,
  le_inf :=
    by intros x y z hxy hyz; exact ⟨set.subset_inter hxy.1 hyz.1, set.subset_inter hxy.2 hyz.2⟩,
  inf_le_left :=
    by intros x y;
       exact ⟨set.inter_subset_left x.vertices y.vertices, set.inter_subset_left x.edges y.edges⟩,
  inf_le_right :=
    by intros x y;
       exact ⟨set.inter_subset_right x.vertices y.vertices, set.inter_subset_right x.edges y.edges⟩,
}

end subgraph_lattice


end subgraphs

namespace multigraph
variables {α : Type u} {β : Type v}

-- Note: given [decidable_pred g.links], the following will give [fintype g.links].
instance link.fintype [fintype α] [fintype β] : fintype (link α β) :=
begin
  have equiv : link α β ≃ α × β × α, {
    use λ x, ⟨x.src, x.via, x.dest⟩,
    use λ z, ⟨z.1, z.2.1, z.2.2⟩,
    rintro ⟨s, v, d⟩, simp,
    rintro ⟨s, v, d⟩, simp,
  },
  exact fintype.of_equiv _ equiv.symm,
end

-- TODO not sure if this (or something close to it) is possible
-- instance fintype.links_from_verts_and_edges (g : multigraph α β) [fintype g.vertices] [fintype g.edges] [decidable_pred g.links] : fintype g.links := sorry

instance fintype.edges_from_links (g : multigraph α β) [fintype g.links] [decidable_eq β] : fintype g.edges :=
begin
  let f : g.links → g.edges := begin
    rintro ⟨x,xel⟩,
    exact ⟨x.via, x, xel, rfl⟩,
  end,
  have h : surjective f, {
    rintro ⟨e, ⟨x, xel, h⟩⟩,
    use [x, xel],
    simpa only [f, subtype.mk_eq_mk], 
  },
  exact fintype.of_surjective f h,
end


end multigraph


section complete_graphs

-- This is the non-simple complete graph with vertex set given by the
-- type α. There is exactly one edge between every pair of vertices
-- (including self-loops at each vertex).
def complete_graph' (α : Type u) : multigraph α (sym2.sym2 α) := {
  vertices := set.univ,
  links := {x | x.via = ⟦(x.src, x.dest)⟧},
  link_src := set.subset_univ _,
  link_rev := begin
    rintros _ ⟨a,b,rfl⟩,
    rw set.mem_set_of_eq at b ⊢,
    rw [link.rev_via, link.rev_src, link.rev_dest],
    rw b,
    exact sym2.eq_swap,
  end,
  efficient := begin
    rintros x y xel yel hvia,
    rw set.mem_set_of_eq at xel yel,
    rw [←hvia, xel] at yel,
    cases sym2.eq yel; cases x; cases y; dsimp [link.same_edge, link.rev]; tidy,
  end,
}


def from_relation {α : Type u} (r : α → α → Prop) : multigraph α (sym2.sym2 α) :=
begin
  let g := complete_graph' α,
  let g' : subgraph g
end

end complete_graphs

end graph



-- structure graph (vertices : Type u) extends multigraph vertices :=
-- (single_edge : injective ends)
-- (loopless : ∀ e : edges, ¬(ends e).is_diag)

-- variables {vertices : Type u}

-- def to_multigraph (g : graph vertices) : multigraph vertices :=
-- ⟨g.edges, g.ends⟩

-- def from_relation {α : Type u} {r : α → α → Prop} (h₁ : symmetric r) (h₂ : irreflexive r) : graph α :=
-- {
--   edges := {z : sym2 α // ∃ x y, r x y ∧ z = sym2.mk x y},
--   ends := λ z, z.val,
--   single_edge :=
--     begin
--       rintros ⟨z₁,x₁,y₁,hr₁,hz₁⟩ ⟨z₂,h₂,x₂,y₂,hr₂,hz₂⟩,
--       simp,
--     end,
--   loopless :=
--     begin
--       rintro ⟨z,x,y,hr,hz⟩ abs,
--       dsimp at abs,
--       rw hz at abs,
--       have heq := sym2.mk_is_diag abs,
--       rw heq at hr,
--       exact h₂ y hr,
--     end
-- }

-- def graph.adj {vertices : Type u} (g : graph vertices) (x y : vertices) : Prop := g.to_multigraph.adj x y

-- lemma adj_of_from_relation {α : Type u} {r : α → α → Prop} (h₁ : symmetric r) (h₂ : irreflexive r)
-- : ∀ x y, r x y ↔ (graph.from_relation h₁ h₂).adj x y :=
-- begin
--   intros x y,
--   split,
--   intro hr,
--   refine ⟨⟨⟨sym2.mk x y, x, y, hr, rfl⟩, rfl⟩⟩,
--   rintro ⟨⟨⟨a,b,c,d,e⟩,f⟩⟩,
--   dsimp [from_relation] at f,
--   rw e at f,
--   have h := sym2.eq f,
--   cases h,
--   rw [h.1,h.2] at d, exact d,
--   rw [h.1,h.2] at d, exact h₁ d,
-- end


-- def complete_graph (α : Type u) [decidable_eq α] : graph α :=
-- @graph.from_relation _ (λ x y, x ≠ y) (λ x y h, h.symm) (λ x : α, by simp)

-- def finite_complete_graph (n : ℕ) := complete_graph (fin n)

-- --
-- -- Finite graphs
-- --

-- instance finite_edge_set [fintype vertices] (g : graph vertices) : fintype g.edges := sorry

-- def graph.nverts [fintype vertices] (g : graph vertices) := fintype.card vertices
-- def graph.nedges [fintype vertices] (g : graph vertices) := fintype.card g.edges

-- end graph

import order.bounded_lattice
import tactic
import data.sym2
open function (hiding graph)
open sym2 (sym2)

-- This definition is drawn from [Chou94].
--
-- [Chou94] Chou, Ching-Tsun. "A formal theory of undirected graphs in
-- Higher-Order Logic." (1994)
-- https://doi.org/10.1007/3-540-58450-1_40

-- Doczkal, Christian and Pous, Damien. (2019). Graph Theory in Coq: Minors, Treewidth, and Isomorphisms

namespace graph

universes u v w

-- A link with vertex type α and edge type β represents a directed
-- path through a given edge.  Caveat: loop edges are directionless.
structure link (α : Type u) (β : Type v) :=
(src : α) (via : β) (dest : α)

namespace link
variables {α α' : Type u} {β β' : Type v}

def rev (x : link α β) : link α β := ⟨x.dest, x.via, x.src⟩

def ends (x : link α β) : sym2 α := ⟦(x.src, x.dest)⟧

def induce (f_v : α → α') (f_e : β → β') (x : link α β) := link.mk (f_v x.src) (f_e x.via) (f_v x.dest)

lemma rev.involutive : involutive (@link.rev α β) :=
begin intro x, cases x, simp [rev], end

@[simp] lemma rev_src (x : link α β) : x.rev.src = x.dest := rfl
@[simp] lemma rev_via (x : link α β) : x.rev.via = x.via := rfl
@[simp] lemma rev_dest (x : link α β) : x.rev.dest = x.src := rfl
@[simp] lemma rev_rev (x : link α β) : x.rev.rev = x :=
by { cases x, simp only [link.rev, eq_self_iff_true, and_self] }

@[simp] lemma rev_ends (x : link α β) : x.rev.ends = x.ends :=
sym2.eq_swap

@[simp] lemma struct_simp (x : link α β) :
{link . src := x.src, via := x.via, dest := x.dest} = x :=
by { cases x, simp }

@[simp]
lemma induce_id (x : link α β) : link.induce id id x = x := by {cases x, simp [link.induce], }

lemma induce_functorial {α' : Type*} {β' : Type*} {α'' : Type*} {β'' : Type*}
(f_v : α → α') (f_e : β → β') (f_v' : α' → α'') (f_e' : β' → β'') (x : link α β) :
induce (f_v' ∘ f_v) (f_e' ∘ f_e) x = induce f_v' f_e' (induce f_v f_e x) :=
by { cases x, simp [induce], }


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

namespace link
variables {α : Type*} {β : Type*}

instance from_subtypes (s : set α) (t : set β) :
has_coe (link s t) (link α β) :=
⟨(λ x, link.mk x.src x.via x.dest)⟩

instance from_edge_subtype (t : set β) :
has_coe (link α t) (link α β) :=
⟨(λ x, link.mk x.src x.via x.dest)⟩


namespace from_subtypes
variables (s : set α) (t : set β)

@[norm_cast] lemma lift_rev (x : link s t) : (x : link α β).rev = x.rev := rfl
@[norm_cast] lemma lift_via (x : link s t) : (x : link α β).via = x.via := rfl
@[norm_cast] lemma lift_src (x : link s t) : (x : link α β).src = x.src := rfl
@[norm_cast] lemma lift_dest (x : link s t) : (x : link α β).dest = x.dest := rfl

@[simp] lemma lift_rev' (x : link s t) : ↑(x.rev) = (x : link α β).rev := rfl
@[simp] lemma lift_via' (x : link s t) : ↑(x.via) = (x : link α β).via := rfl
@[simp] lemma lift_src' (x : link s t) : ↑(x.src) = (x : link α β).src := rfl
@[simp] lemma lift_dest' (x : link s t) : ↑(x.dest) = (x : link α β).dest := rfl

@[simp, norm_cast] lemma lift_subtype_eq (x y : link s t) :
(↑x : link α β) = ↑y ↔ x = y :=
begin
  unfold_coes,
  split,
  intro,
  cases x, cases y,
  simp only [subtype.ext] at a,
  repeat {rw ←subtype.ext at a},
  simp only [a],
  tauto,
  intro h, rw h,
end

@[simp] lemma lift_struct (a a' : s) (b : t) :
(↑{link . src := a, via := b, dest := a'} : link α β) = {src := ↑a, via := ↑b, dest := ↑a'} := rfl

@[simp, norm_cast] lemma same_edge_lift (x y : link s t) : same_edge (x : link α β) y ↔ same_edge x y :=
begin
  dsimp [same_edge],
  rw lift_rev,
  repeat { rw lift_subtype_eq },
end

end from_subtypes

namespace from_edge_subtype
variables (t : set β)

@[norm_cast] lemma lift_rev (x : link α t) : (x : link α β).rev = x.rev := rfl
@[norm_cast] lemma lift_via (x : link α t) : (x : link α β).via = x.via := rfl
@[norm_cast] lemma lift_src (x : link α t) : (x : link α β).src = x.src := rfl
@[norm_cast] lemma lift_dest (x : link α t) : (x : link α β).dest = x.dest := rfl

@[simp] lemma lift_rev' (x : link α t) : ↑(x.rev) = (x : link α β).rev := rfl
@[simp] lemma lift_via' (x : link α t) : ↑(x.via) = (x : link α β).via := rfl
@[simp] lemma lift_src' (x : link α t) : x.src = (x : link α β).src := rfl
@[simp] lemma lift_dest' (x : link α t) : x.dest = (x : link α β).dest := rfl

@[simp, norm_cast] lemma lift_subtype_eq (x y : link α t) :
(↑x : link α β) = ↑y ↔ x = y :=
begin
  unfold_coes,
  split,
  intro,
  cases x, cases y,
  simp only [subtype.ext] at a,
  repeat {rw ←subtype.ext at a},
  simp only [a],
  tauto,
  intro h, rw h,
end

@[simp, norm_cast] lemma same_edge_lift (x y : link α t) : same_edge (x : link α β) y ↔ same_edge x y :=
begin
  dsimp [same_edge],
  rw lift_rev,
  repeat { rw lift_subtype_eq },
end

end from_edge_subtype

end link

-- This is a typeclass indicating that the terms of a given type
-- consist of (multi)graphs.  The class provides the projections for
-- the vertex and edge sets of the graph.
--
-- The way in which edges are attached to the vertices is given by a
-- set of links.  For non-loop edges, links come in pairs,
-- representing the two possible orientations for the edge.  Loop
-- edges only have a single corresponding link.
--
-- If you want to deal with graphs all with the same underlying vertex
-- type, then you might consider using subgraphs of some fixed
-- multigraph.
class multigraphs (α : Type*) :=
(vertices : α → Type u)
(edges : α → Type v)
(links : Π (G : α), set (link (vertices G) (edges G)))
(link_rev : Π {G : α}, link.rev '' links G ⊆ links G)
(all_edges : Π {G : α}, ∀ e, ∃ x, x ∈ links G ∧ link.via x = e)
(efficient : Π {G : α}, ∀ ⦃x y⦄, x ∈ links G → y ∈ links G →
                        link.via x = link.via y → link.same_edge x y)

namespace multigraphs
variables {α : Type*} [multigraphs α] (G : α)

abbreviation link_type := link (vertices G) (edges G)

lemma link_rev_eq : link.rev '' links G = links G :=
begin
  rw set.subset.antisymm_iff,
  split,
  exact link_rev,
  intros x xel,
  use [x.rev, link_rev ⟨x, xel, rfl⟩],
  rw link.rev_rev,
end

def links_between (v w : vertices G) : set (link_type G) := {x | x ∈ links G ∧ x.src = v ∧ x.dest = w}

lemma links_between_subset (v w : vertices G) : links_between G v w ⊆ links G :=
λ x h, h.1

lemma links_between_rev_iff (v w : vertices G) (x : link_type G) :
x ∈ links_between G v w ↔ x.rev ∈ links_between G w v :=
begin
  tidy,
  refine link_rev ⟨x, _, rfl⟩, assumption,
  rw ←link.rev_rev x,
  refine link_rev ⟨x.rev, _, rfl⟩, assumption,
end

lemma links_between_rev_eq (v w : vertices G) :
link.rev '' links_between G v w = links_between G w v :=
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
-- vertex.  (Note: the definition is already a subsingleton due to
-- the multigraph axioms, so this does not need to be a `trunc`.)
def edge_incident (e : edges G) (v : vertices G)  :=
{x // x ∈ links G ∧ link.via x = e ∧ link.src x = v}

instance edge_incident.subsingleton (e : edges G) (v : vertices G) :
subsingleton (edge_incident G e v) :=
begin
  constructor,
  rintros ⟨x, xel, xvia, xsrc⟩ ⟨y, yel, yvia, ysrc⟩,
  have h := efficient xel yel (by cc),
  cases x, cases y,
  tidy,
end

-- The link at an edge leaving a particular vertex.
def edge_link_out {e : edges G} {v : vertices G} (h : edge_incident G e v) : link_type G :=
h.1

-- The link at an edge entering a particular vertex.
def edge_link_in {e : edges G} {v : vertices G} (h : edge_incident G e v) : link_type G :=
(edge_link_out G h).rev

-- Get the vertex opposite a given vertex over a given edge.
def edge_opp {e : edges G} {v : vertices G} (h : edge_incident G e v) : vertices G :=
(edge_link_out G h).dest


section edge_link_properties
variables {e : edges G} {v : vertices G} (h : edge_incident G e v)

lemma edge_link_out.well_defined_in_links : edge_link_out G h ∈ links G := h.2.1

@[simp]
lemma edge_link_out.well_defined_src : (edge_link_out G h).src = v := h.2.2.2

@[simp]
lemma edge_link_out.well_defined_via : (edge_link_out G h).via = e := h.2.2.1

lemma edge_link_out.uniqueness {x : link_type G} (hx : x ∈ links G) (hs : x.src = v) (hv : x.via = e) :
x = edge_link_out G h :=
begin
  have key : h = ⟨x, hx, hv, hs⟩ := subsingleton.elim _ _,
  rw key,
  simp only [edge_link_out],
end

lemma edge_link_out_in_links_between : edge_link_out G h ∈ links_between G v (edge_opp G h) :=
by tidy

end edge_link_properties


def edges_between (v w : vertices G) : set (edges G) := link.via '' links_between G v w

lemma edges_between_symm (v w : vertices G) : edges_between G v w = edges_between G w v :=
begin
  dunfold edges_between,
  rw ←links_between_rev_eq G v w,
  rw set.image_image,
  simp only [link.rev_via],
end

lemma edges_have_ends {x y x' y' : vertices G} {e : edges G}
(h : e ∈ edges_between G x y) (h' : e ∈ edges_between G x' y') :
(x = x' ∧ y = y') ∨ (x = y' ∧ y = x') :=
begin
  tidy,
  cases efficient h_h_left_left h'_h_left_left h_h_right,
  tidy, right, cases h_w, cases h'_w, simp only [link.rev] at h, tidy,
end

-- The links leaving a particular vertex.
def links_out (v : vertices G) : set (link_type G) := {x | x ∈ links G ∧ x.src = v}

-- The links entering a particular vertex.
def links_in (v : vertices G) : set (link_type G) := {x | x ∈ links G ∧ x.dest = v}

lemma links_in_is_rev_links_out (v : vertices G) : links_in G v = link.rev '' links_out G v :=
begin
  ext,
  dsimp only [links_out, links_in],
  split,
  intro h, use x.rev, use link_rev ⟨x, h.1, rfl⟩, rw ←h.2, simp, simp,
  rintros ⟨x',h,rfl⟩, use link_rev ⟨x', h.1, rfl⟩, rw ←h.2, simp,
end

lemma links_between_subset_links_out (v w : vertices G) : links_between G v w ⊆ links_out G v :=
by tidy

lemma edge_link_out_in_links_out {v : vertices G} {e : edges G} (h : edge_incident G e v) : edge_link_out G h ∈ links_out G v :=
by tidy

-- The set of edges incident to a given vertex.  You might want
-- `links_at` if you are traversing a graph.  This doubles as the
-- incidence relation between vertices and edges.
def incident (v : vertices G) : set (edges G) := link.via '' links_out G v

-- The set of vertices adjacent to a given vertex. This doubles as the
-- adjacency relation between vertices.
def adjacent (v : vertices G) : set (vertices G) := link.dest '' links_out G v


noncomputable
def edge_link (e : edges G) : link_type G := classical.some (all_edges e)

noncomputable
def edge_incident_from_incident {e : edges G} {v : vertices G} (h : e ∈ incident G v) : edge_incident G e v :=
begin
  let x := classical.some h,
  have p := classical.some_spec h,
  exact ⟨x, p.1.1, p.2, p.1.2⟩,
end

noncomputable
def link_between_from_edge_between {e : edges G} {v w : vertices G} (h : e ∈ edges_between G v w) : links_between G v w :=
begin
  let x := classical.some h,
  have p := classical.some_spec h,
  exact ⟨x, p.1⟩,
end

-- If you want the computable version, use `edge_opp`.  Gives the
-- vertex opposite a given vertex across an edge.
noncomputable
def edge_opp' (v : vertices G) {e : edges G} (h : e ∈ incident G v) : vertices G :=
edge_opp G (edge_incident_from_incident G h)

section noncomputable_properties

@[simp]
lemma edge_link_via (e : edges G) : (edge_link G e).via = e :=
(classical.some_spec (all_edges e)).2

@[simp]
def edge_incident_from_incident_via {e : edges G} {v : vertices G} (h : e ∈ incident G v) :
(edge_link_out G (edge_incident_from_incident G h)).via = e :=
by simp

@[simp]
def link_between_from_edge_between_via {e : edges G} {v w : vertices G} (h : e ∈ edges_between G v w) :
(link_between_from_edge_between G h).val.via = e :=
(classical.some_spec h).2

end noncomputable_properties


end multigraphs

open multigraphs

structure subgraph {α : Type*} [multigraphs α] (G : α) :=
(vertices' : set (vertices G))
(edges' : set (edges G))
(has_verts : ∀ ⦃x⦄, x ∈ links G → link.via x ∈ edges' →
             link.src x ∈ vertices')

namespace subgraph
variables {α : Type*} [multigraphs α] {G : α}

instance to_multigraph : multigraphs (subgraph G) :=
{ vertices := λ G', vertices' G',
  edges := λ G', edges' G',
  links := λ G', {x | ↑x ∈ links G},
  link_rev := begin
    rintros G' _ ⟨x, xel, rfl⟩,
    rw set.mem_set_of_eq at xel ⊢,
    dsimp,
    exact link_rev ⟨↑x, xel, rfl⟩,
  end,
  all_edges := begin
    rintros G' ⟨e, eel⟩,
    rcases all_edges e with ⟨x, xel, rfl⟩,
    have xsrc := has_verts G' xel eel,
    have xdest := has_verts G' (link_rev ⟨x, xel, rfl⟩) eel,
    use link.mk ⟨x.src, xsrc⟩ ⟨x.via, eel⟩ ⟨x.dest, xdest⟩,
    simpa,
  end,
  efficient := begin
    rintros G' x y xlift ylift vias,
    have h := efficient xlift ylift (begin norm_cast, rw vias, end),
    simp at h,
    exact h,
  end }

section lemmas
variables (G' : subgraph G)

@[simp] lemma coe_vertices : (vertices G') = (subgraph.vertices' G') := rfl
@[simp] lemma coe_edges : (edges G') = (subgraph.edges' G') := rfl

@[ext] lemma ext (x y : subgraph G) : x.vertices' = y.vertices' → x.edges' = y.edges' → x = y :=
begin intros hv he, cases x, cases y, congr, exact hv, exact he, end

end lemmas

section subgraph_lattice

def is_subgraph (x y : subgraph G) := x.vertices' ⊆ y.vertices' ∧ x.edges' ⊆ y.edges'

def union (x y : subgraph G) : subgraph G :=
{ vertices' := x.vertices' ∪ y.vertices',
  edges' := x.edges' ∪ y.edges',
  has_verts := begin
    rintros z hel h,
    cases h,
    exact or.inl (x.has_verts hel h),
    exact or.inr (y.has_verts hel h),
  end }

def inter (x y : subgraph G) : subgraph G :=
{ vertices' := x.vertices' ∩ y.vertices',
  edges' := x.edges' ∩ y.edges',
  has_verts := begin
    rintros z hel h,
    exact ⟨x.has_verts hel h.1, y.has_verts hel h.2⟩,
  end }

instance : has_subset (subgraph G) := ⟨is_subgraph⟩
instance : has_union (subgraph G) := ⟨union⟩
instance : has_inter (subgraph G) := ⟨inter⟩

def top : subgraph G :=
{ vertices' := set.univ,
  edges' := set.univ,
  has_verts := by { rintros z hel h, apply set.mem_univ, } }

def bot : subgraph G :=
{ vertices' := ∅,
  edges' := ∅,
  has_verts := by { rintros z hel h, tauto, } }

instance : bounded_lattice (subgraph G) :=
{ top := top,
  bot := bot,
  le := is_subgraph,
  le_refl := by { intro a, exact ⟨set.subset.refl _, set.subset.refl _⟩, },
  le_trans := by { intros x y z hxy hyz,
                   exact ⟨set.subset.trans hxy.1 hyz.1,
                         set.subset.trans hxy.2 hyz.2⟩, },
  le_antisymm := begin
    intros x y hxy hyx,
    cases x, cases y, congr,
    exact set.subset.antisymm hxy.1 hyx.1,
    exact set.subset.antisymm hxy.2 hyx.2,
  end,
  le_top := λ x, ⟨set.subset_univ _, set.subset_univ _⟩,
  bot_le := by { intro a, split; exact set.empty_subset _, },
  sup := subgraph.union,
  inf := subgraph.inter,
  sup_le := by { intros x y z hxy hyz,
                 exact ⟨set.union_subset hxy.1 hyz.1, set.union_subset hxy.2 hyz.2⟩, },
  le_sup_left :=
    by { intros x y,
         exact ⟨set.subset_union_left x.vertices' y.vertices', set.subset_union_left x.edges' y.edges'⟩, },
  le_sup_right :=
    by { intros x y,
         exact ⟨set.subset_union_right x.vertices' y.vertices', set.subset_union_right x.edges' y.edges'⟩, },
  le_inf :=
    by { intros x y z hxy hyz, exact ⟨set.subset_inter hxy.1 hyz.1, set.subset_inter hxy.2 hyz.2⟩, },
  inf_le_left :=
    by { intros x y,
         exact ⟨set.inter_subset_left x.vertices' y.vertices', set.inter_subset_left x.edges' y.edges'⟩, },
  inf_le_right :=
    by { intros x y,
         exact ⟨set.inter_subset_right x.vertices' y.vertices', set.inter_subset_right x.edges' y.edges'⟩, }, }


end subgraph_lattice

end subgraph

structure simple_graph (α : Type*) :=
(r : α → α → Prop)
(sym : symmetric r)
(irr : irreflexive r)

namespace simple_graph
variables {α : Type*} (G : simple_graph α)

def edge_set : set (sym2 α) := {z | sym2.in_rel G.sym z}

def links' : set (link α (edge_set G)) := {x | link.ends x = x.via}

lemma link_rev' : link.rev '' links' G ⊆ links' G :=
begin
  rintros _ ⟨x, xel, rfl⟩,
  dsimp [links'] at xel ⊢,
  rwa link.rev_ends,
end

-- TODO I tried using `induction e using quotient.induction_on`, but
-- this caused some terrible non-unifiable things in the setoid
-- instances for `quotient.mk`.
lemma all_edges' : ∀ (e : edge_set G), ∃ x, x ∈ links' G ∧ link.via x = e :=
begin
  rintros ⟨e, he⟩,
  have hx' : ∃ (x' : link α (sym2 α)), link.via x' = e ∧ link.ends x' = e, {
    induction e,
    cases e with a b,
    use ⟨a, quot.mk _ (a, b), b⟩,
    simp [link.ends], refl, simp,
  },
  rcases hx' with ⟨⟨s, v, d⟩, hvx', hex'⟩,
  rw ←hvx' at he,
  simp only at he,
  use ⟨s, ⟨v, he⟩, d⟩,
  simp only at hvx' hex',
  split, swap, simp [hvx'],
  simp [links', link.ends],
  norm_cast, simp only,
  simp [link.ends] at hex',
  rw hex', rw ←hvx',
  simp,
end

lemma efficient' : ∀ ⦃x y⦄, x ∈ links' G → y ∈ links' G → link.via x = link.via y → link.same_edge x y :=
begin
  rintros x y xel yel vias,
  cases x, cases y,
  dsimp [links', link.ends] at xel yel,
  norm_cast at xel yel,
  simp at xel yel,
  dsimp at vias,
  have vias' : (↑x_via : sym2 α) = ↑y_via, rw vias,
  rw [←xel, ←yel] at vias',
  dsimp [link.same_edge],
  cases sym2.eq vias',
  left, rw [h.1, h.2], simpa,
  right, dsimp [link.rev], rw [h.1, h.2], simpa,
end

instance to_multigraph {α : Type*} : multigraphs (simple_graph α) :=
{ vertices := λ G, α,
  edges := λ G, edge_set G,
  links := links',
  link_rev := link_rev',
  all_edges := all_edges',
  efficient := efficient' }

lemma r_is_adjacency (G : simple_graph α) : ∀ x y, G.r x y ↔ adjacent G x y :=
begin
  intros x y,
  dsimp [adjacent],
  split, {
    intro h,
    use link.mk x ⟨⟦(x, y)⟧, h⟩ y,
    tidy,
  },
  cases G with r sym irr,
  rintros ⟨⟨src, ⟨via, h⟩, dest⟩, ⟨el, rfl⟩, rfl⟩,
  dsimp [edge_set] at h,
  dsimp [vertices] at src dest,
  simp only,
  induction via,
  cases via with a b,
  change link.ends _ = _ at el,
  simp only [links, links', edge_set, link.ends, subtype.coe_mk] at el,
  simp [sym2.in_rel, quotient.rec_on, quot.rec_on, quot.rec] at h,
  cases sym2.eq el,
  simpa [h_1],
  simp [h_1, sym h],
  refl,
end


end simple_graph


def complete_graph (α : Type*) : simple_graph α :=
{ r := ne,
  sym := λ x y, ne.symm,
  irr := λ x, ne.irrefl }


end graph


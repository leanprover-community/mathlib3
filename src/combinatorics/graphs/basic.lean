/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller.
-/

--import data.equiv.basic
--import combinatorics.graphs.sym2
--import combinatorics.graphs.multigraphs
import data.fintype.basic
import order.bounded_lattice
import tactic
open function (hiding graph)
--open equiv

namespace graph
universes u v

section links

-- A link with vertex type α and edge type β represents a directed
-- path through a given edge.
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

-- Since we are modeling undirected graphs, two links are essentially
-- the same if they are the same up to orientation reversal.
def almost_equal : link α β → link α β → Prop :=
λ x y, x = y ∨ x = y.rev

instance : has_equiv (link α β) := ⟨almost_equal⟩

def lift {V : set α} {E : set β} (x : link V E) : link α β := ⟨x.src.val, x.via.val, x.dest.val⟩

end link

end links


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
(V : set α) (E : set β) (links : set (link α β))
(link_src : link.src '' links ⊆ V)
(link_via : link.via '' links = E)
(link_rev : link.rev '' links ⊆ links)
(efficient : ∀ {x y : link α β}, x ∈ links → y ∈ links → x.via = y.via → x ≈ y)

def multigraph.link_dest {α : Type u} {β : Type v} (g : multigraph α β) : link.dest '' g.links ⊆ g.V :=
begin
  rintros v ⟨x, xel, xdest⟩,
  rw ←xdest,
  exact g.link_src ⟨x.rev, g.link_rev ⟨x, xel, rfl⟩, rfl⟩,
end

namespace multigraph
variables {α : Type u} {β : Type v} {v w : α}


def links_between (g : multigraph α β) (v w : α) : set (link α β) := {x ∈ g.links | x.src = v ∧ x.dest = w}

lemma links_between_subset {g : multigraph α β} (v w : α) : g.links_between v w ⊆ g.links :=
λ x h, h.1

lemma links_between_rev_iff {g : multigraph α β} {v w : α} {x : link α β}
: x ∈ g.links_between v w ↔ x.rev ∈ g.links_between w v :=
begin
  split,
  rintro ⟨xel, h⟩,
  use g.link_rev ⟨x, xel, rfl⟩,  rw [←h.1, ←h.2], simp,
  rintro ⟨xrel, h⟩,
  have xel := g.link_rev ⟨x.rev, xrel, rfl⟩,
  rw link.rev_rev at xel,
  use xel, rw [←h.1, ←h.2], simp only [link.rev_src, link.rev_dest, eq_self_iff_true, and_self],
end

def edges (g : multigraph α β) (v w : α) : set β := link.via '' g.links_between v w

lemma edges_subset_edge_set (g : multigraph α β) (v w : α) : g.edges v w ⊆ g.E :=
begin
  rintros e ⟨x, ⟨xel, h⟩, xvia⟩,
  rw ←g.link_via,
  use [x, xel, xvia],
end

lemma edges_reversible (g : multigraph α β) : ∀ v w, g.edges v w = g.edges w v :=
begin
  have key : ∀ v w e, e ∈ g.edges v w → e ∈ g.edges w v, {
    rintros v w e ⟨x,el,xvia⟩,
    use x.rev,
    rw [links_between_rev_iff, link.rev.involutive],
    use el,
    rwa link.rev_via,
  },
  intros v w,
  ext e,
  exact ⟨key v w e, key w v e⟩,
end

lemma edges_have_ends {g : multigraph α β} {x y x' y' : α} {e : β} (h : e ∈ g.edges x y) (h' : e ∈ g.edges x' y')
: (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') :=
begin
  rcases h with ⟨lx, lxbt, lxvia⟩,
  rcases h' with ⟨lx', lxbt', lxvia'⟩,
  have p : lx.via = lx'.via, cc,
  rw [←lxbt.2.1, ←lxbt.2.2],
  rw [←lxbt'.2.1, ←lxbt'.2.2],
  cases g.efficient lxbt.1 lxbt'.1 p with q q; cases lx; cases lx'; simp only [link.rev] at p q ⊢,
  left, tauto, right, tauto,
end

lemma has_link (g : multigraph α β) {e : β} (h : e ∈ g.E) : ∃ (x : link α β), x ∈ g.links ∧ x.via = e :=
(set.ext_iff.mp g.link_via e).mpr h

def links_at (g : multigraph α β) (v : α) : set (link α β) := {x ∈ g.links | x.src = v}

-- The set of edges incident to a given vertex.  You might want
-- `links_at` if you are traversing a graph.
def incident (g : multigraph α β) (v : α) : set β := link.via '' links_at g v

-- TODO this does not appear to be computable in general
noncomputable
def opp {g : multigraph α β} (v : α) {e} (h : e ∈ incident g v) : α := begin
  exact link.dest (classical.some h),
end


--∃ w, e ∈ g.edges v w := h


end multigraph


section subgraphs
variables {α : Type u} {β : Type v}
open multigraph

-- `subgraph g` is the type of all subgraphs of a given multigraph.
-- These are not multigraphs per se, but they can be converted to
-- multigraphs using `subgraph.to_graph`.  There is an instance to
-- coerce subgraphs to multigraphs.
structure subgraph (g : multigraph α β) :=
(V : set α) (E : set β)
(vert_is_subset : V ⊆ g.V) (edge_is_subset : E ⊆ g.E)
(has_verts : ∀ {e}, e ∈ E → ∀ {x : link α β}, x ∈ g.links → e = x.via → x.src ∈ V)

-- The dest version of subgraph.has_verts
lemma subgraph.has_verts_dest {g : multigraph α β} (h : subgraph g) : ∀ {e}, e ∈ h.E → ∀ {x : link α β}, x ∈ g.links → e = x.via → x.dest ∈ h.V :=
begin
  intros e eel x xel hvia,
  rw ←link.rev_src,
  apply h.has_verts eel (g.link_rev ⟨x, xel, rfl⟩),
  simpa only,
end

-- Construct a multigraph from the given subgraph.
def subgraph.to_graph {g : multigraph α β} (g' : subgraph g) : multigraph α β := {
  V := g'.V,
  E := g'.E,
  links := {x : link α β | x ∈ g.links ∧ x.via ∈ g'.E},
  link_src := begin
    rintros a ⟨x, ⟨xel, h⟩, xsrc⟩,
    have key := g'.has_verts h xel rfl,
    rwa xsrc at key,
  end,
  link_via := begin
    ext e, split,
    rintros ⟨x, ⟨⟨xel, h⟩, rfl⟩⟩,
    exact h,
    intro eel,
    rcases g.has_link (g'.edge_is_subset eel) with ⟨x, xel, rfl⟩,
    use [x, ⟨xel, eel⟩],
  end,
  link_rev := begin
    rintros x' ⟨x, ⟨xel, h⟩, rfl⟩,
    use g.link_rev ⟨x, xel, rfl⟩,
    simpa,
  end,
  efficient := begin
    rintros x y ⟨xel, hx⟩ ⟨yel, hy⟩ vias,
    exact g.efficient xel yel vias,
  end
}

instance {g : multigraph α β} (x : subgraph g) : has_coe (subgraph g) (multigraph α β) := ⟨subgraph.to_graph⟩

@[ext]
def subgraph.ext {g : multigraph α β} (x y : subgraph g) : x.V = y.V → x.E = y.E → x = y :=
begin intros hv he, cases x, cases y, congr, exact hv, exact he, end

section subgraph_lattice

variables {g : multigraph α β}

def subgraph.is_subgraph (x y : subgraph g) := x.V ⊆ y.V ∧ x.E ⊆ y.E

def subgraph.is_ssubgraph (x y : subgraph g) := x.is_subgraph y ∧ (x.V ⊂ y.V ∨ x.E ⊂ y.E)

def subgraph.union (x y : subgraph g) : subgraph g := {
  V := x.V ∪ y.V,
  E := x.E ∪ y.E,
  vert_is_subset := set.union_subset x.vert_is_subset y.vert_is_subset,
  edge_is_subset := set.union_subset x.edge_is_subset y.edge_is_subset,
  has_verts := begin
    rintros e h l lel rfl,
    cases h with h h,
    exact or.inl (x.has_verts h lel rfl),
    exact or.inr (y.has_verts h lel rfl),
  end
}

def subgraph.inter (x y : subgraph g) : subgraph g := {
  V := x.V ∩ y.V,
  E := x.E ∩ y.E,
  vert_is_subset := set.subset.trans (set.inter_subset_left _ _) x.vert_is_subset,
  edge_is_subset := set.subset.trans (set.inter_subset_left _ _) x.edge_is_subset,
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
  V := g.V,
  E := g.E,
  vert_is_subset := set.subset.refl _,
  edge_is_subset := set.subset.refl _,
  has_verts := by rintros e h l lel rfl; exact g.link_src ⟨l, lel, rfl⟩
}
def subgraph.bot : subgraph g := {
  V := ∅,
  E := ∅,
  vert_is_subset := set.empty_subset _,
  edge_is_subset := set.empty_subset _,
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
  le_top := λ x, ⟨x.vert_is_subset, x.edge_is_subset⟩,
  bot_le := by intro a; split; exact set.empty_subset _,
  sup := subgraph.union,
  inf := subgraph.inter,
  sup_le := by intros x y z hxy hyz;
               exact ⟨set.union_subset hxy.1 hyz.1, set.union_subset hxy.2 hyz.2⟩,
  le_sup_left := by intros x y;
                    exact ⟨set.subset_union_left x.V y.V, set.subset_union_left x.E y.E⟩,
  le_sup_right := by intros x y;
                     exact ⟨set.subset_union_right x.V y.V, set.subset_union_right x.E y.E⟩,
  le_inf := by intros x y z hxy hyz; exact ⟨set.subset_inter hxy.1 hyz.1, set.subset_inter hxy.2 hyz.2⟩,
  inf_le_left := by intros x y;
                    exact ⟨set.inter_subset_left x.V y.V, set.inter_subset_left x.E y.E⟩,
  inf_le_right := by intros x y;
                     exact ⟨set.inter_subset_right x.V y.V, set.inter_subset_right x.E y.E⟩,
}

end subgraph_lattice


end subgraphs

namespace multigraph
variables {α : Type u} {β : Type v}

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

-- superfluous
instance fintype.links_from_α_and_β (g : multigraph α β) [fintype α] [fintype β] [decidable_pred g.links] : fintype g.links :=
begin
  apply_instance,
end

-- TODO not sure if this is possible
-- instance fintype.links_from_verts_and_edges (g : multigraph α β) [fintype g.V] [fintype g.E] [decidable_pred g.links] : fintype g.links := sorry

instance fintype.edges_from_links (g : multigraph α β) [fintype g.links] [decidable_eq β] : fintype g.E :=
begin
  let f : g.links → g.E := begin
    rintro ⟨x,xel⟩,
    exact ⟨x.via, (set.ext_iff.mp g.link_via x.via).mp ⟨x, xel, rfl⟩⟩,
  end,
  have h : surjective f, {
    rintro ⟨e, eel⟩,
    rcases (set.ext_iff.mp g.link_via e).mpr eel with ⟨x, xel, rfl⟩,
    use ⟨x, xel⟩,
  },
  exact fintype.of_surjective f h,
end


end multigraph


end graph



-- structure graph (V : Type u) extends multigraph V :=
-- (single_edge : injective ends)
-- (loopless : ∀ e : E, ¬(ends e).is_diag)

-- variables {V : Type u}

-- def to_multigraph (g : graph V) : multigraph V :=
-- ⟨g.E, g.ends⟩

-- def from_relation {α : Type u} {r : α → α → Prop} (h₁ : symmetric r) (h₂ : irreflexive r) : graph α :=
-- {
--   E := {z : sym2 α // ∃ x y, r x y ∧ z = sym2.mk x y},
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

-- def graph.adj {V : Type u} (g : graph V) (x y : V) : Prop := g.to_multigraph.adj x y

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

-- instance finite_edge_set [fintype V] (g : graph V) : fintype g.E := sorry

-- def graph.nverts [fintype V] (g : graph V) := fintype.card V
-- def graph.nedges [fintype V] (g : graph V) := fintype.card g.E

-- end graph

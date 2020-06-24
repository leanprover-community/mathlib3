/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller.
-/

--import data.equiv.basic
--import combinatorics.graphs.sym2
--import combinatorics.graphs.multigraphs
import order.bounded_lattice
import tactic
--open function (hiding graph)
--open equiv
--open sym2

namespace graph
universes u v
--variables {V : Type u} {E : Type v}

-- This is the type for multigraphs with vertex and edge sets in a
-- particular universe.  The V type is inside the structure so that we
-- may define a coercion from subgraphs to multigraphs.  If you want
-- to deal with graphs all with the same vertex then you might want to
-- use subgraphs of a complete graph.
structure multigraph :=
(V : Type u) (E : Type v) (edges : V → V → set E)
(has_edges : ∀ e, ∃ x y, e ∈ edges x y)
(reversible : ∀ x y, edges x y = edges y x)
(has_ends : ∀ {x y x' y' e}, e ∈ edges x y → e ∈ edges x' y' → (x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))


section links

structure link (V : Type u) (E : Type v) :=
(src : V) (via : E) (dest : V)

def link.rev {V : Type u} {E : Type v} (x : link V E) : link V E := ⟨x.dest, x.via, x.src⟩

def multigraph.links (g : multigraph) : set (link g.V g.E) := {x | x.via ∈ g.edges x.src x.dest}

--instance (g : multigraph V) [fintype g.links] : fintype V := sorry
--instance (g : multigraph V) [fintype g.links] : fintype g.E := sorry

end links

section subgraphs

-- `subgraph g` is the type of all subgraphs of a given multigraph.
-- These are not multigraphs per se, but they can be converted to
-- multigraphs using `subgraph.to_graph`.  There is an instance to
-- coerce subgraphs to multigraphs.
structure subgraph (g : multigraph) :=
(V' : set g.V) (E' : set g.E)
(has_verts : ∀ {e}, e ∈ E' → ∃ v w ∈ V', e ∈ g.edges v w)

-- Construct a multigraph from the given subgraph.
def subgraph.to_graph {g : multigraph} (g' : subgraph g) : multigraph := {
  V := subtype g'.V',
  E := subtype g'.E',
  edges := λ x y, {e : subtype g'.E' | e.val ∈ g.edges x y },
  has_edges := λ e, by
    rcases g'.has_verts e.property with ⟨x,y,xel,yel,h⟩;
    exact ⟨⟨x,xel⟩, ⟨y,yel⟩, h⟩,
  reversible := λ ⟨x,xel⟩ ⟨y,yel⟩, by ext ⟨e,ein⟩; simp only [g.reversible],
  has_ends := begin
    rintros ⟨x,xin⟩ ⟨y,yin⟩ ⟨x',x'in⟩ ⟨y',y'in⟩ ⟨e,ein⟩ hxy hx'y',
    simp only [subtype.mk_eq_mk],
    simp only [set.mem_set_of_eq, subtype.coe_mk] at hxy hx'y',
    have hh := g.has_ends,
    exact g.has_ends hxy hx'y',
  end
}

instance {g : multigraph} (x : subgraph g) : has_coe (subgraph g) multigraph := ⟨subgraph.to_graph⟩

@[ext]
def subgraph.ext {g : multigraph} (x y : subgraph g) : x.V' = y.V' → x.E' = y.E' → x = y :=
begin intros hv he, cases x, cases y, congr, exact hv, exact he, end

section subgraph_lattice

variables {g : multigraph}

def subgraph.is_subgraph (x y : subgraph g) := x.V' ⊆ y.V' ∧ x.E' ⊆ y.E'

def subgraph.is_ssubgraph (x y : subgraph g) := x.is_subgraph y ∧ (x.V' ⊂ y.V' ∨ x.E' ⊂ y.E')

def subgraph.union (x y : subgraph g) : subgraph g := {
  V' := x.V' ∪ y.V',
  E' := x.E' ∪ y.E',
  has_verts := begin
    intros e h,
    cases h with h h,
    rcases x.has_verts h with ⟨v, w, vin, win, h⟩,
    use [v, w, or.inl vin, or.inl win, h],
    rcases y.has_verts h with ⟨v, w, vin, win, h⟩,
    use [v, w, or.inr vin, or.inr win, h],
  end}

def subgraph.inter (x y : subgraph g) : subgraph g := {
  V' := x.V' ∩ y.V',
  E' := x.E' ∩ y.E',
  has_verts := begin
    intros e h,
    rcases x.has_verts h.1 with ⟨xv, xw, xvin, xwin, xh⟩,
    rcases y.has_verts h.2 with ⟨yv, yw, yvin, ywin, yh⟩,
    cases g.has_ends xh yh with eqs eqs;
      rw eqs.1 at xvin;
      rw eqs.2 at xwin,
    use [yv, yw, ⟨xvin, yvin⟩, ⟨xwin, ywin⟩, yh],
    rw g.reversible at yh,
    use [yw, yv, ⟨xvin, ywin⟩, ⟨xwin, yvin⟩, yh],
  end
}

instance : has_subset (subgraph g) := ⟨subgraph.is_subgraph⟩
instance : has_ssubset (subgraph g) := ⟨subgraph.is_ssubgraph⟩
instance : has_union (subgraph g) := ⟨subgraph.union⟩
instance : has_inter (subgraph g) := ⟨subgraph.inter⟩

def subgraph.top : subgraph g := {
  V' := ⊤,
  E' := ⊤,
  has_verts := begin
    intros e h,
    rcases g.has_edges e with ⟨v, w, ein⟩,
    refine ⟨v, w, trivial, trivial, ein⟩,
  end
}
def subgraph.bot : subgraph g :=  {
  V' := ∅,
  E' := ∅,
  has_verts := begin intros e h, exfalso, rwa set.mem_empty_eq at h, end
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
  le_top := by intro a; split; exact set.subset_univ _,
  bot_le := by intro a; split; exact set.empty_subset _,
  sup := subgraph.union,
  inf := subgraph.inter,
  sup_le := by intros x y z hxy hyz;
               exact ⟨set.union_subset hxy.1 hyz.1, set.union_subset hxy.2 hyz.2⟩,
  le_sup_left := by intros x y;
                    exact ⟨set.subset_union_left x.V' y.V', set.subset_union_left x.E' y.E'⟩,
  le_sup_right := by intros x y;
                     exact ⟨set.subset_union_right x.V' y.V', set.subset_union_right x.E' y.E'⟩,
  le_inf := by intros x y z hxy hyz; exact ⟨set.subset_inter hxy.1 hyz.1, set.subset_inter hxy.2 hyz.2⟩,
  inf_le_left := by intros x y;
                    exact ⟨set.inter_subset_left x.V' y.V', set.inter_subset_left x.E' y.E'⟩,
  inf_le_right := by intros x y;
                     exact ⟨set.inter_subset_right x.V' y.V', set.inter_subset_right x.E' y.E'⟩,
}

end subgraph_lattice


end subgraphs

section accessors
variable {g : multigraph}

-- The set of edges incident to a given vertex.
def incident (v : g.V) : set g.E := {e | ∃ w, e ∈ g.edges v w}

-- The vertex opposite an edge incident to a given vertex.  This
-- function is mainly here as a note that we cannot make a g.E-valued
-- function due to the way multigraphs are defined.
def opp (v : g.V) {e} (h : e ∈ incident v) : ∃ w, e ∈ g.edges v w := h

end accessors


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

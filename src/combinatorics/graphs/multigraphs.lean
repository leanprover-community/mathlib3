/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller.
-/

import combinatorics.graphs.sym2
open sym2
open function (hiding graph)

namespace graph
universes u v

-- A directed multigraph consists of collections of vertices and edges
-- along with a map attaching the two ends of each edge to the
-- vertices.
structure directed_multigraph (V : Type u) :=
(E : Type u) (ends : E → V × V)

-- A multigraph is like a `directed_multigraph`, except the attaching
-- map is inherently undirected.
structure multigraph (V : Type u) :=
(E : Type v) (ends : E → sym2 V)

namespace multigraph
variable {V : Type u}

-- The set of edges between x and y.
def edge_set (g : multigraph V) (x y : V) : Type v := {e : g.E // g.ends e = sym2.mk x y}

-- Adjacency relation.  Two vertices are adjacent iff there is an edge between them.
def adj (g : multigraph V) (x y : V) : Prop := nonempty (g.edge_set x y)

-- A map between graphs is a map on the vertex sets and a map on the
-- edge sets such that the edge attachments are respected.
structure hom {V V' : Type u} (g : multigraph V) (g' : multigraph V') :=
(on_vertices : V → V')
(on_edges : g.E → g'.E)
(on_ends : ∀ e : g.E, (sym2.induce on_vertices) (g.ends e) = g'.ends (on_edges e))

def hom.id {V : Type u} {g : multigraph V} : hom g g := {
  on_vertices := id,
  on_edges := id,
  on_ends := by simp
}

section homs
variables {V₁ V₂ V₃ : Type u} {g₁ : multigraph V₁} {g₂ : multigraph V₂} {g₃ : multigraph V₃}

def hom.comp (g : hom g₂ g₃) (f : hom g₁ g₂) : hom g₁ g₃ := {
  on_vertices := g.on_vertices ∘ f.on_vertices,
  on_edges := g.on_edges ∘ f.on_edges,
  on_ends := begin
    intro e,
    rw sym2.induce.functorial,
    repeat {rw comp_app},
    rw f.on_ends,
    rw g.on_ends,
  end
}

@[simp]
lemma hom.comp_id (f : hom g₁ g₂) : hom.comp f hom.id = f :=
begin cases f, dunfold hom.comp, congr, end

@[simp]
lemma hom.id_comp (f : hom g₁ g₂) : hom.comp hom.id f = f :=
begin cases f, dunfold hom.comp, congr, end

structure multigraph_equiv (g₁ : multigraph V₁) (g₂ : multigraph V₂) :=
(to_fun    : hom g₁ g₂)
(inv_fun   : hom g₂ g₁)
(left_inv  : inv_fun.comp to_fun = hom.id)
(right_inv : to_fun.comp inv_fun = hom.id)

def multigraph_equiv.id {g : multigraph V} : multigraph_equiv g g := {
  to_fun := hom.id,
  inv_fun := hom.id,
  left_inv := by simp,
  right_inv := by simp,
}

def multigraph_equiv.symm (f : multigraph_equiv g₁ g₂) : multigraph_equiv g₂ g₁ :=
⟨f.inv_fun, f.to_fun, f.right_inv, f.left_inv⟩

-- TODO (and @[simp] lemmas)
--def multigraph_equiv.comp (g : multigraph_equiv g₂ g₃) (f : multigraph_equiv g₁ g₂) : multigraph_equiv g₁ g₃
--def multigraph_equiv.comp_id
--def multigraph_equiv.id_comp
--def multigraph_equiv.comp_symm {f : multigraph_equiv g₁ g₂}: f.comp f.symm = multigraph_equiv.id
--def multigraph_equiv.symm_comp {f : multigraph_equiv g₂ g₁}: f.symm.comp f = multigraph_equiv.id

-- Two multigraphs are isomorphic if there is an equivalence.
def multigraph_iso (g₁ : multigraph V₁) (g₂ : multigraph V₂) := nonempty (multigraph_equiv g₁ g₂)

instance : has_equiv (multigraph V) := ⟨multigraph_iso⟩

end homs

-- A description of a multigraph by the edge sets.  Used by
-- `multigraph.from_edge_set_desc` to construct a multigraph.
structure edge_set_desc (V : Type u) :=
(edge : V → V → Sort v)
(inv : Π x y, edge x y ≃ edge y x)
(loops : Π x, inv x x = equiv.refl (edge x x))

namespace edge_set_desc

-- These definitions are for constructing the edges of a multigraph
-- described by an `edge_set_desc`, and they are used by
-- `from_edge_set_desc` to construct a multigraph.

def pre_edge_set (d : edge_set_desc V) := Σ (x y : V), d.edge x y

inductive pre_edge_set_equiv (d : edge_set_desc V) : pre_edge_set d → pre_edge_set d → Prop
| refl (x : pre_edge_set d) : pre_edge_set_equiv x x
| swap (x y : V) (z : d.edge x y) : pre_edge_set_equiv ⟨x, y, z⟩ ⟨y, x, d.inv x y z⟩

def total_edge_set (e : edge_set_desc V) := quot (pre_edge_set_equiv e)

end edge_set_desc

-- Construct a multigraph from an `edge_set_desc`.
def from_edge_set_desc (x : edge_set_desc V) : multigraph V := {
  E := edge_set_desc.total_edge_set x,
  ends := λ e, quot.rec_on e
                 (λ e', sigma.cases_on e' (λ x e'', sigma.cases_on e'' (λ y z, sym2.mk x y)))
                 begin
                   intros x y e,
                   cases e,
                   refl,
                   rw eq_rec_constant,
                   apply quot.sound,
                   apply sym2_rel.swap,
                 end
}

-- Convert a multigraph back into an `edge_set_desc`.
def to_edge_set_desc (g : multigraph V) : edge_set_desc V := {
  edge := g.edge_set,
  inv := λ x y,
    begin
      refine ⟨_,_,_,_⟩,
      rintro ⟨e,h⟩, use e, rw sym2.comm, exact h,
      rintro ⟨e,h⟩, use e, rw sym2.comm, exact h,
--      have h : {e : g.E | g.ends e = sym2.mk x y} = {e : g.E | g.ends e = sym2.mk y x},
--        ext, rw sym2.comm,
--      dunfold edge_set,
--      rw h,
      rintro ⟨e,h⟩, simp,
      rintro ⟨e,h⟩, simp,
    end,
  loops := begin rintro x, ext, cases x_1, simp, end
}


-- TODO The proof seems to be almost done, but I'm getting confused about dependent types at the end.

noncomputable
lemma to_edge_set_desc_and_back (g : multigraph V) [decidable_eq V] [decidable_eq g.E] : multigraph_equiv g (from_edge_set_desc g.to_edge_set_desc) :=
begin
  let sym_a : sym2 V → V := λ z, (classical.some (quot.exists_rep z)).1,
  let sym_b : sym2 V → V := λ z, (classical.some (quot.exists_rep z)).2,
  have sym_h : ∀ (z : sym2 V), sym2.mk (sym_a z) (sym_b z) = z, {
    intro z,
    dsimp [sym_a, sym_b, sym2.mk], simp,
    rw classical.some_spec (quot.exists_rep z),
  },
  let f : g.E → (from_edge_set_desc g.to_edge_set_desc).E :=
    λ e, quot.mk _ ⟨sym_a (g.ends e), sym_b (g.ends e), ⟨e, (sym_h (g.ends e)).symm⟩⟩,
  let f' : (from_edge_set_desc g.to_edge_set_desc).E → g.E, {
    refine λ e', quot.rec_on e' (λ z₁, sigma.cases_on z₁
                                   (λ x z₂, sigma.cases_on z₂
                                     (λ y z₃, z₃.val))) _,
    intros x y p,
    cases p,
    refl,
    dsimp [to_edge_set_desc],
    rcases p_z with ⟨e,p_h⟩,
    simp,
  },
  have red : ∀ x y (e : g.edge_set x y),
               (from_edge_set_desc g.to_edge_set_desc).ends (quot.mk g.to_edge_set_desc.pre_edge_set_equiv ⟨x, ⟨y, e⟩⟩)
               = sym2.mk x y, {
    rintros x y ⟨e,h⟩, 
    dsimp [from_edge_set_desc],
    simp,
  },
  have red' : ∀ x y (e : g.edge_set x y),
                f' (quot.mk g.to_edge_set_desc.pre_edge_set_equiv ⟨x, ⟨y, e⟩⟩)
                = e.val, {
    rintros x y ⟨e, h⟩,
    dsimp [f'], simp,
  },
  refine ⟨_,_,_,_⟩,
  refine ⟨id,f,_⟩,
  intro e,
  simp only [id.def, sym2.induce.id],
  exact (sym_h (g.ends e)).symm,
  refine ⟨id,f',_⟩,
  rintro ⟨x,y,z,h⟩,
  simp only [id.def, sym2.induce.id],
  rw red,
  dsimp [f'],
  rw h,
  
  refl,
  dsimp [hom.comp, hom.id],
  congr,
  ext ⟨x,y,e,h⟩,
  dsimp,
  rw red',
  dsimp [f],
  apply quot.sound,
  have h' := (sym_h (g.ends e)).symm,
  set pre_edge : edge_set_desc.pre_edge_set (g.to_edge_set_desc) := ⟨sym_a (g.ends e), ⟨sym_b (g.ends e), ⟨e, h'⟩⟩⟩ with pre_edge_eq,
  change g.to_edge_set_desc.pre_edge_set_equiv pre_edge _,
  -- by_cases hx : sym_a (g.ends e) = x,
  -- by_cases hy : sym_b (g.ends e) = y,
  
  -- rw [hx,hy] at pre_edge_eq,
  -- rw heq,
  -- refine edge_set_desc.pre_edge_set_equiv.refl _,

  -- refine edge_set_desc.pre_edge_set_equiv.swap _ _ _,

  sorry,

end

end multigraph

end graph

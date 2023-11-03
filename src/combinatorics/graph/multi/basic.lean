/-
Copyright (c) 2023 Yaël Dillies, Antoine Labelle, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Antoine Labelle, Kyle Miller
-/
import category_theory.limits.shapes.terminal
import data.sym.sym2

/-!
# Indexed multigraphs

This file defines (indexed) multigraphs. A multigraph is a collection of vertices and a collection
of edges with two maps from the edges to the vertices (representing their ends) and a compatible
involution of the edges.

We provide the category structure and show that multigraphs have a terminal object, namely the graph
with one vertex and one half-loop.

## Main declarations

* `multigraph`: Multigraphs. Also the category of multigraphs.
* `multigraph.discrete`: For a type `X`, the graph with a single half-loop at `x : X` and no other
  edge.

## References

* [Evan Patterson, *Graphs and C-sets*](https://www.algebraicjulia.org/blog/post/2020/09/cset-graphs-1/)
-/

open category_theory category_theory.limits

universes u v

variables {α β : Type*}

/-- A multigraph is a type of vertices `α`, a type of edges `E`, two maps `E → α` representing the
edges ends, and an involution of the edges that respects the ends.

This definition allows *half-loops*, edges from a vertex `v` to itself that are fixed under the
edges involution. -/
@[nolint check_univs]
structure multigraph (α : Type u) :=
(E : Type v)
(edge_verts : E → sym2 α)
(edges : sym2 α → set E)
(mem_edges_iff : ∀ z e, e ∈ edges z ↔ edge_verts e = z)

namespace multigraph
variables {G H I : multigraph α}

attribute [protected] E

/-- `multigraph.inv` as a permutation of the edges. -/
@[simps] def inv_equiv : equiv.perm G.E := ⟨G.inv, G.inv, G.inv_inv, G.inv_inv⟩

/-- A multigraph morphism from `G` to `H` is two maps from the vertices/edges of `G` to the
vertices/edges of `H` that preserve the endpoints and involution of edges. Use `G ⟶ H` instead of
`G.hom H`. -/
@[nolint has_nonempty_instance]
structure map (G : multigraph α) (H : multigraph β) :=
(to_fun : α → β)
(map : G.E → H.E)
(fst_map' : ∀ e, H.fst (map e) = to_fun (G.fst e) . obviously)
(snd_map' : ∀ e, H.snd (map e) = to_fun (G.snd e) . obviously)
(inv_map : ∀ e, H.inv (map e) = map (G.inv e) . obviously)

instance : quiver multigraph := ⟨hom⟩

namespace hom
variables (f : G ⟶ H) (e : G.E)

attribute [simp] inv_map

instance : has_coe_to_fun (G ⟶ H) (λ f, G → H) := ⟨to_fun⟩

@[simp] lemma to_fun_eq_coe : f.to_fun = f := rfl
@[simp] lemma coe_mk (f : G → H) (map : G.E → H.E) (fst_map snd_map inv_map) :
  ⇑(⟨f, map, fst_map, snd_map, inv_map⟩ : G ⟶ H) = f := rfl
@[simp] lemma mk_coe : (⟨f, f.map, f.fst_map', f.snd_map', f.inv_map⟩ : G ⟶ H) = f :=
by { cases f, refl }

@[ext] lemma ext {f g : G ⟶ H} (h₀ : (f : G → H) = g) (h₁ : f.map = g.map) : f = g :=
by { cases f, cases g, congr' }

@[simp] lemma fst_map : H.fst (f.map e) = f (G.fst e) := fst_map' _ _
@[simp] lemma snd_map : H.snd (f.map e) = f (G.snd e) := snd_map' _ _

end hom

instance : large_category multigraph :=
{ hom := hom,
  id := λ X, { to_fun := id, map := id },
  comp := λ X Y Z f g, { to_fun := g.to_fun ∘ f.to_fun, map := g.map ∘ f.map } }

@[simp] lemma coe_id : ⇑(𝟙 G) = id := rfl
@[simp] lemma map_id : (𝟙 G : G ⟶ G).map = id := rfl
@[simp] lemma coe_comp (f : G ⟶ H) (g : H ⟶ I) : ⇑(f ≫ g) = g ∘ f := rfl
@[simp] lemma map_comp (f : G ⟶ H) (g : H ⟶ I) : (f ≫ g).map = g.map ∘ f.map := rfl

/-- Construct a multigraph isomorphism from isomorphisms of the vertices and edges. -/
def iso.mk (eα : G ≃ H) (eE : G.E ≃ H.E) (fst_map : ∀ e, H.fst (eE e) = eα (G.fst e))
  (snd_map : ∀ e, H.snd (eE e) = eα (G.snd e)) (inv_map : ∀ e, H.inv (eE e) = eE (G.inv e)) :
  G ≅ H :=
{ hom := { to_fun := eα,
           map := eE,
           fst_map' := fst_map,
           snd_map' := snd_map,
           inv_map := inv_map },
  inv := { to_fun := eα.symm,
           map := eE.symm,
           fst_map' := λ e, eα.eq_symm_apply.2 $ by rw [←fst_map, eE.apply_symm_apply],
           snd_map' := λ e, eα.eq_symm_apply.2 $ by rw [←snd_map, eE.apply_symm_apply],
           inv_map := λ e, eE.eq_symm_apply.2 $ by rw [←inv_map, eE.apply_symm_apply] } }

/-- The multigraph with vertices `X` and a single loop at each vertex. -/
@[simps] def discrete (X : Type*) : multigraph :=
{ α := X, E := X, fst := id, snd := id, inv := id }

instance : inhabited multigraph := ⟨discrete punit⟩

/-- `multigraph.discrete` as a functor. -/
def discrete_functor : Type* ⥤ multigraph :=
{ obj := discrete, map := λ X Y f, { to_fun := f, map := f } }

/-- The multigraph with a simple vertex and a single loop is terminal. -/
def is_terminal_discrete_punit : is_terminal (discrete punit) :=
(is_terminal_equiv_unique _ _).symm $ λ G,
  { default := ({ to_fun := λ _, (), map := λ _, () } : G ⟶ discrete punit), uniq := by tidy }

instance : has_terminal multigraph := is_terminal_discrete_punit.has_terminal

end multigraph

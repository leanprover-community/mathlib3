/-
Copyright (c) 2022 Yaël Dillies, Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Antoine Labelle
-/
import category_theory.limits.shapes.terminal

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

/-- A multigraph is a type of vertices `V`, a type of edges `E`, two maps `E → V` representing the
edges ends, and an involution of the edges that respects the ends.

This definition allows *half-loops*, edges from a vertex `v` to itself that are fixed under the
edges involution. -/
@[nolint check_univs]
structure multigraph :=
(V : Type u)
(E : Type v)
(fst snd : E → V)
(inv : E → E)
(inv_fst : ∀ e, fst (inv e) = snd e . obviously)
(inv_snd : ∀ e, snd (inv e) = fst e . obviously)
(inv_inv : ∀ e, inv (inv e) = e . obviously)

namespace multigraph
variables {G H I : multigraph.{u v}}

attribute [simp] inv_fst inv_snd inv_inv

instance : has_coe_to_sort multigraph Type* := ⟨V⟩

attribute [protected] V E

/-- A multigraph morphism from `G` to `H` is two maps from the vertices/edges of `G` to the
vertices/edges of `H` that preserve the endpoints and involution of edges. -/
@[nolint has_nonempty_instance]
structure hom (G H : multigraph) :=
(to_fun : G → H)
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

/-- The multigraph with vertices `X` and a single loop at each vertex. -/
@[simps] def discrete (X : Type*) : multigraph :=
{ V := X, E := X, fst := id, snd := id, inv := id }

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

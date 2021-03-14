/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import tactic
/-!
# Quivers

This module defines quivers. A quiver `G` on a type `V` of vertices assigns to every
pair `a b : V` of vertices a type `G a b`, thought of as edges from `a` to `b`. This
is a very permissive notion of graph.
-/

-- We use the same universe order as in category theory.
universes v u

/-- A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
    a type `G a b`, thought of as edges from `a` to `b`. -/
def quiver (V : Type u) := V → V → Type v

/-- The default quiver on `V` is the empty quiver. -/
instance {V} : inhabited (quiver.{v} V) :=
⟨λ a b, pempty⟩

/-- A subquiver `H` of `G` picks out subset `H a b` of the edges from `a` to `b`
    for every pair of vertices `a b`. -/
def subquiver {V} (G : quiver V) :=
Π a b : V, set (G a b)

/-- The default subquiver of `G` contains every edge. -/
instance {V} {G : quiver V} : inhabited (subquiver G) :=
⟨λ a b, set.univ⟩

/-- A subquiver viewed as a quiver on its own. -/
def subquiver.quiver {V} {G : quiver V} (H : subquiver G) : quiver V :=
λ a b, H a b

namespace quiver

/-- `G.sum H` takes the disjoint union of the edges of `G` and `H`. -/
def sum {V} (G H : quiver V) : quiver V :=
λ a b, G a b ⊕ H a b

/-- `G.opposite` reverses the direction of all edges of `G`. -/
def opposite {V} (G : quiver V) : quiver V :=
flip G

/-- `G.symmetrify` adds to `G` the reversal of all edges of `G`. -/
def symmetrify {V} (G : quiver V) : quiver V :=
G.sum G.opposite

/-- `G.total` is the type of _all_ edges of `G`. -/
@[ext] structure total {V} (G : quiver.{v u} V) : Type (max u v) :=
(source : V)
(target : V)
(edge : G source target)

instance {V} [inhabited V] {G : quiver V} [inhabited (G (default V) (default V))] :
  inhabited G.total :=
⟨⟨default V, default V, default _⟩⟩

/-- A `H` subquiver of `G.symmetrify` determines a subquiver of `G`, containing an
    an edge `e` if either `e` or its reversal is in `H`. -/
def subquiver_symmetrify {V} (G : quiver V) :
  subquiver G.symmetrify → subquiver G :=
λ H a b, { e | sum.inl e ∈ H a b ∨ sum.inr e ∈ H b a }

/-- A subquiver of `G` can equivalently be viewed as a total set of edges. -/
def subquiver_equiv_set_total {V} (G : quiver V) :
  subquiver G ≃ set G.total :=
{ to_fun := λ H, {e | e.edge ∈ H e.source e.target },
  inv_fun := λ S a b, { e | total.mk a b e ∈ S },
  left_inv := λ H, rfl,
  right_inv := by { intro S, ext, cases x, refl } }

/-- `G.path a b` is the type of paths from `a` to `b` through the edges of `G`. -/
inductive path {V} (G : quiver.{v u} V) (a : V) : V → Type (max u v)
| nil  : path a
| cons : Π {b c : V}, path b → G b c → path c

/-- A quiver is an arborescence when there is a unique path from the default vertex
    to every other vertex. -/
class arborescence {V} [inhabited V] (G : quiver.{v u} V) : Type (max u v) :=
(unique_path : Π (b : V), unique (G.path (default V) b))

attribute [instance] arborescence.unique_path

end quiver

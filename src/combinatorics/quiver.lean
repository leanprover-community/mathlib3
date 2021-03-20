/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import tactic
/-!
# Quivers

This module defines quivers. A quiver `G` on a type `V` of vertices assigns to every
pair `a b : V` of vertices a type `G.arrow a b` of arrows from `a` to `b`. This
is a very permissive notion of directed graph.
-/

-- We use the same universe order as in category theory.
-- See note [category_theory universes]
universes v u

/-- A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
    a type `G.arrow a b` of arrows from `a` to `b`. -/
structure quiver (V : Type u) :=
(arrow : V → V → Sort v)

/-- A wide subquiver `H` of `G` picks out a set `H a b` of arrows from `a` to `b`
    for every pair of vertices `a b`. -/
def wide_subquiver {V} (G : quiver V) :=
Π a b : V, set (G.arrow a b)

/-- A wide subquiver viewed as a quiver on its own. -/
def wide_subquiver.quiver {V} {G : quiver V} (H : wide_subquiver G) : quiver V :=
⟨λ a b, H a b⟩

namespace quiver

/-- The quiver with no arrows. -/
protected def empty (V) : quiver.{v} V := ⟨λ a b, pempty⟩

instance {V} : inhabited (quiver.{v} V) := ⟨quiver.empty V⟩
instance {V} (G : quiver V) : has_bot (wide_subquiver G) := ⟨λ a b, ∅⟩
instance {V} (G : quiver V) : has_top (wide_subquiver G) := ⟨λ a b, set.univ⟩
instance {V} {G : quiver V} : inhabited (wide_subquiver G) := ⟨⊤⟩

/-- `G.sum H` takes the disjoint union of the arrows of `G` and `H`. -/
protected def sum {V} (G H : quiver V) : quiver V :=
⟨λ a b, G.arrow a b ⊕ H.arrow a b⟩

/-- `G.opposite` reverses the direction of all arrows of `G`. -/
protected def opposite {V} (G : quiver V) : quiver V :=
⟨flip G.arrow⟩

/-- `G.symmetrify` adds to `G` the reversal of all arrows of `G`. -/
def symmetrify {V} (G : quiver V) : quiver V :=
G.sum G.opposite

@[simp] lemma empty_arrow {V} (a b : V) : (quiver.empty V).arrow a b = pempty := rfl

@[simp] lemma sum_arrow {V} (G H : quiver V) (a b : V) :
  (G.sum H).arrow a b = (G.arrow a b ⊕ H.arrow a b) := rfl

@[simp] lemma opposite_arrow {V} (G : quiver V) (a b : V) :
  G.opposite.arrow a b = G.arrow b a := rfl

@[simp] lemma symmetrify_arrow {V} (G : quiver V) (a b : V) :
  G.symmetrify.arrow a b = (G.arrow a b ⊕ G.arrow b a) := rfl

@[simp] lemma opposite_opposite {V} (G : quiver V) : G.opposite.opposite = G :=
by { cases G, refl }

/-- `G.total` is the type of _all_ arrows of `G`. -/
@[ext] protected structure total {V} (G : quiver.{v u} V) : Sort (max (u+1) v) :=
(source : V)
(target : V)
(arrow : G.arrow source target)

instance {V} [inhabited V] {G : quiver V} [inhabited (G.arrow (default V) (default V))] :
  inhabited G.total :=
⟨⟨default V, default V, default _⟩⟩

/-- A wide subquiver `H` of `G.symmetrify` determines a wide subquiver of `G`, containing an
    an arrow `e` if either `e` or its reversal is in `H`. -/
def wide_subquiver_symmetrify {V} {G : quiver V} :
  wide_subquiver G.symmetrify → wide_subquiver G :=
λ H a b, { e | sum.inl e ∈ H a b ∨ sum.inr e ∈ H b a }

/-- A wide subquiver of `G` can equivalently be viewed as a total set of arrows. -/
def wide_subquiver_equiv_set_total {V} {G : quiver V} :
  wide_subquiver G ≃ set G.total :=
{ to_fun := λ H, { e | e.arrow ∈ H e.source e.target },
  inv_fun := λ S a b, { e | total.mk a b e ∈ S },
  left_inv := λ H, rfl,
  right_inv := by { intro S, ext, cases x, refl } }

/-- `G.path a b` is the type of paths from `a` to `b` through the arrows of `G`. -/
inductive path {V} (G : quiver.{v u} V) (a : V) : V → Sort (max (u+1) v)
| nil  : path a
| cons : Π {b c : V}, path b → G.arrow b c → path c

/-- The length of a path is the number of edges it uses. -/
def path.length {V} {G : quiver V} {a : V} : Π {b}, G.path a b → ℕ
| _ path.nil        := 0
| _ (path.cons p _) := p.length + 1

/-- A quiver is an arborescence when there is a unique path from the default vertex
    to every other vertex. -/
class arborescence {V} (T : quiver.{v u} V) : Sort (max (u+1) v) :=
(root : V)
(unique_path : Π (b : V), unique (T.path root b))

/-- The root of an arborescence. -/
protected def root {V} (T : quiver V) [arborescence T] : V :=
arborescence.root T

instance {V} (T : quiver V) [arborescence T] (b : V) : unique (T.path T.root b) :=
arborescence.unique_path b

/-- An `L`-labelling of a quiver assigns to every arrow an element of `L`. -/
def labelling {V} (G : quiver V) (L) := Π a b, G.arrow a b → L

instance {V} (G : quiver V) (L) [inhabited L] : inhabited (G.labelling L) :=
⟨λ a b e, default L⟩

end quiver

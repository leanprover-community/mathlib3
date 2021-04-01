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

/-- The length of a path is the number of arrows it uses. -/
def path.length {V} {G : quiver V} {a : V} : Π {b}, G.path a b → ℕ
| _ path.nil        := 0
| _ (path.cons p _) := p.length + 1

@[simp] lemma path.length_nil {V} {G : quiver V} {a : V} :
  (path.nil : G.path a a).length = 0 := rfl

@[simp] lemma path.length_cons {V} {G : quiver V} (a b c : V) (p : G.path a b)
  (e : G.arrow b c) : (p.cons e).length = p.length + 1 := rfl

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

/-- To show that `T : quiver V` is an arborescence with root `r : V`, it suffices to
  - provide a height function `V → ℕ` such that every arrow goes from a
    lower vertex to a higher vertex,
  - show that every vertex has at most one arrow to it, and
  - show that every vertex other than `r` has an arrow to it. -/
noncomputable def arborescence_mk {V} (T : quiver V) (r : V)
  (height : V → ℕ)
  (height_lt : ∀ ⦃a b⦄, T.arrow a b → height a < height b)
  (unique_arrow : ∀ ⦃a b c⦄ (e : T.arrow a c) (f : T.arrow b c), a = b ∧ e == f)
  (root_or_arrow : ∀ b, b = r ∨ ∃ a, nonempty (T.arrow a b)) : arborescence T :=
{ root := r,
  unique_path := λ b, ⟨classical.inhabited_of_nonempty
    begin
      rcases (show ∃ n, height b < n, from ⟨_, lt_add_one _⟩) with ⟨n, hn⟩,
      induction n with n ih generalizing b,
      { exact false.elim (nat.not_lt_zero _ hn) },
      rcases root_or_arrow b with ⟨⟨⟩⟩ | ⟨a, ⟨e⟩⟩,
      { exact ⟨path.nil⟩ },
      { rcases ih a (lt_of_lt_of_le (height_lt e) (nat.lt_succ_iff.mp hn)) with ⟨p⟩,
        exact ⟨p.cons e⟩ }
    end,
    begin
      have height_le : ∀ {a b}, T.path a b → height a ≤ height b,
      { intros a b p, induction p with b c p e ih, refl,
        exact le_of_lt (lt_of_le_of_lt ih (height_lt e)) },
      suffices : ∀ p q : T.path r b, p = q,
      { intro p, apply this },
      intros p q, induction p with a c p e ih; cases q with b _ q f,
      { refl },
      { exact false.elim (lt_irrefl _ (lt_of_le_of_lt (height_le q) (height_lt f))) },
      { exact false.elim (lt_irrefl _ (lt_of_le_of_lt (height_le p) (height_lt e))) },
      { rcases unique_arrow e f with ⟨⟨⟩, ⟨⟩⟩, rw ih },
    end ⟩ }

/-- `G.rooted_connected r` means that there is a path from `r` to any other vertex. -/
class rooted_connected {V} (G : quiver V) (r : V) : Prop :=
(nonempty_path : ∀ b : V, nonempty (G.path r b))

attribute [instance] rooted_connected.nonempty_path

variables {V : Type*} (G : quiver.{v+1} V) (r : V) [G.rooted_connected r]

/-- A path from `r` of minimal length. -/
noncomputable def shortest_path (b : V) : G.path r b :=
well_founded.min (measure_wf path.length) set.univ set.univ_nonempty

/-- The length of a path is at least the length of the shortest path -/
lemma shortest_path_spec {a : V} (p : G.path r a) :
  (G.shortest_path r a).length ≤ p.length :=
not_lt.mp (well_founded.not_lt_min (measure_wf _) set.univ _ trivial)

/-- A subquiver which by construction is an arborescence. -/
def geodesic_subtree : wide_subquiver G :=
λ a b, { e | ∃ p : G.path r a, shortest_path G r b = p.cons e }

noncomputable instance geodesic_arborescence : (G.geodesic_subtree r).quiver.arborescence :=
arborescence_mk _ r (λ a, (G.shortest_path r a).length)
(by { rintros a b ⟨e, p, h⟩,
  rw [h, path.length_cons, nat.lt_succ_iff], apply shortest_path_spec })
(by { rintros a b c ⟨e, p, h⟩ ⟨f, q, j⟩, cases h.symm.trans j, split; refl })
(by { intro b, have : ∃ p, G.shortest_path r b = p := ⟨_, rfl⟩,
  rcases this with ⟨p, hp⟩, cases p with a _ p e,
  { exact or.inl rfl }, { exact or.inr ⟨a, ⟨⟨e, p, hp⟩⟩⟩ } })

end quiver

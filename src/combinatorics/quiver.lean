/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import data.equiv.basic
import order.well_founded
import data.nat.basic
import data.opposite

/-!
# Quivers

This module defines quivers. A quiver on a type `V` of vertices assigns to every
pair `a b : V` of vertices a type `a ⟶ b` of arrows from `a` to `b`. This
is a very permissive notion of directed graph.

## Implementation notes

Currently `quiver` is defined with `arrow : V → V → Sort v`.
This is different from the category theory setup,
where we insist that morphisms live in some `Type`.
There's some balance here: it's nice to allow `Prop` to ensure there are no multiple arrows,
but it is also results in error-prone universe signatures when constraints require a `Type`.
-/

open opposite

-- We use the same universe order as in category theory.
-- See note [category_theory universes]
universes v v₁ v₂ u u₁ u₂

/--
A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
a type `a ⟶ b` of arrows from `a` to `b`.

For graphs with no repeated edges, one can use `quiver.{0} V`, which ensures
`a ⟶ b : Prop`. For multigraphs, one can use `quiver.{v+1} V`, which ensures
`a ⟶ b : Type v`.

Because `category` will later extend this class, we call the field `hom`.
Except when constructing instances, you should rarely see this, and use the `⟶` notation instead.
-/
class quiver (V : Type u) :=
(hom : V → V → Sort v)

infixr ` ⟶ `:10 := quiver.hom -- type as \h

/--
A morphism of quivers. As we will later have categorical functors extend this structure,
we call it a `prefunctor`.
-/
structure prefunctor (V : Type u₁) [quiver.{v₁} V] (W : Type u₂) [quiver.{v₂} W] :=
(obj [] : V → W)
(map : Π {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y))

namespace prefunctor

/--
The identity morphism between quivers.
-/
@[simps]
def id (V : Type*) [quiver V] : prefunctor V V :=
{ obj := id,
  map := λ X Y f, f, }

instance (V : Type*) [quiver V] : inhabited (prefunctor V V) := ⟨id V⟩

/--
Composition of morphisms between quivers.
-/
@[simps]
def comp {U : Type*} [quiver U] {V : Type*} [quiver V] {W : Type*} [quiver W]
  (F : prefunctor U V) (G : prefunctor V W) : prefunctor U W :=
{ obj := λ X, G.obj (F.obj X),
  map := λ X Y f, G.map (F.map f), }

end prefunctor

/-- A wide subquiver `H` of `G` picks out a set `H a b` of arrows from `a` to `b`
    for every pair of vertices `a b`.

    NB: this does not work for `Prop`-valued quivers. It requires `G : quiver.{v+1} V`. -/
def wide_subquiver (V) [quiver.{v+1} V] :=
Π a b : V, set (a ⟶ b)

/-- A type synonym for `V`, when thought of as a quiver having only the arrows from
some `wide_subquiver`. -/
@[nolint unused_arguments has_inhabited_instance]
def wide_subquiver.to_Type (V) [quiver V] (H : wide_subquiver V) : Type u := V

instance wide_subquiver_has_coe_to_sort {V} [quiver V] :
  has_coe_to_sort (wide_subquiver V) (Type u) :=
{ coe := λ H, wide_subquiver.to_Type V H }

/-- A wide subquiver viewed as a quiver on its own. -/
instance wide_subquiver.quiver {V} [quiver V] (H : wide_subquiver V) : quiver H :=
⟨λ a b, H a b⟩

namespace quiver

/-- A type synonym for a quiver with no arrows. -/
@[nolint has_inhabited_instance]
def empty (V) : Type u := V

instance empty_quiver (V : Type u) : quiver.{u} (empty V) := ⟨λ a b, pempty⟩

@[simp] lemma empty_arrow {V : Type u} (a b : empty V) : (a ⟶ b) = pempty := rfl

instance {V} [quiver V] : has_bot (wide_subquiver V) := ⟨λ a b, ∅⟩
instance {V} [quiver V] : has_top (wide_subquiver V) := ⟨λ a b, set.univ⟩
instance {V} [quiver V] : inhabited (wide_subquiver V) := ⟨⊤⟩

/-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
instance opposite {V} [quiver V] : quiver Vᵒᵖ :=
⟨λ a b, (unop b) ⟶ (unop a)⟩

/--
The opposite of an arrow in `V`.
-/
def hom.op {V} [quiver V] {X Y : V} (f : X ⟶ Y) : op Y ⟶ op X := f
/--
Given an arrow in `Vᵒᵖ`, we can take the "unopposite" back in `V`.
-/
def hom.unop {V} [quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X := f

attribute [irreducible] quiver.opposite

/-- A type synonym for the symmetrized quiver (with an arrow both ways for each original arrow).
    NB: this does not work for `Prop`-valued quivers. It requires `[quiver.{v+1} V]`. -/
@[nolint has_inhabited_instance]
def symmetrify (V) : Type u := V

instance symmetrify_quiver (V : Type u) [quiver V] : quiver (symmetrify V) :=
⟨λ a b : V, (a ⟶ b) ⊕ (b ⟶ a)⟩

/-- `total V` is the type of _all_ arrows of `V`. -/
-- TODO Unify with `category_theory.arrow`? (The fields have been named to match.)
@[ext, nolint has_inhabited_instance]
structure total (V : Type u) [quiver.{v} V] : Sort (max (u+1) v) :=
(left : V)
(right : V)
(hom : left ⟶ right)

/-- A wide subquiver `H` of `G.symmetrify` determines a wide subquiver of `G`, containing an
    an arrow `e` if either `e` or its reversal is in `H`. -/
-- Without the explicit universe level in `quiver.{v+1}` Lean comes up with
-- `quiver.{max u_2 u_3 + 1}`. This causes problems elsewhere, so we write `quiver.{v+1}`.
def wide_subquiver_symmetrify {V} [quiver.{v+1} V] :
  wide_subquiver (symmetrify V) → wide_subquiver V :=
λ H a b, { e | sum.inl e ∈ H a b ∨ sum.inr e ∈ H b a }

/-- A wide subquiver of `G` can equivalently be viewed as a total set of arrows. -/
def wide_subquiver_equiv_set_total {V} [quiver V] :
  wide_subquiver V ≃ set (total V) :=
{ to_fun := λ H, { e | e.hom ∈ H e.left e.right },
  inv_fun := λ S a b, { e | total.mk a b e ∈ S },
  left_inv := λ H, rfl,
  right_inv := by { intro S, ext, cases x, refl } }

/-- `G.path a b` is the type of paths from `a` to `b` through the arrows of `G`. -/
inductive path {V : Type u} [quiver.{v} V] (a : V) : V → Sort (max (u+1) v)
| nil  : path a
| cons : Π {b c : V}, path b → (b ⟶ c) → path c

/-- An arrow viewed as a path of length one. -/
def hom.to_path {V} [quiver V] {a b : V} (e : a ⟶ b) : path a b :=
path.nil.cons e

namespace path

variables {V : Type u} [quiver V]

/-- The length of a path is the number of arrows it uses. -/
def length {a : V} : Π {b : V}, path a b → ℕ
| _ path.nil        := 0
| _ (path.cons p _) := p.length + 1

@[simp] lemma length_nil {a : V} :
  (path.nil : path a a).length = 0 := rfl

@[simp] lemma length_cons (a b c : V) (p : path a b)
  (e : b ⟶ c) : (p.cons e).length = p.length + 1 := rfl

/-- Composition of paths. -/
def comp {a b : V} : Π {c}, path a b → path b c → path a c
| _ p (path.nil) := p
| _ p (path.cons q e) := (p.comp q).cons e

@[simp] lemma comp_cons {a b c d : V} (p : path a b) (q : path b c) (e : c ⟶ d) :
  p.comp (q.cons e) = (p.comp q).cons e := rfl
@[simp] lemma comp_nil {a b : V} (p : path a b) : p.comp path.nil = p := rfl
@[simp] lemma nil_comp {a : V} : ∀ {b} (p : path a b), path.nil.comp p = p
| a path.nil := rfl
| b (path.cons p e) := by rw [comp_cons, nil_comp]
@[simp] lemma comp_assoc {a b c : V} : ∀ {d}
  (p : path a b) (q : path b c) (r : path c d),
    (p.comp q).comp r = p.comp (q.comp r)
| c p q path.nil := rfl
| d p q (path.cons r e) := by rw [comp_cons, comp_cons, comp_cons, comp_assoc]

end path

end quiver

namespace prefunctor

open quiver

variables {V : Type u₁} [quiver.{v₁} V] {W : Type u₂} [quiver.{v₂} W] (F : prefunctor V W)

/-- The image of a path under a prefunctor. -/
def map_path {a : V} :
  Π {b : V}, path a b → path (F.obj a) (F.obj b)
| _ path.nil := path.nil
| _ (path.cons p e) := path.cons (map_path p) (F.map e)

@[simp] lemma map_path_nil (a : V) : F.map_path (path.nil : path a a) = path.nil := rfl
@[simp] lemma map_path_cons {a b c : V} (p : path a b) (e : b ⟶ c) :
  F.map_path (path.cons p e) = path.cons (F.map_path p) (F.map e) := rfl

@[simp] lemma map_path_comp {a b : V} (p : path a b) :
  ∀ {c : V} (q : path b c), F.map_path (p.comp q) = (F.map_path p).comp (F.map_path q)
| _ path.nil := rfl
| _ (path.cons p e) := begin dsimp, rw [map_path_comp], end

end prefunctor

namespace quiver

/-- A quiver is an arborescence when there is a unique path from the default vertex
    to every other vertex. -/
class arborescence (V : Type u) [quiver.{v} V] : Type (max u v) :=
(root : V)
(unique_path : Π (b : V), unique (path root b))

/-- The root of an arborescence. -/
def root (V : Type u) [quiver V] [arborescence V] : V :=
arborescence.root

instance {V : Type u} [quiver V] [arborescence V] (b : V) : unique (path (root V) b) :=
arborescence.unique_path b

/-- An `L`-labelling of a quiver assigns to every arrow an element of `L`. -/
def labelling (V : Type u) [quiver V] (L : Sort*) := Π ⦃a b : V⦄, (a ⟶ b) → L

instance {V : Type u} [quiver V] (L) [inhabited L] : inhabited (labelling V L) :=
⟨λ a b e, default L⟩

/-- To show that `[quiver V]` is an arborescence with root `r : V`, it suffices to
  - provide a height function `V → ℕ` such that every arrow goes from a
    lower vertex to a higher vertex,
  - show that every vertex has at most one arrow to it, and
  - show that every vertex other than `r` has an arrow to it. -/
noncomputable def arborescence_mk {V : Type u} [quiver V] (r : V)
  (height : V → ℕ)
  (height_lt : ∀ ⦃a b⦄, (a ⟶ b) → height a < height b)
  (unique_arrow : ∀ ⦃a b c : V⦄ (e : a ⟶ c) (f : b ⟶ c), a = b ∧ e == f)
  (root_or_arrow : ∀ b, b = r ∨ ∃ a, nonempty (a ⟶ b)) : arborescence V :=
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
      have height_le : ∀ {a b}, path a b → height a ≤ height b,
      { intros a b p, induction p with b c p e ih, refl,
        exact le_of_lt (lt_of_le_of_lt ih (height_lt e)) },
      suffices : ∀ p q : path r b, p = q,
      { intro p, apply this },
      intros p q, induction p with a c p e ih; cases q with b _ q f,
      { refl },
      { exact false.elim (lt_irrefl _ (lt_of_le_of_lt (height_le q) (height_lt f))) },
      { exact false.elim (lt_irrefl _ (lt_of_le_of_lt (height_le p) (height_lt e))) },
      { rcases unique_arrow e f with ⟨⟨⟩, ⟨⟩⟩, rw ih },
    end ⟩ }

/-- `rooted_connected r` means that there is a path from `r` to any other vertex. -/
class rooted_connected {V : Type u} [quiver V] (r : V) : Prop :=
(nonempty_path : ∀ b : V, nonempty (path r b))

attribute [instance] rooted_connected.nonempty_path

section geodesic_subtree

variables {V : Type u} [quiver.{v+1} V] (r : V) [rooted_connected r]

/-- A path from `r` of minimal length. -/
noncomputable def shortest_path (b : V) : path r b :=
well_founded.min (measure_wf path.length) set.univ set.univ_nonempty

/-- The length of a path is at least the length of the shortest path -/
lemma shortest_path_spec {a : V} (p : path r a) :
  (shortest_path r a).length ≤ p.length :=
not_lt.mp (well_founded.not_lt_min (measure_wf _) set.univ _ trivial)

/-- A subquiver which by construction is an arborescence. -/
def geodesic_subtree : wide_subquiver V :=
λ a b, { e | ∃ p : path r a, shortest_path r b = p.cons e }

noncomputable instance geodesic_arborescence : arborescence (geodesic_subtree r) :=
arborescence_mk r (λ a, (shortest_path r a).length)
(by { rintros a b ⟨e, p, h⟩,
  rw [h, path.length_cons, nat.lt_succ_iff], apply shortest_path_spec })
(by { rintros a b c ⟨e, p, h⟩ ⟨f, q, j⟩, cases h.symm.trans j, split; refl })
(by { intro b, have : ∃ p, shortest_path r b = p := ⟨_, rfl⟩,
  rcases this with ⟨p, hp⟩, cases p with a _ p e,
  { exact or.inl rfl }, { exact or.inr ⟨a, ⟨⟨e, p, hp⟩⟩⟩ } })

end geodesic_subtree

variables (V : Type u) [quiver.{v+1} V]

/-- A quiver `has_reverse` if we can reverse an arrow `p` from `a` to `b` to get an arrow
    `p.reverse` from `b` to `a`.-/
class has_reverse :=
(reverse' : Π {a b : V}, (a ⟶ b) → (b ⟶ a))

instance : has_reverse (symmetrify V) := ⟨λ a b e, e.swap⟩

variables {V} [has_reverse V]

/-- Reverse the direction of an arrow. -/
def reverse {a b : V} : (a ⟶ b) → (b ⟶ a) := has_reverse.reverse'

/-- Reverse the direction of a path. -/
def path.reverse {a : V} : Π {b}, path a b → path b a
| a path.nil := path.nil
| b (path.cons p e) := (reverse e).to_path.comp p.reverse

variables (V)

/-- Two vertices are related in the zigzag setoid if there is a
    zigzag of arrows from one to the other. -/
def zigzag_setoid : setoid V :=
⟨λ a b, nonempty (path (a : symmetrify V) (b : symmetrify V)),
 λ a, ⟨path.nil⟩,
 λ a b ⟨p⟩, ⟨p.reverse⟩,
 λ a b c ⟨p⟩ ⟨q⟩, ⟨p.comp q⟩⟩

/-- The type of weakly connected components of a directed graph. Two vertices are
    in the same weakly connected component if there is a zigzag of arrows from one
    to the other. -/
def weakly_connected_component : Type* := quotient (zigzag_setoid V)

namespace weakly_connected_component
variable {V}

/-- The weakly connected component corresponding to a vertex. -/
protected def mk : V → weakly_connected_component V := quotient.mk'

instance : has_coe_t V (weakly_connected_component V) := ⟨weakly_connected_component.mk⟩
instance [inhabited V] : inhabited (weakly_connected_component V) := ⟨↑(default V)⟩

protected lemma eq (a b : V) :
  (a : weakly_connected_component V) = b ↔ nonempty (path (a : symmetrify V) (b : symmetrify V)) :=
quotient.eq'

end weakly_connected_component

end quiver

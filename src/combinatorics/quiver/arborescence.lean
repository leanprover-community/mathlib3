/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import order.well_founded
import data.nat.basic
import combinatorics.quiver.subquiver
import combinatorics.quiver.path

/-!
# Arborescences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A quiver `V` is an arborescence (or directed rooted tree) when we have a root vertex `root : V` such
that for every `b : V` there is a unique path from `root` to `b`.

## Main definitions

- `quiver.arborescence V`: a typeclass asserting that `V` is an arborescence
- `arborescence_mk`: a convenient way of proving that a quiver is an arborescence
- `rooted_connected r`: a typeclass asserting that there is at least one path from `r` to `b` for
every `b`.
- `geodesic_subtree r`: given `[rooted_conntected r]`, this is a subquiver of `V` which contains
just enough edges to include a shortest path from `r` to `b` for every `b`.
- `geodesic_arborescence : arborescence (geodesic_subtree r)`: an instance saying that the geodesic
subtree is an arborescence. This proves the directed analogue of 'every connected graph has a
spanning tree'. This proof avoids the use of Zorn's lemma.
-/

open opposite
universes v u

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
      rcases (show ∃ n, height b < n, from ⟨_, nat.lt.base _⟩) with ⟨n, hn⟩,
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
(by { rintros a b ⟨e, p, h⟩, rw [h, path.length_cons, nat.lt_succ_iff], apply shortest_path_spec })
(by { rintros a b c ⟨e, p, h⟩ ⟨f, q, j⟩, cases h.symm.trans j, split; refl })
begin
  intro b,
  rcases hp : shortest_path r b with (_ | ⟨p, e⟩),
  { exact or.inl rfl },
  { exact or.inr ⟨_, ⟨⟨e, p, hp⟩⟩⟩ }
end

end geodesic_subtree

end quiver

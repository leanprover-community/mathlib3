/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import combinatorics.quiver.basic
import combinatorics.quiver.path
import data.sum.basic
import tactic.nth_rewrite
/-!
## Symmetric quivers and arrow reversal

This file contains constructions related to symmetric quivers:

* `symmetrify V` adds formal inverses to each arrow of `V`.
* `has_reverse` is the class of quivers where each arrow has an assigned formal inverse.
* `has_involutive_reverse` extends `has_reverse` by requiring that the reverse of the reverse
  is equal to the original arrow.
* `prefunctor.preserve_reverse` is the class of prefunctors mapping reverses to reverses.
* `symmetrify.of`, `symmetrify.lift`, and the associated lemmas witness the universal property
  of `symmetrify`.
-/

universes v u w

namespace quiver

/-- A type synonym for the symmetrized quiver (with an arrow both ways for each original arrow).
    NB: this does not work for `Prop`-valued quivers. It requires `[quiver.{v+1} V]`. -/
@[nolint has_nonempty_instance]
def symmetrify (V) : Type u := V

instance symmetrify_quiver (V : Type u) [quiver V] : quiver (symmetrify V) :=
⟨λ a b : V, (a ⟶ b) ⊕ (b ⟶ a)⟩

variables (U V W : Type*) [quiver.{u+1} U] [quiver.{v+1} V]

/-- A quiver `has_reverse` if we can reverse an arrow `p` from `a` to `b` to get an arrow
    `p.reverse` from `b` to `a`.-/
class has_reverse :=
(reverse' : Π {a b : V}, (a ⟶ b) → (b ⟶ a))

/-- Reverse the direction of an arrow. -/
def reverse {V} [quiver.{v+1} V] [has_reverse V] {a b : V} : (a ⟶ b) → (b ⟶ a) :=
  has_reverse.reverse'

/-- A quiver `has_involutive_reverse` if reversing twice is the identity.`-/
class has_involutive_reverse extends has_reverse V :=
(inv' : Π {a b : V} (f : a ⟶ b), reverse (reverse f) = f)

@[simp] lemma reverse_reverse {V} [quiver.{v+1} V] [h : has_involutive_reverse V]
  {a b : V} (f : a ⟶ b) : reverse (reverse f) = f := by apply h.inv'

@[simp] lemma reverse_eq_reverse_iff {V} [quiver.{v+1} V] [h : has_involutive_reverse V]
  {a b : V} (f g : a ⟶ b) : reverse f = reverse g ↔ f = g :=
begin
  split,
  { rintro h, simpa using congr_arg quiver.reverse h, },
  { rintro h, congr, assumption, },
end

lemma eq_reverse_iff {V} [quiver.{v+1} V] [h : has_involutive_reverse V]
  {a b : V} (f : a ⟶ b) (g : b ⟶ a) : f = reverse g ↔ reverse f = g :=
begin
  nth_rewrite_lhs 0 ←reverse_reverse f,
  rw reverse_eq_reverse_iff,
end

variables {U V W}

/-- A prefunctor preserving reversal of arrows -/
class _root_.prefunctor.preserves_reverse [has_reverse U] [has_reverse V] (φ : U ⥤q V) :=
(map_reverse' : ∀ {u v : U} (e : u ⟶ v), φ.map (reverse e) = reverse (φ.map e))

@[simp] lemma _root_.prefunctor.map_reverse  [has_reverse U] [has_reverse V] (φ : U ⥤q V)
  [φ.preserves_reverse] {u v : U} (e : u ⟶ v) : φ.map (reverse e) = reverse (φ.map e) :=
prefunctor.preserves_reverse.map_reverse' e

instance _root_.prefunctor.preserves_reverse_comp [quiver.{w+1} W]
  [has_reverse U] [has_reverse V] [has_reverse W] (φ : U ⥤q V) (ψ : V ⥤q W)
  [φ.preserves_reverse] [ψ.preserves_reverse] : (φ ⋙q ψ).preserves_reverse :=
{ map_reverse' := λ u v e, by { simp only [prefunctor.comp_map, prefunctor.map_reverse], } }

instance _root_.prefunctor.preserves_reverse_id [has_reverse U] :
  (prefunctor.id U).preserves_reverse :=
{ map_reverse' := λ u v e, rfl }

instance : has_reverse (symmetrify V) := ⟨λ a b e, e.swap⟩
instance : has_involutive_reverse (symmetrify V) :=
{ to_has_reverse := ⟨λ a b e, e.swap⟩,
  inv' := λ a b e, congr_fun sum.swap_swap_eq e }

@[simp] lemma symmetrify_reverse {a b : symmetrify V} (e : a ⟶ b) :
  reverse e = e.swap := rfl

/-- Shorthand for the "forward" arrow corresponding to `f` in `symmetrify V` -/
abbreviation hom.to_pos {X Y : V} (f : X ⟶ Y) :
  (quiver.symmetrify_quiver V).hom X Y := sum.inl f

/-- Shorthand for the "backward" arrow corresponding to `f` in `symmetrify V` -/
abbreviation hom.to_neg {X Y : V} (f : X ⟶ Y) :
  (quiver.symmetrify_quiver V).hom Y X := sum.inr f

/-- Reverse the direction of a path. -/
@[simp] def path.reverse [has_reverse V] {a : V} : Π {b}, path a b → path b a
| a path.nil := path.nil
| b (path.cons p e) := (reverse e).to_path.comp p.reverse

@[simp] lemma path.reverse_to_path [has_reverse V] {a b : V} (f : a ⟶ b) :
  f.to_path.reverse = (reverse f).to_path := rfl

@[simp] lemma path.reverse_comp [has_reverse V] {a b c : V} (p : path a b) (q : path b c) :
  (p.comp q).reverse = q.reverse.comp p.reverse := by
{ induction q, { simp, }, { simp [q_ih], }, }

@[simp] lemma path.reverse_reverse [h : has_involutive_reverse V] {a b : V} (p : path a b) :
  p.reverse.reverse = p :=
begin
  induction p,
  { simp, },
  { simp only [path.reverse, path.reverse_comp, path.reverse_to_path, reverse_reverse, p_ih],
    refl, },
end

namespace symmetrify

/-- The inclusion of a quiver in its symmetrification -/
def of : prefunctor V (symmetrify V) :=
{ obj := id,
  map := λ X Y f, sum.inl f }

/-- Given a quiver `V'` with reversible arrows, a prefunctor to `V'` can be lifted to one from
    `symmetrify V` to `V'` -/
def lift {V' : Type*} [quiver V'] [has_reverse V'] (φ : V ⥤q V') :
  (symmetrify V) ⥤q V' :=
{ obj := φ.obj,
  map := λ X Y f, sum.rec (λ fwd, φ.map fwd) (λ bwd, reverse (φ.map bwd)) f }

lemma lift_spec  (V' : Type*) [quiver V'] [has_reverse V'] (φ : V ⥤q V') :
  of ⋙q (lift φ) = φ :=
begin
  fapply prefunctor.ext,
  { rintro X, refl, },
  { rintros X Y f, refl, },
end

lemma lift_reverse  (V' : Type*) [quiver V'] [h : has_involutive_reverse V']
  (φ : V ⥤q V')
  {X Y : symmetrify V} (f : X ⟶ Y) :
  (lift φ).map (quiver.reverse f) = quiver.reverse ((lift φ).map f) :=
begin
  dsimp [lift], cases f,
  { simp only, refl, },
  { simp only, rw h.inv', refl, }
end

/-- `lift φ` is the only prefunctor extending `φ` and preserving reverses. -/
lemma lift_unique (V' : Type*) [quiver V'] [has_reverse V']
  (φ : V ⥤q V')
  (Φ : (symmetrify V) ⥤q V')
  (hΦ : of ⋙q Φ = φ) [hΦrev : Φ.preserves_reverse] :
  Φ = lift φ :=
begin
  subst_vars,
  fapply prefunctor.ext,
  { rintro X, refl, },
  { rintros X Y f,
    cases f,
    { refl, },
    { dsimp [lift,of],
      simp only [←prefunctor.map_reverse, symmetrify_reverse, sum.swap_inl], }, },
end

/-- A prefunctor canonically defines a prefunctor of the symmetrifications. -/
@[simps] def _root_.prefunctor.symmetrify (φ : U ⥤q V) : (symmetrify U) ⥤q (symmetrify V) :=
{ obj := φ.obj,
  map := λ X Y, sum.map φ.map φ.map }

instance _root_.prefunctor.symmetrify_preserves_reverse  (φ : U ⥤q V) :
  prefunctor.preserves_reverse φ.symmetrify := ⟨λ u v e, by { cases e; refl }⟩

end symmetrify

namespace push

variables {W} (σ : V → W)

instance [has_reverse V] : has_reverse (push σ) :=
{ reverse' := λ a b F, by { cases F, constructor, apply reverse, exact F_f, } }

instance [h : quiver.has_involutive_reverse V] : quiver.has_involutive_reverse (push σ) :=
{ reverse' := λ a b F, by { cases F, constructor, apply reverse, exact F_f, },
  inv' :=  λ a b F, by { cases F, dsimp [reverse], congr, apply h.inv', } }

@[simp] lemma of_reverse [h : has_involutive_reverse V]  (X Y : V) (f : X ⟶ Y):
  (reverse $ ((of σ)).map f) = ((of σ)).map (reverse f) := rfl

end push

/--
A quiver with involutive reverses is connected iff there exists a path between any pair of
vertices.
-/
@[nolint unused_arguments]
def is_connected (V) [quiver.{u+1} V] [has_involutive_reverse V] := ∀ (X Y : V), nonempty (path X Y)

end quiver

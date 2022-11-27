/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import combinatorics.quiver.subquiver
import combinatorics.quiver.path
import data.sum.basic

/-!
## Weakly connected components

For a quiver `V`, we build a quiver `symmetrify V` by adding a reversal of every edge.
Informally, a path in `symmetrify V` corresponds to a 'zigzag' in `V`. This lets us
define the type `weakly_connected_component V` as the quotient of `V` by the relation which
identifies `a` with `b` if there is a path from `a` to `b` in `symmetrify V`. (These
zigzags can be seen as a proof-relevant analogue of `eqv_gen`.)

Strongly connected components have not yet been defined.
-/
universes v u

namespace quiver

/-- A type synonym for the symmetrized quiver (with an arrow both ways for each original arrow).
    NB: this does not work for `Prop`-valued quivers. It requires `[quiver.{v+1} V]`. -/
@[nolint has_nonempty_instance]
def symmetrify (V) : Type u := V

instance symmetrify_quiver (V : Type u) [quiver V] : quiver (symmetrify V) :=
⟨λ a b : V, (a ⟶ b) ⊕ (b ⟶ a)⟩

variables (V : Type u) [quiver.{v+1} V]

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

variables {V}

instance : has_reverse (symmetrify V) := ⟨λ a b e, e.swap⟩
instance : has_involutive_reverse (symmetrify V) :=
{ to_has_reverse := ⟨λ a b e, e.swap⟩,
  inv' := λ a b e, congr_fun sum.swap_swap_eq e }


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
  p.reverse.reverse = p := by
{ induction p,
  { simp, },
  { simp only [path.reverse, path.reverse_comp, path.reverse_to_path, reverse_reverse, p_ih],
    refl, }, }

/-- The inclusion of a quiver in its symmetrification -/
def symmetrify.of : prefunctor V (symmetrify V) :=
{ obj := id,
  map := λ X Y f, sum.inl f }

/-- Given a quiver `V'` with reversible arrows, a prefunctor to `V'` can be lifted to one from
    `symmetrify V` to `V'` -/
def symmetrify.lift {V' : Type*} [quiver V'] [has_reverse V'] (φ : prefunctor V V') :
  prefunctor (symmetrify V) V' :=
{ obj := φ.obj,
  map := λ X Y f, sum.rec (λ fwd, φ.map fwd) (λ bwd, reverse (φ.map bwd)) f }

lemma symmetrify.lift_spec  (V' : Type*) [quiver V'] [has_reverse V'] (φ : prefunctor V V') :
  symmetrify.of.comp (symmetrify.lift φ) = φ :=
begin
  fapply prefunctor.ext,
  { rintro X, refl, },
  { rintros X Y f, refl, },
end

lemma symmetrify.lift_reverse  (V' : Type*) [quiver V'] [h : has_involutive_reverse V']
  (φ : prefunctor V V')
  {X Y : symmetrify V} (f : X ⟶ Y) :
  (symmetrify.lift φ).map (quiver.reverse f) = quiver.reverse ((symmetrify.lift φ).map f) :=
begin
  dsimp [symmetrify.lift], cases f,
  { simp only, refl, },
  { simp only, rw h.inv', refl, }
end

/-- `lift φ` is the only prefunctor extending `φ` and preserving reverses. -/
lemma symmetrify.lift_unique (V' : Type*) [quiver V'] [has_reverse V']
  (φ : prefunctor V V')
  (Φ : prefunctor (symmetrify V) V')
  (hΦ : symmetrify.of.comp Φ = φ)
  (hΦinv : ∀ {X Y : V} (f : X ⟶ Y), Φ.map (reverse f) = reverse (Φ.map f)) :
  Φ = symmetrify.lift φ :=
begin
  subst_vars,
  fapply prefunctor.ext,
  { rintro X, refl, },
  { rintros X Y f,
    cases f,
    { refl, },
    { dsimp [symmetrify.lift,symmetrify.of],
      convert hΦinv (sum.inl f), }, },
end

variables (V)

/-- Two vertices are related in the zigzag setoid if there is a
    zigzag of arrows from one to the other. -/
def zigzag_setoid : setoid V :=
⟨λ a b, nonempty (@path (symmetrify V) _ a b),
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
instance [inhabited V] : inhabited (weakly_connected_component V) := ⟨show V, from default⟩

protected lemma eq (a b : V) :
  (a : weakly_connected_component V) = b ↔ nonempty (@path (symmetrify V) _ a b) :=
quotient.eq'

end weakly_connected_component

variable {V}

/-- A wide subquiver `H` of `G.symmetrify` determines a wide subquiver of `G`, containing an
    an arrow `e` if either `e` or its reversal is in `H`. -/
-- Without the explicit universe level in `quiver.{v+1}` Lean comes up with
-- `quiver.{max u_2 u_3 + 1}`. This causes problems elsewhere, so we write `quiver.{v+1}`.
def wide_subquiver_symmetrify (H : wide_subquiver (symmetrify V)) : wide_subquiver V :=
λ a b, { e | sum.inl e ∈ H a b ∨ sum.inr e ∈ H b a }

end quiver

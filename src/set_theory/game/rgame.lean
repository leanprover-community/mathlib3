/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.game.pgame

/-!
# Pre-games up to relabelling

In `set_theory/pgame.lean`, we define combinatorial pre-games as arising from a left and right
family of pre-games. Despite being the most natural definition in type theory, this leads to a major
inconvenience, where operations on pre-games aren't as well-behaved as they are in ZFC. For
instance, pre-game addition isn't commutative, since the indexing types for the moves don't match.

Here, we define the quotient `rgame` of `pgame` by relabellings. Two games are relabellings of one
another if there exists a bijection between their left and right moves, and the same is true for
their left and right options. We prove that `rgame` is an `add_comm_monoid`.

## Todo

- Move the definition of `pgame.mul` here, prove basic results about `rgame.mul`.
- Define the relation of subsequency up to relabelling.
-/

open pgame function

universe u

/-- The setoid of pre-games quotiented by the existence of a relabelling. -/
def rgame.setoid : setoid pgame :=
⟨λ x y, nonempty (relabelling x y),
 λ x, ⟨relabelling.refl x⟩,
 λ x y ⟨h⟩, ⟨h.symm⟩,
 λ x y z ⟨h₁⟩ ⟨h₂⟩, ⟨h₁.trans h₂⟩⟩

/-- The quotient of pre-games quotiented by the existence of a relabelling. -/
def rgame := quotient rgame.setoid

namespace rgame

/-- Lift an relabelling-respecting function on `pgame` to `rgame`. -/
def lift {α} (f : pgame → α)
  (H : ∀ {x y}, relabelling x y → f x = f y) : rgame → α :=
quot.lift f (λ x y h, begin
  change nonempty (relabelling x y) at h,
  cases h,
  exact H h
end)

/-- Lift a binary relabelling-respecting function on `pgame` to `rgame`. -/
def lift₂ {α} (f : pgame → pgame → α)
  (H : ∀ {x₁ y₁ x₂ y₂}, relabelling x₁ x₂ → relabelling y₁ y₂ → f x₁ y₁ = f x₂ y₂) :
  rgame → rgame → α :=
@quotient.lift₂ _ _ _ rgame.setoid rgame.setoid f (λ x₁ y₁ x₂ y₂ ⟨hx⟩ ⟨hy⟩, H hx hy)

/-- Lift a pre-game to its quotient by relabelling. -/
def mk (x : pgame) : rgame := quotient.mk' x

theorem sound {x y : pgame} (e : relabelling x y) : mk x = mk y :=
quot.sound ⟨e⟩

@[elab_as_eliminator] theorem induction_on {p : rgame → Prop} (x : rgame) : (∀ a, p (mk a)) → p x :=
quotient.induction_on' x

instance : has_le rgame :=
⟨lift₂ (λ x y, x ≤ y) (λ x₁ y₁ x₂ y₂ hx hy, propext (le_congr hx.equiv hy.equiv))⟩

theorem le_rfl : ∀ {x : rgame}, x ≤ x :=
by { rintro ⟨x⟩, exact pgame.le_rfl }
theorem le_refl (x : rgame) : x ≤ x :=
le_rfl
theorem le_trans : ∀ x y z : rgame, x ≤ y → y ≤ z → x ≤ z :=
by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩, apply pgame.le_trans }

instance : is_preorder rgame (≤) :=
{ refl := le_refl,
  trans := @le_trans }

/-- This instance is incompatible with that provided by `game.partial_order`, which is why it's made
into a `def` instead. -/
instance : has_lt rgame :=
⟨lift₂ (λ x y, x < y) (λ x₁ y₁ x₂ y₂ hx hy, propext (lt_congr hx.equiv hy.equiv))⟩

@[simp] theorem not_le : ∀ {x y : rgame}, ¬ x ≤ y ↔ y < x :=
by { rintro ⟨x⟩ ⟨y⟩, exact not_le }

@[simp] theorem not_lt : ∀ {x y : rgame}, ¬ x < y ↔ y ≤ x :=
by { rintro ⟨x⟩ ⟨y⟩, exact not_lt }

instance : has_zero rgame := ⟨mk 0⟩
instance : inhabited rgame := ⟨0⟩
instance : has_one rgame := ⟨mk 1⟩

/-- The negation of `{L | R}` is `{-R | -L}`. -/
instance : has_neg rgame :=
⟨lift (λ x, mk (-x)) (λ x y h, sound (h.neg_congr))⟩

@[simp] lemma mk_neg (a : pgame) : mk (-a) = -mk a := rfl

@[simp] lemma neg_zero : -(0 : rgame) = 0 :=
show mk (-0) = mk 0, by rw pgame.neg_zero

instance : has_involutive_neg rgame.{u} :=
{ neg_neg := λ x, induction_on x $ λ a, by rw [←mk_neg, ←mk_neg, neg_neg],
  ..rgame.has_neg }

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
instance : has_add rgame :=
⟨lift₂ (λ x y, mk (x + y)) (λ x₁ y₁ x₂ y₂ hx hy, sound (relabelling.add_congr hx hy))⟩

@[simp] lemma mk_add (a b : pgame) : mk (a + b) = mk a + mk b := rfl

instance : has_sub rgame :=
⟨λ x y, x + -y⟩

@[simp] lemma mk_sub (a b : pgame) : mk (a - b) = mk a - mk b := rfl

@[simp] lemma sub_zero (x : rgame) : x - 0 = x + 0 :=
show x + -0 = x + 0, by rw neg_zero

instance : add_semigroup rgame :=
{ add_assoc := by { rintros ⟨x⟩ ⟨y⟩ ⟨z⟩, exact sound (add_assoc_relabelling x y z) },
  ..rgame.has_add }

instance : add_monoid rgame :=
{ add_zero := by { rintro ⟨x⟩, exact sound (add_zero_relabelling x) },
  zero_add := by { rintro ⟨x⟩, exact sound (zero_add_relabelling x) },
  ..rgame.has_zero,
  ..rgame.add_semigroup }

instance : add_comm_semigroup rgame :=
{ add_comm := by { rintros ⟨x⟩ ⟨y⟩, exact sound (add_comm_relabelling x y) },
  ..rgame.add_semigroup }

instance : add_comm_monoid rgame :=
{ ..rgame.add_monoid,
  ..rgame.add_comm_semigroup }

instance covariant_class_add_le : covariant_class rgame rgame (+) (≤) :=
⟨by { rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h, exact @add_le_add_left _ _ _ _ b c h a }⟩

instance covariant_class_swap_add_le : covariant_class rgame rgame (swap (+)) (≤) :=
⟨by { rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h, exact @add_le_add_right _ _ _ _ b c h a }⟩

instance covariant_class_add_lt : covariant_class rgame rgame (+) (<) :=
⟨by { rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h, exact @add_lt_add_left _ _ _ _ b c h a }⟩

instance covariant_class_swap_add_lt : covariant_class rgame rgame (swap (+)) (<) :=
⟨by { rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h, exact @add_lt_add_right _ _ _ _ b c h a }⟩

end rgame

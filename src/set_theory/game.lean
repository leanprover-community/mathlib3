/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison
-/
import set_theory.pgame

/-!
# Combinatorial games.

In this file we define the quotient of pre-games by the equivalence relation `p ≈ q ↔ p ≤ q ∧ q ≤
p`, and construct an instance `add_comm_group game`, as well as an instance `partial_order game`
(although note carefully the warning that the `<` field in this instance is not the usual relation
on combinatorial games).
-/

universes u

local infix ` ≈ ` := pgame.equiv

instance pgame.setoid : setoid pgame :=
⟨λ x y, x ≈ y,
 λ x, pgame.equiv_refl _,
 λ x y, pgame.equiv_symm,
 λ x y z, pgame.equiv_trans⟩

/-- The type of combinatorial games. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a combinatorial pre-game is built
  inductively from two families of combinatorial games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC.
  A combinatorial game is then constructed by quotienting by the equivalence
  `x ≈ y ↔ x ≤ y ∧ y ≤ x`. -/
def game := quotient pgame.setoid

open pgame

namespace game

/-- The relation `x ≤ y` on games. -/
def le : game → game → Prop :=
quotient.lift₂ (λ x y, x ≤ y) (λ x₁ y₁ x₂ y₂ hx hy, propext (le_congr hx hy))

instance : has_le game :=
{ le := le }

@[refl] theorem le_refl : ∀ x : game, x ≤ x :=
by { rintro ⟨x⟩, apply pgame.le_refl }
@[trans] theorem le_trans : ∀ x y z : game, x ≤ y → y ≤ z → x ≤ z :=
by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩, apply pgame.le_trans }
theorem le_antisymm : ∀ x y : game, x ≤ y → y ≤ x → x = y :=
by { rintro ⟨x⟩ ⟨y⟩ h₁ h₂, apply quot.sound, exact ⟨h₁, h₂⟩ }

/-- The relation `x < y` on games. -/
-- We don't yet make this into an instance, because it will conflict with the (incorrect) notion
-- of `<` provided by `partial_order` later.
def lt : game → game → Prop :=
quotient.lift₂ (λ x y, x < y) (λ x₁ y₁ x₂ y₂ hx hy, propext (lt_congr hx hy))

theorem not_le : ∀ {x y : game}, ¬ (x ≤ y) ↔ (lt y x) :=
by { rintro ⟨x⟩ ⟨y⟩, exact not_le }

instance : has_zero game := ⟨⟦0⟧⟩
instance : has_one game := ⟨⟦1⟧⟩

/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : game → game :=
quot.lift (λ x, ⟦-x⟧) (λ x y h, quot.sound (@neg_congr x y h))

instance : has_neg game :=
{ neg := neg }

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
def add : game → game → game :=
quotient.lift₂ (λ x y : pgame, ⟦x + y⟧) (λ x₁ y₁ x₂ y₂ hx hy, quot.sound (pgame.add_congr hx hy))

instance : has_add game := ⟨add⟩

theorem add_assoc : ∀ (x y z : game), (x + y) + z = x + (y + z) :=
begin
  rintros ⟨x⟩ ⟨y⟩ ⟨z⟩,
  apply quot.sound,
  exact add_assoc_equiv
end

instance : add_semigroup game.{u} :=
{ add_assoc := add_assoc,
  ..game.has_add }

theorem add_zero : ∀ (x : game), x + 0 = x :=
begin
  rintro ⟨x⟩,
  apply quot.sound,
  apply add_zero_equiv
end
theorem zero_add : ∀ (x : game), 0 + x = x :=
begin
  rintro ⟨x⟩,
  apply quot.sound,
  apply zero_add_equiv
end

instance : add_monoid game :=
{ add_zero := add_zero,
  zero_add := zero_add,
  ..game.has_zero,
  ..game.add_semigroup }

theorem add_left_neg : ∀ (x : game), (-x) + x = 0 :=
begin
  rintro ⟨x⟩,
  apply quot.sound,
  apply add_left_neg_equiv
end

instance : add_group game :=
{ add_left_neg := add_left_neg,
  ..game.has_neg,
  ..game.add_monoid }

theorem add_comm : ∀ (x y : game), x + y = y + x :=
begin
  rintros ⟨x⟩ ⟨y⟩,
  apply quot.sound,
  exact add_comm_equiv
end

instance : add_comm_semigroup game :=
{ add_comm := add_comm,
  ..game.add_semigroup }

instance : add_comm_group game :=
{ ..game.add_comm_semigroup,
  ..game.add_group }

theorem add_le_add_left : ∀ (a b : game), a ≤ b → ∀ (c : game), c + a ≤ c + b :=
begin rintro ⟨a⟩ ⟨b⟩ h ⟨c⟩, apply pgame.add_le_add_left h, end

-- While it is very tempting to define a `partial_order` on games, and prove
-- that games form an `ordered_comm_group`, it is a bit dangerous.

-- The relations `≤` and `<` on games do not satisfy
-- `lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a)`
-- (Consider `a = 0`, `b = star`.)
-- (`lt_iff_le_not_le` is satisfied by surreal numbers, however.)
-- Thus we can not use `<` when defining a `partial_order`.

-- Because of this issue, we define the `partial_order` and `ordered_comm_group` instances,
-- but do not actually mark them as instances, for safety.

/-- The `<` operation provided by this partial order is not the usual `<` on games! -/
def game_partial_order : partial_order game :=
{ le_refl := le_refl,
  le_trans := le_trans,
  le_antisymm := le_antisymm,
  ..game.has_le }

local attribute [instance] game_partial_order

/-- The `<` operation provided by this `ordered_comm_group` is not the usual `<` on games! -/
def ordered_comm_group_game : ordered_comm_group game :=
ordered_comm_group.mk' add_le_add_left

end game

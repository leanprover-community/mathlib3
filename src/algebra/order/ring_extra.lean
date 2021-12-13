/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import algebra.invertible
import algebra.order.group_extra
-- import algebra.order.sub
-- import data.set.intervals.basic

universe u
variable {α : Type u}

@[protect_proj]
class ordered_semiring (α : Type u) extends semiring α, partial_order α,
  covariant_class α α (+) (≤) :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b :=
  λ a b h c, covariant_class.elim c h)
(mul_lt_mul_of_pos_left :  ∀ a b c : α, a < b → 0 < c → c * a < c * b)
(mul_lt_mul_of_pos_right : ∀ a b c : α, a < b → 0 < c → a * c < b * c)

instance ordered_semiring.to_ordered_add_comm_monoid [h : ordered_semiring α] :
  ordered_add_comm_monoid α :=
{ ..h }

@[protect_proj]
class ordered_comm_semiring (α : Type u) extends ordered_semiring α :=
(mul_comm : ∀ a b : α, a * b = b * a)

instance ordered_comm_semiring.to_comm_semiring [h : ordered_comm_semiring α] : comm_semiring α :=
{ ..h }

@[protect_proj]
class ordered_ring (α : Type u) extends ring α, partial_order α,
  covariant_class α α (+) (≤) :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b :=
  λ a b h c, covariant_class.elim c h)
(mul_pos     : ∀ a b : α, 0 < a → 0 < b → 0 < a * b)

section ordered_ring
variables [ordered_ring α] {a b c : α}

-- See Note [decidable namespace]
protected lemma decidable.ordered_ring.mul_nonneg [@decidable_rel α (≤)]
  {a b : α} (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) : 0 ≤ a * b :=
begin
  by_cases ha : a ≤ 0, { simp [le_antisymm ha h₁] },
  by_cases hb : b ≤ 0, { simp [le_antisymm hb h₂] },
  exact (le_not_le_of_lt (ordered_ring.mul_pos a b (h₁.lt_of_not_le ha) (h₂.lt_of_not_le hb))).1,
end

lemma ordered_ring.mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b :=
by classical; exact decidable.ordered_ring.mul_nonneg

-- See Note [decidable namespace]
protected lemma decidable.ordered_ring.mul_le_mul_of_nonneg_left
  [@decidable_rel α (≤)] (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b :=
begin
  rw [← sub_nonneg, ← mul_sub],
  exact decidable.ordered_ring.mul_nonneg h₂ (sub_nonneg.2 h₁),
end

lemma ordered_ring.mul_le_mul_of_nonneg_left : a ≤ b → 0 ≤ c → c * a ≤ c * b :=
by classical; exact decidable.ordered_ring.mul_le_mul_of_nonneg_left

-- See Note [decidable namespace]
protected lemma decidable.ordered_ring.mul_le_mul_of_nonneg_right
  [@decidable_rel α (≤)] (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c :=
begin
  rw [← sub_nonneg, ← sub_mul],
  exact decidable.ordered_ring.mul_nonneg (sub_nonneg.2 h₁) h₂,
end

lemma ordered_ring.mul_le_mul_of_nonneg_right : a ≤ b → 0 ≤ c → a * c ≤ b * c :=
by classical; exact decidable.ordered_ring.mul_le_mul_of_nonneg_right

lemma ordered_ring.mul_lt_mul_of_pos_left (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b :=
begin
  rw [← sub_pos, ← mul_sub],
  exact ordered_ring.mul_pos _ _ h₂ (sub_pos.2 h₁),
end

lemma ordered_ring.mul_lt_mul_of_pos_right (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c :=
begin
  rw [← sub_pos, ← sub_mul],
  exact ordered_ring.mul_pos _ _ (sub_pos.2 h₁) h₂,
end
instance ordered_ring.to_ordered_semiring [h : ordered_ring α] : ordered_semiring α :=
{ mul_lt_mul_of_pos_left  := λ a b c hab cpos, _,
  mul_lt_mul_of_pos_right := _,
  ..h }

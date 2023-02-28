/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.hom.group
import algebra.order.monoid.order_dual
import algebra.order.monoid.with_zero.basic
import data.nat.cast.defs

/-! # Adjoining top/bottom elements to ordered monoids.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/

universes u v
variables {α : Type u} {β : Type v}

open function

namespace with_top

section has_one

variables [has_one α]

@[to_additive] instance : has_one (with_top α) := ⟨(1 : α)⟩

@[simp, norm_cast, to_additive] lemma coe_one : ((1 : α) : with_top α) = 1 := rfl

@[simp, norm_cast, to_additive] lemma coe_eq_one {a : α} : (a : with_top α) = 1 ↔ a = 1 :=
coe_eq_coe

@[simp, norm_cast, to_additive coe_nonneg]
lemma one_le_coe [has_le α] {a : α} : 1 ≤ (a : with_top α) ↔ 1 ≤ a := coe_le_coe

@[simp, norm_cast, to_additive coe_le_zero]
lemma coe_le_one [has_le α] {a : α} : (a : with_top α) ≤ 1 ↔ a ≤ 1 := coe_le_coe

@[simp, norm_cast, to_additive coe_pos]
lemma one_lt_coe [has_lt α] {a : α} : 1 < (a : with_top α) ↔ 1 < a := coe_lt_coe

@[simp, norm_cast, to_additive coe_lt_zero]
lemma coe_lt_one [has_lt α] {a : α} : (a : with_top α) < 1 ↔ a < 1 := coe_lt_coe

@[simp, to_additive] protected lemma map_one {β} (f : α → β) :
  (1 : with_top α).map f = (f 1 : with_top β) := rfl

@[simp, norm_cast, to_additive] theorem one_eq_coe {a : α} : 1 = (a : with_top α) ↔ a = 1 :=
trans eq_comm coe_eq_one

@[simp, to_additive] theorem top_ne_one : ⊤ ≠ (1 : with_top α) .
@[simp, to_additive] theorem one_ne_top : (1 : with_top α) ≠ ⊤ .

instance [has_zero α] [has_le α] [zero_le_one_class α] : zero_le_one_class (with_top α) :=
⟨some_le_some.2 zero_le_one⟩

end has_one

section has_add
variables [has_add α] {a b c d : with_top α} {x y : α}

instance : has_add (with_top α) := ⟨option.map₂ (+)⟩

@[norm_cast] lemma coe_add : ((x + y : α) : with_top α) = x + y := rfl
@[norm_cast] lemma coe_bit0 : ((bit0 x : α) : with_top α) = bit0 x := rfl
@[norm_cast] lemma coe_bit1 [has_one α] {a : α} : ((bit1 a : α) : with_top α) = bit1 a := rfl

@[simp] lemma top_add (a : with_top α) : ⊤ + a = ⊤ := rfl
@[simp] lemma add_top (a : with_top α) : a + ⊤ = ⊤ := by cases a; refl

@[simp] lemma add_eq_top : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
by cases a; cases b; simp [none_eq_top, some_eq_coe, ←with_top.coe_add]

lemma add_ne_top : a + b ≠ ⊤ ↔ a ≠ ⊤ ∧ b ≠ ⊤ := add_eq_top.not.trans not_or_distrib

lemma add_lt_top [has_lt α] {a b : with_top α} : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ :=
by simp_rw [with_top.lt_top_iff_ne_top, add_ne_top]

lemma add_eq_coe : ∀ {a b : with_top α} {c : α},
  a + b = c ↔ ∃ (a' b' : α), ↑a' = a ∧ ↑b' = b ∧ a' + b' = c
| none b c := by simp [none_eq_top]
| (some a) none c := by simp [none_eq_top]
| (some a) (some b) c :=
    by simp only [some_eq_coe, ← coe_add, coe_eq_coe, exists_and_distrib_left, exists_eq_left]

@[simp] lemma add_coe_eq_top_iff {x : with_top α} {y : α} : x + y = ⊤ ↔ x = ⊤ :=
by { induction x using with_top.rec_top_coe; simp [← coe_add] }

@[simp] lemma coe_add_eq_top_iff {y : with_top α} : ↑x + y = ⊤ ↔ y = ⊤ :=
by { induction y using with_top.rec_top_coe; simp [← coe_add] }

instance covariant_class_add_le [has_le α] [covariant_class α α (+) (≤)] :
  covariant_class (with_top α) (with_top α) (+) (≤) :=
⟨λ a b c h, begin
  cases a; cases c; try { exact le_top },
  rcases le_coe_iff.1 h with ⟨b, rfl, h'⟩,
  exact coe_le_coe.2 (add_le_add_left (coe_le_coe.1 h) _)
end⟩

instance covariant_class_swap_add_le [has_le α] [covariant_class α α (swap (+)) (≤)] :
  covariant_class (with_top α) (with_top α) (swap (+)) (≤) :=
⟨λ a b c h, begin
  cases a; cases c; try { exact le_top },
  rcases le_coe_iff.1 h with ⟨b, rfl, h'⟩,
  exact coe_le_coe.2 (add_le_add_right (coe_le_coe.1 h) _)
end⟩

instance contravariant_class_add_lt [has_lt α] [contravariant_class α α (+) (<)] :
  contravariant_class (with_top α) (with_top α) (+) (<) :=
⟨λ a b c h, begin
  induction a using with_top.rec_top_coe, { exact (not_none_lt _ h).elim },
  induction b using with_top.rec_top_coe, { exact (not_none_lt _ h).elim },
  induction c using with_top.rec_top_coe,
  { exact coe_lt_top _ },
  { exact coe_lt_coe.2 (lt_of_add_lt_add_left $ coe_lt_coe.1 h) }
end⟩

instance contravariant_class_swap_add_lt [has_lt α] [contravariant_class α α (swap (+)) (<)] :
  contravariant_class (with_top α) (with_top α) (swap (+)) (<) :=
⟨λ a b c h, begin
  cases a; cases b; try { exact (not_none_lt _ h).elim },
  cases c,
  { exact coe_lt_top _ },
  { exact coe_lt_coe.2 (lt_of_add_lt_add_right $ coe_lt_coe.1 h) }
end⟩

protected lemma le_of_add_le_add_left [has_le α] [contravariant_class α α (+) (≤)] (ha : a ≠ ⊤)
  (h : a + b ≤ a + c) : b ≤ c :=
begin
  lift a to α using ha,
  induction c using with_top.rec_top_coe, { exact le_top },
  induction b using with_top.rec_top_coe, { exact (not_top_le_coe _ h).elim },
  simp only [← coe_add, coe_le_coe] at h ⊢,
  exact le_of_add_le_add_left h
end

protected lemma le_of_add_le_add_right [has_le α] [contravariant_class α α (swap (+)) (≤)]
  (ha : a ≠ ⊤) (h : b + a ≤ c + a) : b ≤ c :=
begin
  lift a to α using ha,
  cases c,
  { exact le_top },
  cases b,
  { exact (not_top_le_coe _ h).elim },
  { exact coe_le_coe.2 (le_of_add_le_add_right $ coe_le_coe.1 h) }
end

protected lemma add_lt_add_left [has_lt α] [covariant_class α α (+) (<)] (ha : a ≠ ⊤) (h : b < c) :
  a + b < a + c :=
begin
  lift a to α using ha,
  rcases lt_iff_exists_coe.1 h with ⟨b, rfl, h'⟩,
  cases c,
  { exact coe_lt_top _ },
  { exact coe_lt_coe.2 (add_lt_add_left (coe_lt_coe.1 h) _) }
end

protected lemma add_lt_add_right [has_lt α] [covariant_class α α (swap (+)) (<)]
  (ha : a ≠ ⊤) (h : b < c) :
  b + a < c + a :=
begin
  lift a to α using ha,
  rcases lt_iff_exists_coe.1 h with ⟨b, rfl, h'⟩,
  cases c,
  { exact coe_lt_top _ },
  { exact coe_lt_coe.2 (add_lt_add_right (coe_lt_coe.1 h) _) }
end

protected lemma add_le_add_iff_left [has_le α] [covariant_class α α (+) (≤)]
  [contravariant_class α α (+) (≤)]
  (ha : a ≠ ⊤) : a + b ≤ a + c ↔ b ≤ c :=
⟨with_top.le_of_add_le_add_left ha, λ h, add_le_add_left h a⟩

protected lemma add_le_add_iff_right [has_le α] [covariant_class α α (swap (+)) (≤)]
  [contravariant_class α α (swap (+)) (≤)] (ha : a ≠ ⊤) : b + a ≤ c + a ↔ b ≤ c :=
⟨with_top.le_of_add_le_add_right ha, λ h, add_le_add_right h a⟩

protected lemma add_lt_add_iff_left [has_lt α] [covariant_class α α (+) (<)]
  [contravariant_class α α (+) (<)] (ha : a ≠ ⊤) : a + b < a + c ↔ b < c :=
⟨lt_of_add_lt_add_left, with_top.add_lt_add_left ha⟩

protected lemma add_lt_add_iff_right [has_lt α] [covariant_class α α (swap (+)) (<)]
  [contravariant_class α α (swap (+)) (<)] (ha : a ≠ ⊤) : b + a < c + a ↔ b < c :=
⟨lt_of_add_lt_add_right, with_top.add_lt_add_right ha⟩

protected lemma add_lt_add_of_le_of_lt [preorder α] [covariant_class α α (+) (<)]
  [covariant_class α α (swap (+)) (≤)] (ha : a ≠ ⊤) (hab : a ≤ b) (hcd : c < d) : a + c < b + d :=
(with_top.add_lt_add_left ha hcd).trans_le $ add_le_add_right hab _

protected lemma add_lt_add_of_lt_of_le [preorder α] [covariant_class α α (+) (≤)]
  [covariant_class α α (swap (+)) (<)] (hc : c ≠ ⊤) (hab : a < b) (hcd : c ≤ d) : a + c < b + d :=
(with_top.add_lt_add_right hc hab).trans_le $ add_le_add_left hcd _

/-  There is no `with_top.map_mul_of_mul_hom`, since `with_top` does not have a multiplication. -/
@[simp] protected lemma map_add {F} [has_add β] [add_hom_class F α β] (f : F) (a b : with_top α) :
  (a + b).map f = a.map f + b.map f :=
begin
  induction a using with_top.rec_top_coe,
  { exact (top_add _).symm },
  { induction b using with_top.rec_top_coe,
    { exact (add_top _).symm },
    { rw [map_coe, map_coe, ← coe_add, ← coe_add, ← map_add],
      refl } },
end

end has_add

instance [add_semigroup α] : add_semigroup (with_top α) :=
{ add_assoc := λ _ _ _, option.map₂_assoc add_assoc,
  ..with_top.has_add }

instance [add_comm_semigroup α] : add_comm_semigroup (with_top α) :=
{ add_comm := λ _ _, option.map₂_comm add_comm,
  ..with_top.add_semigroup }

instance [add_zero_class α] : add_zero_class (with_top α) :=
{ zero_add := option.map₂_left_identity zero_add,
  add_zero := option.map₂_right_identity add_zero,
  ..with_top.has_zero,
  ..with_top.has_add }

instance [add_monoid α] : add_monoid (with_top α) :=
{ ..with_top.add_zero_class,
  ..with_top.has_zero,
  ..with_top.add_semigroup }

instance [add_comm_monoid α] : add_comm_monoid (with_top α) :=
{ ..with_top.add_monoid, ..with_top.add_comm_semigroup }

instance [add_monoid_with_one α] : add_monoid_with_one (with_top α) :=
{ nat_cast := λ n, ↑(n : α),
  nat_cast_zero := by rw [nat.cast_zero, with_top.coe_zero],
  nat_cast_succ := λ n, by rw [nat.cast_add_one, with_top.coe_add, with_top.coe_one],
  .. with_top.has_one, .. with_top.add_monoid }

instance [add_comm_monoid_with_one α] : add_comm_monoid_with_one (with_top α) :=
{ .. with_top.add_monoid_with_one, .. with_top.add_comm_monoid }

instance [ordered_add_comm_monoid α] : ordered_add_comm_monoid (with_top α) :=
{ add_le_add_left :=
    begin
      rintros a b h (_|c), { simp [none_eq_top] },
      rcases b with (_|b), { simp [none_eq_top] },
      rcases le_coe_iff.1 h with ⟨a, rfl, h⟩,
      simp only [some_eq_coe, ← coe_add, coe_le_coe] at h ⊢,
      exact add_le_add_left h c
    end,
  ..with_top.partial_order, ..with_top.add_comm_monoid }

instance [linear_ordered_add_comm_monoid α] :
  linear_ordered_add_comm_monoid_with_top (with_top α) :=
{ top_add' := with_top.top_add,
  ..with_top.order_top,
  ..with_top.linear_order,
  ..with_top.ordered_add_comm_monoid,
  ..option.nontrivial }

instance [has_le α] [has_add α] [has_exists_add_of_le α] : has_exists_add_of_le (with_top α) :=
⟨λ a b, match a, b with
  | ⊤, ⊤ := by simp
  | (a : α), ⊤ := λ _, ⟨⊤, rfl⟩
  | (a : α), (b : α) := λ h, begin
      obtain ⟨c, rfl⟩ := exists_add_of_le (with_top.coe_le_coe.1 h),
      exact ⟨c, rfl⟩
    end
  | ⊤, (b : α) := λ h, (not_top_le_coe _ h).elim
end⟩

instance [canonically_ordered_add_monoid α] : canonically_ordered_add_monoid (with_top α) :=
{ le_self_add := λ a b, match a, b with
  | ⊤, ⊤ := le_rfl
  | (a : α), ⊤ := le_top
  | (a : α), (b : α) := with_top.coe_le_coe.2 le_self_add
  | ⊤, (b : α) := le_rfl
  end,
  ..with_top.order_bot, ..with_top.ordered_add_comm_monoid, ..with_top.has_exists_add_of_le }

instance [canonically_linear_ordered_add_monoid α] :
  canonically_linear_ordered_add_monoid (with_top α) :=
{ ..with_top.canonically_ordered_add_monoid, ..with_top.linear_order }

@[simp, norm_cast] lemma coe_nat [add_monoid_with_one α] (n : ℕ) : ((n : α) : with_top α) = n := rfl
@[simp] lemma nat_ne_top [add_monoid_with_one α] (n : ℕ) : (n : with_top α) ≠ ⊤ := coe_ne_top
@[simp] lemma top_ne_nat [add_monoid_with_one α] (n : ℕ) : (⊤ : with_top α) ≠ n := top_ne_coe

/-- Coercion from `α` to `with_top α` as an `add_monoid_hom`. -/
def coe_add_hom [add_monoid α] : α →+ with_top α :=
⟨coe, rfl, λ _ _, rfl⟩

@[simp] lemma coe_coe_add_hom [add_monoid α] : ⇑(coe_add_hom : α →+ with_top α) = coe := rfl

@[simp] lemma zero_lt_top [ordered_add_comm_monoid α] : (0 : with_top α) < ⊤ :=
coe_lt_top 0

@[simp, norm_cast] lemma zero_lt_coe [ordered_add_comm_monoid α] (a : α) :
  (0 : with_top α) < a ↔ 0 < a :=
coe_lt_coe

/-- A version of `with_top.map` for `one_hom`s. -/
@[to_additive "A version of `with_top.map` for `zero_hom`s", simps { fully_applied := ff }]
protected def _root_.one_hom.with_top_map {M N : Type*} [has_one M] [has_one N] (f : one_hom M N) :
  one_hom (with_top M) (with_top N) :=
{ to_fun := with_top.map f,
  map_one' := by rw [with_top.map_one, map_one, coe_one] }

/-- A version of `with_top.map` for `add_hom`s. -/
@[simps { fully_applied := ff }] protected def _root_.add_hom.with_top_map
  {M N : Type*} [has_add M] [has_add N] (f : add_hom M N) :
  add_hom (with_top M) (with_top N) :=
{ to_fun := with_top.map f,
  map_add' := with_top.map_add f }

/-- A version of `with_top.map` for `add_monoid_hom`s. -/
@[simps { fully_applied := ff }] protected def _root_.add_monoid_hom.with_top_map
  {M N : Type*} [add_zero_class M] [add_zero_class N] (f : M →+ N) :
  with_top M →+ with_top N :=
{ to_fun := with_top.map f,
  .. f.to_zero_hom.with_top_map, .. f.to_add_hom.with_top_map }

end with_top

namespace with_bot

@[to_additive] instance [has_one α] : has_one (with_bot α) := with_top.has_one
instance [has_add α] : has_add (with_bot α) := with_top.has_add
instance [add_semigroup α] : add_semigroup (with_bot α) := with_top.add_semigroup
instance [add_comm_semigroup α] : add_comm_semigroup (with_bot α) := with_top.add_comm_semigroup
instance [add_zero_class α] : add_zero_class (with_bot α) := with_top.add_zero_class
instance [add_monoid α] : add_monoid (with_bot α) := with_top.add_monoid
instance [add_comm_monoid α] : add_comm_monoid (with_bot α) := with_top.add_comm_monoid
instance [add_monoid_with_one α] : add_monoid_with_one (with_bot α) := with_top.add_monoid_with_one

instance [add_comm_monoid_with_one α] : add_comm_monoid_with_one (with_bot α) :=
with_top.add_comm_monoid_with_one

instance [has_zero α] [has_one α] [has_le α] [zero_le_one_class α] :
  zero_le_one_class (with_bot α) :=
⟨some_le_some.2 zero_le_one⟩

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
@[to_additive]
lemma coe_one [has_one α] : ((1 : α) : with_bot α) = 1 := rfl

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
@[to_additive]
lemma coe_eq_one [has_one α] {a : α} : (a : with_bot α) = 1 ↔ a = 1 :=
with_top.coe_eq_one

@[simp, norm_cast, to_additive coe_nonneg]
lemma one_le_coe [has_one α] [has_le α] {a : α} : 1 ≤ (a : with_bot α) ↔ 1 ≤ a := coe_le_coe

@[simp, norm_cast, to_additive coe_le_zero]
lemma coe_le_one [has_one α] [has_le α] {a : α} : (a : with_bot α) ≤ 1 ↔ a ≤ 1 := coe_le_coe

@[simp, norm_cast, to_additive coe_pos]
lemma one_lt_coe [has_one α] [has_lt α] {a : α} : 1 < (a : with_bot α) ↔ 1 < a := coe_lt_coe

@[simp, norm_cast, to_additive coe_lt_zero]
lemma coe_lt_one [has_one α] [has_lt α] {a : α} : (a : with_bot α) < 1 ↔ a < 1 := coe_lt_coe

@[simp, to_additive] protected lemma map_one {β} [has_one α] (f : α → β) :
  (1 : with_bot α).map f = (f 1 : with_bot β) := rfl

@[norm_cast] lemma coe_nat [add_monoid_with_one α] (n : ℕ) : ((n : α) : with_bot α) = n := rfl
@[simp] lemma nat_ne_bot [add_monoid_with_one α] (n : ℕ) : (n : with_bot α) ≠ ⊥ := coe_ne_bot
@[simp] lemma bot_ne_nat [add_monoid_with_one α] (n : ℕ) : (⊥ : with_bot α) ≠ n := bot_ne_coe

section has_add
variables [has_add α] {a b c d : with_bot α} {x y : α}

-- `norm_cast` proves those lemmas, because `with_top`/`with_bot` are reducible
lemma coe_add (a b : α) : ((a + b : α) : with_bot α) = a + b := rfl
lemma coe_bit0 : ((bit0 x : α) : with_bot α) = bit0 x := rfl
lemma coe_bit1 [has_one α] {a : α} : ((bit1 a : α) : with_bot α) = bit1 a := rfl

@[simp] lemma bot_add (a : with_bot α) : ⊥ + a = ⊥ := rfl
@[simp] lemma add_bot (a : with_bot α) : a + ⊥ = ⊥ := by cases a; refl

@[simp] lemma add_eq_bot : a + b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := with_top.add_eq_top
lemma add_ne_bot : a + b ≠ ⊥ ↔ a ≠ ⊥ ∧ b ≠ ⊥ := with_top.add_ne_top

lemma bot_lt_add [has_lt α] {a b : with_bot α} : ⊥ < a + b ↔ ⊥ < a ∧ ⊥ < b :=
@with_top.add_lt_top αᵒᵈ _ _ _ _

lemma add_eq_coe : a + b = x ↔ ∃ (a' b' : α), ↑a' = a ∧ ↑b' = b ∧ a' + b' = x := with_top.add_eq_coe

@[simp] lemma add_coe_eq_bot_iff : a + y = ⊥ ↔ a = ⊥ := with_top.add_coe_eq_top_iff
@[simp] lemma coe_add_eq_bot_iff : ↑x + b = ⊥ ↔ b = ⊥ := with_top.coe_add_eq_top_iff

/-  There is no `with_bot.map_mul_of_mul_hom`, since `with_bot` does not have a multiplication. -/
@[simp] protected lemma map_add {F} [has_add β] [add_hom_class F α β] (f : F) (a b : with_bot α) :
  (a + b).map f = a.map f + b.map f :=
with_top.map_add f a b

/-- A version of `with_bot.map` for `one_hom`s. -/
@[to_additive "A version of `with_bot.map` for `zero_hom`s", simps { fully_applied := ff }]
protected def _root_.one_hom.with_bot_map {M N : Type*} [has_one M] [has_one N] (f : one_hom M N) :
  one_hom (with_bot M) (with_bot N) :=
{ to_fun := with_bot.map f,
  map_one' := by rw [with_bot.map_one, map_one, coe_one] }

/-- A version of `with_bot.map` for `add_hom`s. -/
@[simps { fully_applied := ff }] protected def _root_.add_hom.with_bot_map
  {M N : Type*} [has_add M] [has_add N] (f : add_hom M N) :
  add_hom (with_bot M) (with_bot N) :=
{ to_fun := with_bot.map f,
  map_add' := with_bot.map_add f }

/-- A version of `with_bot.map` for `add_monoid_hom`s. -/
@[simps { fully_applied := ff }] protected def _root_.add_monoid_hom.with_bot_map
  {M N : Type*} [add_zero_class M] [add_zero_class N] (f : M →+ N) :
  with_bot M →+ with_bot N :=
{ to_fun := with_bot.map f,
  .. f.to_zero_hom.with_bot_map, .. f.to_add_hom.with_bot_map }

variables [preorder α]

instance covariant_class_add_le [covariant_class α α (+) (≤)] :
  covariant_class (with_bot α) (with_bot α) (+) (≤) :=
@order_dual.covariant_class_add_le (with_top αᵒᵈ) _ _ _

instance covariant_class_swap_add_le [covariant_class α α (swap (+)) (≤)] :
  covariant_class (with_bot α) (with_bot α) (swap (+)) (≤) :=
@order_dual.covariant_class_swap_add_le (with_top αᵒᵈ) _ _ _

instance contravariant_class_add_lt [contravariant_class α α (+) (<)] :
  contravariant_class (with_bot α) (with_bot α) (+) (<) :=
@order_dual.contravariant_class_add_lt (with_top αᵒᵈ) _ _ _

instance contravariant_class_swap_add_lt [contravariant_class α α (swap (+)) (<)] :
  contravariant_class (with_bot α) (with_bot α) (swap (+)) (<) :=
@order_dual.contravariant_class_swap_add_lt (with_top αᵒᵈ) _ _ _

protected lemma le_of_add_le_add_left [contravariant_class α α (+) (≤)] (ha : a ≠ ⊥)
  (h : a + b ≤ a + c) : b ≤ c :=
@with_top.le_of_add_le_add_left αᵒᵈ _ _ _ _ _ _ ha h

protected lemma le_of_add_le_add_right [contravariant_class α α (swap (+)) (≤)] (ha : a ≠ ⊥)
  (h : b + a ≤ c + a) : b ≤ c :=
@with_top.le_of_add_le_add_right αᵒᵈ _ _ _ _ _ _ ha h

protected lemma add_lt_add_left [covariant_class α α (+) (<)] (ha : a ≠ ⊥) (h : b < c) :
  a + b < a + c :=
@with_top.add_lt_add_left αᵒᵈ _ _ _ _ _ _ ha h

protected lemma add_lt_add_right [covariant_class α α (swap (+)) (<)] (ha : a ≠ ⊥) (h : b < c) :
  b + a < c + a :=
@with_top.add_lt_add_right αᵒᵈ _ _ _ _ _ _ ha h

protected lemma add_le_add_iff_left [covariant_class α α (+) (≤)] [contravariant_class α α (+) (≤)]
  (ha : a ≠ ⊥) : a + b ≤ a + c ↔ b ≤ c :=
⟨with_bot.le_of_add_le_add_left ha, λ h, add_le_add_left h a⟩

protected lemma add_le_add_iff_right [covariant_class α α (swap (+)) (≤)]
  [contravariant_class α α (swap (+)) (≤)] (ha : a ≠ ⊥) : b + a ≤ c + a ↔ b ≤ c :=
⟨with_bot.le_of_add_le_add_right ha, λ h, add_le_add_right h a⟩

protected lemma add_lt_add_iff_left [covariant_class α α (+) (<)] [contravariant_class α α (+) (<)]
  (ha : a ≠ ⊥) : a + b < a + c ↔ b < c :=
⟨lt_of_add_lt_add_left, with_bot.add_lt_add_left ha⟩

protected lemma add_lt_add_iff_right [covariant_class α α (swap (+)) (<)]
  [contravariant_class α α (swap (+)) (<)] (ha : a ≠ ⊥) : b + a < c + a ↔ b < c :=
⟨lt_of_add_lt_add_right, with_bot.add_lt_add_right ha⟩

protected lemma add_lt_add_of_le_of_lt [covariant_class α α (+) (<)]
  [covariant_class α α (swap (+)) (≤)] (hb : b ≠ ⊥) (hab : a ≤ b) (hcd : c < d) : a + c < b + d :=
@with_top.add_lt_add_of_le_of_lt αᵒᵈ _ _ _ _ _ _ _ _ hb hab hcd

protected lemma add_lt_add_of_lt_of_le [covariant_class α α (+) (≤)]
  [covariant_class α α (swap (+)) (<)] (hd : d ≠ ⊥) (hab : a < b) (hcd : c ≤ d) : a + c < b + d :=
@with_top.add_lt_add_of_lt_of_le αᵒᵈ _ _ _ _ _ _ _ _ hd hab hcd

end has_add

instance [ordered_add_comm_monoid α] : ordered_add_comm_monoid (with_bot α) :=
{ add_le_add_left := λ a b h c, add_le_add_left h c,
  ..with_bot.partial_order,
  ..with_bot.add_comm_monoid }

instance [linear_ordered_add_comm_monoid α] : linear_ordered_add_comm_monoid (with_bot α) :=
{ ..with_bot.linear_order, ..with_bot.ordered_add_comm_monoid }

end with_bot

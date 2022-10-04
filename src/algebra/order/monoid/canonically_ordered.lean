/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/

import algebra.order.monoid.with_zero

/-!
# Canonically ordered monoids
-/

universes u
variables {α : Type u}

set_option old_structure_cmd true

/-- A canonically ordered additive monoid is an ordered commutative additive monoid
  in which the ordering coincides with the subtractibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a + c`.
  This is satisfied by the natural numbers, for example, but not
  the integers or other nontrivial `ordered_add_comm_group`s. -/
@[protect_proj, ancestor ordered_add_comm_monoid has_bot]
class canonically_ordered_add_monoid (α : Type*) extends ordered_add_comm_monoid α, has_bot α :=
(bot_le : ∀ x : α, ⊥ ≤ x)
(exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c, b = a + c)
(le_self_add : ∀ a b : α, a ≤ a + b)

@[priority 100]  -- see Note [lower instance priority]
instance canonically_ordered_add_monoid.to_order_bot (α : Type u)
  [h : canonically_ordered_add_monoid α] : order_bot α :=
{ ..h }

/-- A canonically ordered monoid is an ordered commutative monoid
  in which the ordering coincides with the divisibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a * c`.
  Examples seem rare; it seems more likely that the `order_dual`
  of a naturally-occurring lattice satisfies this than the lattice
  itself (for example, dual of the lattice of ideals of a PID or
  Dedekind domain satisfy this; collections of all things ≤ 1 seem to
  be more natural that collections of all things ≥ 1).
-/
@[protect_proj, ancestor ordered_comm_monoid has_bot, to_additive]
class canonically_ordered_monoid (α : Type*) extends ordered_comm_monoid α, has_bot α :=
(bot_le : ∀ x : α, ⊥ ≤ x)
(exists_mul_of_le : ∀ {a b : α}, a ≤ b → ∃ c, b = a * c)
(le_self_mul : ∀ a b : α, a ≤ a * b)

@[priority 100, to_additive]  -- see Note [lower instance priority]
instance canonically_ordered_monoid.to_order_bot (α : Type u)
  [h : canonically_ordered_monoid α] : order_bot α :=
{ ..h }

@[priority 100, to_additive]  -- see Note [lower instance priority]
instance canonically_ordered_monoid.has_exists_mul_of_le (α : Type u)
  [h : canonically_ordered_monoid α] : has_exists_mul_of_le α :=
{ ..h }

section canonically_ordered_monoid

variables [canonically_ordered_monoid α] {a b c d : α}

@[to_additive] lemma le_self_mul : a ≤ a * c := canonically_ordered_monoid.le_self_mul _ _
@[to_additive] lemma le_mul_self : a ≤ b * a := by { rw mul_comm, exact le_self_mul }

@[to_additive] lemma self_le_mul_right (a b : α) : a ≤ a * b := le_self_mul
@[to_additive] lemma self_le_mul_left (a b : α) : a ≤ b * a := le_mul_self

@[to_additive] lemma le_of_mul_le_left : a * b ≤ c → a ≤ c := le_self_mul.trans
@[to_additive] lemma le_of_mul_le_right : a * b ≤ c → b ≤ c := le_mul_self.trans

@[to_additive]
lemma le_iff_exists_mul : a ≤ b ↔ ∃ c, b = a * c :=
⟨exists_mul_of_le, by { rintro ⟨c, rfl⟩, exact le_self_mul }⟩

@[to_additive]
lemma le_iff_exists_mul' : a ≤ b ↔ ∃ c, b = c * a :=
by simpa only [mul_comm _ a] using le_iff_exists_mul

@[simp, to_additive zero_le] lemma one_le (a : α) : 1 ≤ a :=
le_iff_exists_mul.mpr ⟨a, (one_mul _).symm⟩

@[to_additive] lemma bot_eq_one : (⊥ : α) = 1 :=
le_antisymm bot_le (one_le ⊥)

@[simp, to_additive] lemma mul_eq_one_iff : a * b = 1 ↔ a = 1 ∧ b = 1 :=
mul_eq_one_iff' (one_le _) (one_le _)

@[simp, to_additive] lemma le_one_iff_eq_one : a ≤ 1 ↔ a = 1 :=
(one_le a).le_iff_eq

@[to_additive] lemma one_lt_iff_ne_one : 1 < a ↔ a ≠ 1 :=
(one_le a).lt_iff_ne.trans ne_comm

@[to_additive] lemma eq_one_or_one_lt : a = 1 ∨ 1 < a :=
(one_le a).eq_or_lt.imp_left eq.symm

@[simp, to_additive add_pos_iff] lemma one_lt_mul_iff : 1 < a * b ↔ 1 < a ∨ 1 < b :=
by simp only [one_lt_iff_ne_one, ne.def, mul_eq_one_iff, not_and_distrib]

@[to_additive] lemma exists_one_lt_mul_of_lt (h : a < b) : ∃ c (hc : 1 < c), a * c = b :=
begin
  obtain ⟨c, hc⟩ := le_iff_exists_mul.1 h.le,
  refine ⟨c, one_lt_iff_ne_one.2 _, hc.symm⟩,
  rintro rfl,
  simpa [hc, lt_irrefl] using h
end

@[to_additive] lemma le_mul_left (h : a ≤ c) : a ≤ b * c :=
calc a = 1 * a : by simp
  ... ≤ b * c : mul_le_mul' (one_le _) h

@[to_additive] lemma le_mul_right (h : a ≤ b) : a ≤ b * c :=
calc a = a * 1 : by simp
  ... ≤ b * c : mul_le_mul' h (one_le _)

@[to_additive]
lemma lt_iff_exists_mul [covariant_class α α (*) (<)] : a < b ↔ ∃ c > 1, b = a * c :=
begin
  simp_rw [lt_iff_le_and_ne, and_comm, le_iff_exists_mul, ← exists_and_distrib_left, exists_prop],
  apply exists_congr, intro c,
  rw [and.congr_left_iff, gt_iff_lt], rintro rfl,
  split,
  { rw [one_lt_iff_ne_one], apply mt, rintro rfl, rw [mul_one] },
  { rw [← (self_le_mul_right a c).lt_iff_ne], apply lt_mul_of_one_lt_right' }
end

instance with_zero.has_exists_add_of_le {α} [has_add α] [preorder α] [has_exists_add_of_le α] :
  has_exists_add_of_le (with_zero α) :=
⟨λ a b, begin
  apply with_zero.cases_on a,
  { exact λ _, ⟨b, (zero_add b).symm⟩ },
  apply with_zero.cases_on b,
  { exact λ b' h, (with_bot.not_coe_le_bot _ h).elim },
  rintro a' b' h,
  obtain ⟨c, rfl⟩ := exists_add_of_le (with_zero.coe_le_coe.1 h),
  exact ⟨c, rfl⟩,
end⟩

-- This instance looks absurd: a monoid already has a zero
/-- Adding a new zero to a canonically ordered additive monoid produces another one. -/
instance with_zero.canonically_ordered_add_monoid {α : Type u} [canonically_ordered_add_monoid α] :
  canonically_ordered_add_monoid (with_zero α) :=
{ le_self_add := λ a b, begin
    apply with_zero.cases_on a,
    { exact bot_le },
    apply with_zero.cases_on b,
    { exact λ b', le_rfl },
    { exact λ a' b', with_zero.coe_le_coe.2 le_self_add }
  end,
  .. with_zero.order_bot,
  .. with_zero.ordered_add_comm_monoid zero_le, ..with_zero.has_exists_add_of_le }

end canonically_ordered_monoid

lemma pos_of_gt {M : Type*} [canonically_ordered_add_monoid M] {n m : M} (h : n < m) : 0 < m :=
lt_of_le_of_lt (zero_le _) h

@[priority 100] instance canonically_ordered_add_monoid.zero_le_one_class {M : Type*}
  [canonically_ordered_add_monoid M] [has_one M] : zero_le_one_class M :=
⟨zero_le 1⟩

/-- A canonically linear-ordered additive monoid is a canonically ordered additive monoid
    whose ordering is a linear order. -/
@[protect_proj, ancestor canonically_ordered_add_monoid linear_order]
class canonically_linear_ordered_add_monoid (α : Type*)
      extends canonically_ordered_add_monoid α, linear_order α

/-- A canonically linear-ordered monoid is a canonically ordered monoid
    whose ordering is a linear order. -/
@[protect_proj, ancestor canonically_ordered_monoid linear_order, to_additive]
class canonically_linear_ordered_monoid (α : Type*)
      extends canonically_ordered_monoid α, linear_order α

section canonically_linear_ordered_monoid
variables [canonically_linear_ordered_monoid α]

@[priority 100, to_additive]  -- see Note [lower instance priority]
instance canonically_linear_ordered_monoid.semilattice_sup : semilattice_sup α :=
{ ..linear_order.to_lattice }

instance with_zero.canonically_linear_ordered_add_monoid
  (α : Type*) [canonically_linear_ordered_add_monoid α] :
    canonically_linear_ordered_add_monoid (with_zero α) :=
{ .. with_zero.canonically_ordered_add_monoid,
  .. with_zero.linear_order }

@[to_additive]
lemma min_mul_distrib (a b c : α) : min a (b * c) = min a (min a b * min a c) :=
begin
  cases le_total a b with hb hb,
  { simp [hb, le_mul_right] },
  { cases le_total a c with hc hc,
    { simp [hc, le_mul_left] },
    { simp [hb, hc] } }
end

@[to_additive]
lemma min_mul_distrib' (a b c : α) : min (a * b) c = min (min a c * min b c) c :=
by simpa [min_comm _ c] using min_mul_distrib c a b

@[simp, to_additive]
lemma one_min (a : α) : min 1 a = 1 :=
min_eq_left (one_le a)

@[simp, to_additive]
lemma min_one (a : α) : min a 1 = 1 :=
min_eq_right (one_le a)

/-- In a linearly ordered monoid, we are happy for `bot_eq_one` to be a `@[simp]` lemma. -/
@[simp, to_additive
  "In a linearly ordered monoid, we are happy for `bot_eq_zero` to be a `@[simp]` lemma"]
lemma bot_eq_one' : (⊥ : α) = 1 :=
bot_eq_one

end canonically_linear_ordered_monoid

namespace prod

variables {β : Type*}

@[to_additive] instance [canonically_ordered_monoid α] [canonically_ordered_monoid β] :
  canonically_ordered_monoid (α × β) :=
{ le_self_mul := λ a b, ⟨le_self_mul, le_self_mul⟩,
  ..prod.ordered_comm_monoid, ..prod.order_bot _ _, ..prod.has_exists_mul_of_le }

end prod

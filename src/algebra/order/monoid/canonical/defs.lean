/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import order.bounded_order
import order.min_max
import algebra.ne_zero
import algebra.order.monoid.defs

/-!
# Canonically ordered monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

universe u
variables {α : Type u}

set_option old_structure_cmd true

/-- An `ordered_comm_monoid` with one-sided 'division' in the sense that
if `a ≤ b`, there is some `c` for which `a * c = b`. This is a weaker version
of the condition on canonical orderings defined by `canonically_ordered_monoid`. -/
class has_exists_mul_of_le (α : Type u) [has_mul α] [has_le α] : Prop :=
(exists_mul_of_le : ∀ {a b : α}, a ≤ b → ∃ (c : α), b = a * c)

/-- An `ordered_add_comm_monoid` with one-sided 'subtraction' in the sense that
if `a ≤ b`, then there is some `c` for which `a + c = b`. This is a weaker version
of the condition on canonical orderings defined by `canonically_ordered_add_monoid`. -/
class has_exists_add_of_le (α : Type u) [has_add α] [has_le α] : Prop :=
(exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ (c : α), b = a + c)

attribute [to_additive] has_exists_mul_of_le

export has_exists_mul_of_le (exists_mul_of_le)

export has_exists_add_of_le (exists_add_of_le)

@[priority 100, to_additive] -- See note [lower instance priority]
instance group.has_exists_mul_of_le (α : Type u) [group α] [has_le α] : has_exists_mul_of_le α :=
⟨λ a b hab, ⟨a⁻¹ * b, (mul_inv_cancel_left _ _).symm⟩⟩

section mul_one_class
variables [mul_one_class α] [preorder α] [contravariant_class α α (*) (<)] [has_exists_mul_of_le α]
  {a b : α}

@[to_additive] lemma exists_one_lt_mul_of_lt' (h : a < b) : ∃ c, 1 < c ∧ a * c = b :=
by { obtain ⟨c, rfl⟩ := exists_mul_of_le h.le, exact ⟨c, one_lt_of_lt_mul_right h, rfl⟩ }

end mul_one_class

section has_exists_mul_of_le
variables [linear_order α] [densely_ordered α] [monoid α] [has_exists_mul_of_le α]
  [covariant_class α α (*) (<)] [contravariant_class α α (*) (<)] {a b : α}

@[to_additive]
lemma le_of_forall_one_lt_le_mul (h : ∀ ε : α, 1 < ε → a ≤ b * ε) : a ≤ b :=
le_of_forall_le_of_dense $ λ x hxb, by { obtain ⟨ε, rfl⟩ := exists_mul_of_le hxb.le,
  exact h _ ((lt_mul_iff_one_lt_right' b).1 hxb) }

@[to_additive]
lemma le_of_forall_one_lt_lt_mul' (h : ∀ ε : α, 1 < ε → a < b * ε) : a ≤ b :=
le_of_forall_one_lt_le_mul $ λ ε hε, (h _ hε).le

@[to_additive]
lemma le_iff_forall_one_lt_lt_mul' : a ≤ b ↔ ∀ ε, 1 < ε → a < b * ε :=
⟨λ h ε, lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul'⟩

end has_exists_mul_of_le

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

end canonically_ordered_monoid

lemma pos_of_gt {M : Type*} [canonically_ordered_add_monoid M] {n m : M} (h : n < m) : 0 < m :=
lt_of_le_of_lt (zero_le _) h

namespace ne_zero

lemma pos {M} (a : M) [canonically_ordered_add_monoid M] [ne_zero a] : 0 < a :=
(zero_le a).lt_of_ne $ ne_zero.out.symm

lemma of_gt {M} [canonically_ordered_add_monoid M] {x y : M} (h : x < y) : ne_zero y :=
of_pos $ pos_of_gt h

-- 1 < p is still an often-used `fact`, due to `nat.prime` implying it, and it implying `nontrivial`
-- on `zmod`'s ring structure. We cannot just set this to be any `x < y`, else that becomes a
-- metavariable and it will hugely slow down typeclass inference.
@[priority 10]
instance of_gt' {M} [canonically_ordered_add_monoid M] [has_one M] {y : M}
  [fact (1 < y)] : ne_zero y :=
of_gt $ fact.out $ 1 < y

instance bit0 {M} [canonically_ordered_add_monoid M] {x : M} [ne_zero x] : ne_zero (bit0 x) :=
of_pos $ bit0_pos $ ne_zero.pos x

end ne_zero

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

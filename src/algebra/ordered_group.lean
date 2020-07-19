/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.group.with_one
import algebra.group.type_tags
import order.bounded_lattice

set_option old_structure_cmd true
set_option default_priority 100 -- see Note [default priority]

/-!
# Ordered monoids and groups

This file develops the basics of ordered monoids and groups.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.

-/

universe u
variable {α : Type u}

/-- An ordered commutative monoid is a commutative monoid
with a partial order such that
  * `a ≤ b → c * a ≤ c * b` (multiplication is monotone)
  * `a * b < a * c → b < c`.
-/
@[protect_proj, ancestor comm_monoid partial_order]
class ordered_comm_monoid (α : Type*) extends comm_monoid α, partial_order α :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
(lt_of_mul_lt_mul_left : ∀ a b c : α, a * b < a * c → b < c)

/-- An ordered (additive) commutative monoid is a commutative monoid
  with a partial order such that
  * `a ≤ b → c + a ≤ c + b` (addition is monotone)
  * `a + b < a + c → b < c`.
-/
@[protect_proj, ancestor add_comm_monoid partial_order]
class ordered_add_comm_monoid (α : Type*) extends add_comm_monoid α, partial_order α :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(lt_of_add_lt_add_left : ∀ a b c : α, a + b < a + c → b < c)

attribute [to_additive ordered_add_comm_monoid] ordered_comm_monoid

section ordered_comm_monoid
variables [ordered_comm_monoid α] {a b c d : α}

@[to_additive add_le_add_left]
lemma mul_le_mul_left' (h : a ≤ b) (c) : c * a ≤ c * b :=
ordered_comm_monoid.mul_le_mul_left a b h c

@[to_additive add_le_add_right]
lemma mul_le_mul_right' (h : a ≤ b) (c) : a * c ≤ b * c :=
mul_comm c a ▸ mul_comm c b ▸ mul_le_mul_left' h c

@[to_additive lt_of_add_lt_add_left]
lemma lt_of_mul_lt_mul_left' : a * b < a * c → b < c :=
ordered_comm_monoid.lt_of_mul_lt_mul_left a b c

@[to_additive add_le_add]
lemma mul_le_mul' (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
le_trans (mul_le_mul_right' h₁ _) (mul_le_mul_left' h₂ _)

@[to_additive]
lemma mul_le_mul_three {a b c d e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) :
      a * b * c ≤ d * e * f :=
mul_le_mul' (mul_le_mul' h₁ h₂) h₃

@[to_additive]
lemma le_mul_of_one_le_right (h : 1 ≤ b) : a ≤ a * b :=
have a * 1 ≤ a * b, from mul_le_mul_left' h _,
by rwa mul_one at this

@[to_additive]
lemma le_mul_of_one_le_left (h : 1 ≤ b) : a ≤ b * a :=
have 1 * a ≤ b * a, from mul_le_mul_right' h a,
by rwa one_mul at this

@[to_additive lt_of_add_lt_add_right]
lemma lt_of_mul_lt_mul_right' (h : a * b < c * b) : a < c :=
lt_of_mul_lt_mul_left'
  (show b * a < b * c, begin rw [mul_comm b a, mul_comm b c], assumption end)

-- here we start using properties of one.
@[to_additive]
lemma le_mul_of_one_le_of_le (ha : 1 ≤ a) (hbc : b ≤ c) : b ≤ a * c :=
one_mul b ▸ mul_le_mul' ha hbc

@[to_additive]
lemma le_mul_of_le_of_one_le (hbc : b ≤ c) (ha : 1 ≤ a) : b ≤ c * a :=
mul_one b ▸ mul_le_mul' hbc ha

@[to_additive add_nonneg]
lemma one_le_mul (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
le_mul_of_one_le_of_le ha hb

@[to_additive add_pos_of_pos_of_nonneg]
lemma one_lt_mul_of_lt_of_le' (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
lt_of_lt_of_le ha $ le_mul_of_one_le_right hb

@[to_additive add_pos_of_nonneg_of_pos]
lemma one_lt_mul_of_le_of_lt' (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
lt_of_lt_of_le hb $ le_mul_of_one_le_left ha

@[to_additive add_pos]
lemma one_lt_mul' (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
one_lt_mul_of_lt_of_le' ha $ le_of_lt hb

@[to_additive add_nonpos]
lemma mul_le_one' (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
one_mul (1:α) ▸ (mul_le_mul' ha hb)

@[to_additive]
lemma mul_le_of_le_one_of_le' (ha : a ≤ 1) (hbc : b ≤ c) : a * b ≤ c :=
one_mul c ▸ mul_le_mul' ha hbc

@[to_additive]
lemma mul_le_of_le_of_le_one' (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
mul_one c ▸ mul_le_mul' hbc ha

@[to_additive]
lemma mul_lt_one_of_lt_one_of_le_one' (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
lt_of_le_of_lt (mul_le_of_le_of_le_one' (le_refl _) hb) ha

@[to_additive]
lemma mul_lt_one_of_le_one_of_lt_one' (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
lt_of_le_of_lt (mul_le_of_le_one_of_le' ha (le_refl _)) hb

@[to_additive]
lemma mul_lt_one' (ha : a < 1) (hb : b < 1) : a * b < 1 :=
mul_lt_one_of_le_one_of_lt_one' (le_of_lt ha) hb

@[to_additive]
lemma lt_mul_of_one_le_of_lt' (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
lt_of_lt_of_le hbc $ le_mul_of_one_le_left ha

@[to_additive]
lemma lt_mul_of_lt_of_one_le' (hbc : b < c) (ha : 1 ≤ a) : b < c * a :=
lt_of_lt_of_le hbc $ le_mul_of_one_le_right ha

@[to_additive]
lemma lt_mul_of_one_lt_of_lt' (ha : 1 < a) (hbc : b < c) : b < a * c :=
lt_mul_of_one_le_of_lt' (le_of_lt ha) hbc

@[to_additive]
lemma lt_mul_of_lt_of_one_lt' (hbc : b < c) (ha : 1 < a) : b < c * a :=
lt_mul_of_lt_of_one_le' hbc (le_of_lt ha)

@[to_additive]
lemma mul_lt_of_le_one_of_lt' (ha : a ≤ 1) (hbc : b < c) : a * b < c :=
lt_of_le_of_lt (mul_le_of_le_one_of_le' ha (le_refl _)) hbc

@[to_additive]
lemma mul_lt_of_lt_of_le_one' (hbc : b < c) (ha : a ≤ 1)  : b * a < c :=
lt_of_le_of_lt (mul_le_of_le_of_le_one' (le_refl _) ha) hbc

@[to_additive]
lemma mul_lt_of_lt_one_of_lt' (ha : a < 1) (hbc : b < c) : a * b < c :=
mul_lt_of_le_one_of_lt' (le_of_lt ha) hbc

@[to_additive]
lemma mul_lt_of_lt_of_lt_one' (hbc : b < c) (ha : a < 1) : b * a < c :=
mul_lt_of_lt_of_le_one' hbc (le_of_lt ha)

@[to_additive]
lemma mul_eq_one_iff' (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b = 1 ↔ a = 1 ∧ b = 1 :=
iff.intro
  (assume hab : a * b = 1,
   have a ≤ 1, from hab ▸ le_mul_of_le_of_one_le (le_refl _) hb,
   have a = 1, from le_antisymm this ha,
   have b ≤ 1, from hab ▸ le_mul_of_one_le_of_le ha (le_refl _),
   have b = 1, from le_antisymm this hb,
   and.intro ‹a = 1› ‹b = 1›)
  (assume ⟨ha', hb'⟩, by rw [ha', hb', mul_one])

section mono

variables {β : Type*} [preorder β] {f g : β → α}

@[to_additive monotone.add]
lemma monotone.mul' (hf : monotone f) (hg : monotone g) : monotone (λ x, f x * g x) :=
λ x y h, mul_le_mul' (hf h) (hg h)

@[to_additive monotone.add_const]
lemma monotone.mul_const' (hf : monotone f) (a : α) : monotone (λ x, f x * a) :=
hf.mul' monotone_const

@[to_additive monotone.const_add]
lemma monotone.const_mul' (hf : monotone f) (a : α) : monotone (λ x, a * f x) :=
monotone_const.mul' hf

end mono

end ordered_comm_monoid

lemma bit0_pos [ordered_add_comm_monoid α] {a : α} (h : 0 < a) : 0 < bit0 a :=
add_pos h h

namespace units

@[to_additive]
instance [monoid α] [preorder α] : preorder (units α) :=
preorder.lift (coe : units α → α)

@[simp, to_additive, norm_cast]
theorem coe_le_coe [monoid α] [preorder α] {a b : units α} :
  (a : α) ≤ b ↔ a ≤ b := iff.rfl

@[simp, to_additive, norm_cast]
theorem coe_lt_coe [monoid α] [preorder α] {a b : units α} :
  (a : α) < b ↔ a < b := iff.rfl

@[to_additive]
instance [monoid α] [partial_order α] : partial_order (units α) :=
partial_order.lift coe units.ext

@[to_additive]
instance [monoid α] [linear_order α] : linear_order (units α) :=
linear_order.lift coe units.ext

@[to_additive]
instance [monoid α] [decidable_linear_order α] : decidable_linear_order (units α) :=
decidable_linear_order.lift coe units.ext

@[simp, to_additive, norm_cast]
theorem max_coe [monoid α] [decidable_linear_order α] {a b : units α} :
  (↑(max a b) : α) = max a b :=
by by_cases a ≤ b; simp [max, h]

@[simp, to_additive, norm_cast]
theorem min_coe [monoid α] [decidable_linear_order α] {a b : units α} :
  (↑(min a b) : α) = min a b :=
by by_cases a ≤ b; simp [min, h]

end units

namespace with_zero

instance [preorder α] : preorder (with_zero α) := with_bot.preorder
instance [partial_order α] : partial_order (with_zero α) := with_bot.partial_order
instance [partial_order α] : order_bot (with_zero α) := with_bot.order_bot
instance [lattice α] : lattice (with_zero α) := with_bot.lattice
instance [linear_order α] : linear_order (with_zero α) := with_bot.linear_order
instance [decidable_linear_order α] :
 decidable_linear_order (with_zero α) := with_bot.decidable_linear_order

/--
If `0` is the least element in `α`, then `with_zero α` is an `ordered_add_comm_monoid`.
-/
def ordered_add_comm_monoid [ordered_add_comm_monoid α]
  (zero_le : ∀ a : α, 0 ≤ a) : ordered_add_comm_monoid (with_zero α) :=
begin
  suffices, refine {
    add_le_add_left := this,
    ..with_zero.partial_order,
    ..with_zero.add_comm_monoid, .. },
  { intros a b c h,
    have h' := lt_iff_le_not_le.1 h,
    rw lt_iff_le_not_le at ⊢,
    refine ⟨λ b h₂, _, λ h₂, h'.2 $ this _ _ h₂ _⟩,
    cases h₂, cases c with c,
    { cases h'.2 (this _ _ bot_le a) },
    { refine ⟨_, rfl, _⟩,
      cases a with a,
      { exact with_bot.some_le_some.1 h'.1 },
      { exact le_of_lt (lt_of_add_lt_add_left $
          with_bot.some_lt_some.1 h), } } },
  { intros a b h c ca h₂,
    cases b with b,
    { rw le_antisymm h bot_le at h₂,
      exact ⟨_, h₂, le_refl _⟩ },
    cases a with a,
    { change c + 0 = some ca at h₂,
      simp at h₂, simp [h₂],
      exact ⟨_, rfl, by simpa using add_le_add_left (zero_le b) _⟩ },
    { simp at h,
      cases c with c; change some _ = _ at h₂;
        simp [-add_comm] at h₂; subst ca; refine ⟨_, rfl, _⟩,
      { exact h },
      { exact add_le_add_left h _ } } }
end

end with_zero

namespace with_top

section has_one

variables [has_one α]

@[to_additive] instance : has_one (with_top α) := ⟨(1 : α)⟩

@[simp, to_additive] lemma coe_one : ((1 : α) : with_top α) = 1 := rfl

@[simp, to_additive] lemma coe_eq_one {a : α} : (a : with_top α) = 1 ↔ a = 1 :=
coe_eq_coe

@[simp, to_additive] theorem one_eq_coe {a : α} : 1 = (a : with_top α) ↔ a = 1 :=
by rw [eq_comm, coe_eq_one]

attribute [norm_cast] coe_one coe_eq_one coe_zero coe_eq_zero one_eq_coe zero_eq_coe

@[simp, to_additive] theorem top_ne_one : ⊤ ≠ (1 : with_top α) .
@[simp, to_additive] theorem one_ne_top : (1 : with_top α) ≠ ⊤ .

end has_one

instance [has_add α] : has_add (with_top α) :=
⟨λ o₁ o₂, o₁.bind (λ a, o₂.map (λ b, a + b))⟩

instance [add_semigroup α] : add_semigroup (with_top α) :=
{ add := (+),
  ..@additive.add_semigroup _ $ @with_zero.semigroup (multiplicative α) _ }

@[norm_cast] lemma coe_add [has_add α] {a b : α} : ((a + b : α) : with_top α) = a + b := rfl

@[norm_cast] lemma coe_bit0 [has_add α] {a : α} : ((bit0 a : α) : with_top α) = bit0 a := rfl

@[norm_cast]
lemma coe_bit1 [has_add α] [has_one α] {a : α} : ((bit1 a : α) : with_top α) = bit1 a := rfl

instance [add_comm_semigroup α] : add_comm_semigroup (with_top α) :=
{ ..@additive.add_comm_semigroup _ $
    @with_zero.comm_semigroup (multiplicative α) _ }

instance [add_monoid α] : add_monoid (with_top α) :=
{ zero := some 0,
  add := (+),
  ..@additive.add_monoid _ $ @monoid_with_zero.to_monoid _ $
    @with_zero.monoid_with_zero (multiplicative α) _ }

instance [add_comm_monoid α] : add_comm_monoid (with_top α) :=
{ zero := 0,
  add := (+),
  ..@additive.add_comm_monoid _ $ @comm_monoid_with_zero.to_comm_monoid _ $
    @with_zero.comm_monoid_with_zero (multiplicative α) _ }

instance [ordered_add_comm_monoid α] : ordered_add_comm_monoid (with_top α) :=
begin
  suffices, refine {
    add_le_add_left := this,
    ..with_top.partial_order,
    ..with_top.add_comm_monoid, ..},
  { intros a b c h,
    have h' := h,
    rw lt_iff_le_not_le at h' ⊢,
    refine ⟨λ c h₂, _, λ h₂, h'.2 $ this _ _ h₂ _⟩,
    cases h₂, cases a with a,
    { exact (not_le_of_lt h).elim le_top },
    cases b with b,
    { exact (not_le_of_lt h).elim le_top },
    { exact ⟨_, rfl, le_of_lt (lt_of_add_lt_add_left $
        with_top.some_lt_some.1 h)⟩ } },
  { intros a b h c ca h₂,
    cases c with c, {cases h₂},
    cases b with b; cases h₂,
    cases a with a, {cases le_antisymm h le_top },
    simp at h,
    exact ⟨_, rfl, add_le_add_left h _⟩, }
end

@[simp] lemma zero_lt_top [ordered_add_comm_monoid α] : (0 : with_top α) < ⊤ :=
coe_lt_top 0

@[simp, norm_cast] lemma zero_lt_coe [ordered_add_comm_monoid α] (a : α) : (0 : with_top α) < a ↔ 0 < a :=
coe_lt_coe

@[simp] lemma add_top [ordered_add_comm_monoid α] : ∀{a : with_top α}, a + ⊤ = ⊤
| none := rfl
| (some a) := rfl

@[simp] lemma top_add [ordered_add_comm_monoid α] {a : with_top α} : ⊤ + a = ⊤ := rfl

lemma add_eq_top [ordered_add_comm_monoid α] (a b : with_top α) : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
by cases a; cases b; simp [none_eq_top, some_eq_coe, coe_add.symm]

lemma add_lt_top [ordered_add_comm_monoid α] (a b : with_top α) : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ :=
by simp [lt_top_iff_ne_top, add_eq_top, not_or_distrib]

end with_top

namespace with_bot

instance [has_zero α] : has_zero (with_bot α) := with_top.has_zero
instance [has_one α] : has_one (with_bot α) := with_top.has_one
instance [add_semigroup α] : add_semigroup (with_bot α) := with_top.add_semigroup
instance [add_comm_semigroup α] : add_comm_semigroup (with_bot α) := with_top.add_comm_semigroup
instance [add_monoid α] : add_monoid (with_bot α) := with_top.add_monoid
instance [add_comm_monoid α] : add_comm_monoid (with_bot α) :=  with_top.add_comm_monoid

instance [ordered_add_comm_monoid α] : ordered_add_comm_monoid (with_bot α) :=
begin
  suffices, refine {
    add_le_add_left := this,
    ..with_bot.partial_order,
    ..with_bot.add_comm_monoid, ..},
  { intros a b c h,
    have h' := h,
    rw lt_iff_le_not_le at h' ⊢,
    refine ⟨λ b h₂, _, λ h₂, h'.2 $ this _ _ h₂ _⟩,
    cases h₂, cases a with a,
    { exact (not_le_of_lt h).elim bot_le },
    cases c with c,
    { exact (not_le_of_lt h).elim bot_le },
    { exact ⟨_, rfl, le_of_lt (lt_of_add_lt_add_left $
        with_bot.some_lt_some.1 h)⟩ } },
  { intros a b h c ca h₂,
    cases c with c, {cases h₂},
    cases a with a; cases h₂,
    cases b with b, {cases le_antisymm h bot_le},
    simp at h,
    exact ⟨_, rfl, add_le_add_left h _⟩, }
end

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_zero [has_zero α] : ((0 : α) : with_bot α) = 0 := rfl

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_one [has_one α] : ((1 : α) : with_bot α) = 1 := rfl

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_eq_zero {α : Type*}
  [add_monoid α] {a : α} : (a : with_bot α) = 0 ↔ a = 0 :=
by norm_cast

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_add [add_semigroup α] (a b : α) : ((a + b : α) : with_bot α) = a + b := by norm_cast

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_bit0 [add_semigroup α] {a : α} : ((bit0 a : α) : with_bot α) = bit0 a :=
by norm_cast

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_bit1 [add_semigroup α] [has_one α] {a : α} : ((bit1 a : α) : with_bot α) = bit1 a :=
by norm_cast

@[simp] lemma bot_add [ordered_add_comm_monoid α] (a : with_bot α) : ⊥ + a = ⊥ := rfl

@[simp] lemma add_bot [ordered_add_comm_monoid α] (a : with_bot α) : a + ⊥ = ⊥ := by cases a; refl

end with_bot

/-- A canonically ordered monoid is an ordered commutative monoid
  in which the ordering coincides with the divisibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a + c`.
  This is satisfied by the natural numbers, for example, but not
  the integers or other ordered groups. -/
@[protect_proj]
class canonically_ordered_add_monoid (α : Type*) extends ordered_add_comm_monoid α, order_bot α :=
(le_iff_exists_add : ∀a b:α, a ≤ b ↔ ∃c, b = a + c)

section canonically_ordered_add_monoid
variables [canonically_ordered_add_monoid α] {a b c d : α}

lemma le_iff_exists_add : a ≤ b ↔ ∃c, b = a + c :=
canonically_ordered_add_monoid.le_iff_exists_add a b

@[simp] lemma zero_le (a : α) : 0 ≤ a := le_iff_exists_add.mpr ⟨a, by simp⟩

@[simp] lemma bot_eq_zero : (⊥ : α) = 0 :=
le_antisymm bot_le (zero_le ⊥)

@[simp] lemma add_eq_zero_iff : a + b = 0 ↔ a = 0 ∧ b = 0 :=
add_eq_zero_iff' (zero_le _) (zero_le _)

@[simp] lemma le_zero_iff_eq : a ≤ 0 ↔ a = 0 :=
iff.intro
  (assume h, le_antisymm h (zero_le a))
  (assume h, h ▸ le_refl a)

lemma zero_lt_iff_ne_zero : 0 < a ↔ a ≠ 0 :=
iff.intro ne_of_gt $ assume hne, lt_of_le_of_ne (zero_le _) hne.symm

@[nolint ge_or_gt]
lemma exists_pos_add_of_lt (h : a < b) : ∃ c > 0, a + c = b :=
begin
  obtain ⟨c, hc⟩ := le_iff_exists_add.1 (le_of_lt h),
  refine ⟨c, zero_lt_iff_ne_zero.2 _, hc.symm⟩,
  rintro rfl,
  simpa [hc, lt_irrefl] using h
end

lemma le_add_left (h : a ≤ c) : a ≤ b + c :=
calc a = 0 + a : by simp
  ... ≤ b + c : add_le_add (zero_le _) h

lemma le_add_right (h : a ≤ b) : a ≤ b + c :=
calc a = a + 0 : by simp
  ... ≤ b + c : add_le_add h (zero_le _)

instance with_zero.canonically_ordered_add_monoid :
  canonically_ordered_add_monoid (with_zero α) :=
{ le_iff_exists_add := λ a b, begin
    cases a with a,
    { exact iff_of_true bot_le ⟨b, (zero_add b).symm⟩ },
    cases b with b,
    { exact iff_of_false
        (mt (le_antisymm bot_le) (by simp))
        (λ ⟨c, h⟩, by cases c; cases h) },
    { simp [le_iff_exists_add, -add_comm],
      split; intro h; rcases h with ⟨c, h⟩,
      { exact ⟨some c, congr_arg some h⟩ },
      { cases c; cases h,
        { exact ⟨_, (add_zero _).symm⟩ },
        { exact ⟨_, rfl⟩ } } }
  end,
  bot    := 0,
  bot_le := assume a a' h, option.no_confusion h,
  .. with_zero.ordered_add_comm_monoid zero_le }

instance with_top.canonically_ordered_add_monoid : canonically_ordered_add_monoid (with_top α) :=
{ le_iff_exists_add := assume a b,
  match a, b with
  | a, none     := show a ≤ ⊤ ↔ ∃c, ⊤ = a + c, by simp; refine ⟨⊤, _⟩; cases a; refl
  | (some a), (some b) := show (a:with_top α) ≤ ↑b ↔ ∃c:with_top α, ↑b = ↑a + c,
    begin
      simp [canonically_ordered_add_monoid.le_iff_exists_add, -add_comm],
      split,
      { rintro ⟨c, rfl⟩, refine ⟨c, _⟩, norm_cast },
      { exact assume h, match b, h with _, ⟨some c, rfl⟩ := ⟨_, rfl⟩ end }
    end
  | none, some b := show (⊤ : with_top α) ≤ b ↔ ∃c:with_top α, ↑b = ⊤ + c, by simp
  end,
  .. with_top.order_bot,
  .. with_top.ordered_add_comm_monoid }

end canonically_ordered_add_monoid

/-- An ordered cancellative additive commutative monoid
is an additive commutative monoid with a partial order,
in which addition is cancellative and strictly monotone. -/
@[protect_proj, ancestor add_comm_monoid add_left_cancel_semigroup add_right_cancel_semigroup partial_order]
class ordered_cancel_add_comm_monoid (α : Type u)
      extends add_comm_monoid α, add_left_cancel_semigroup α,
              add_right_cancel_semigroup α, partial_order α :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c)

/-- An ordered cancellative commutative monoid
is a commutative monoid with a partial order,
in which multiplication is cancellative and strictly monotone. -/
@[protect_proj, ancestor comm_monoid left_cancel_semigroup right_cancel_semigroup partial_order]
class ordered_cancel_comm_monoid (α : Type u)
      extends comm_monoid α, left_cancel_semigroup α,
              right_cancel_semigroup α, partial_order α :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
(le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c)

attribute [to_additive ordered_cancel_add_comm_monoid] ordered_cancel_comm_monoid

section ordered_cancel_comm_monoid
variables [ordered_cancel_comm_monoid α] {a b c d : α}

@[to_additive]
instance ordered_cancel_comm_monoid.to_left_cancel_monoid :
  left_cancel_monoid α := { ..‹ordered_cancel_comm_monoid α› }

@[to_additive le_of_add_le_add_left]
lemma le_of_mul_le_mul_left' : ∀ {a b c : α}, a * b ≤ a * c → b ≤ c :=
ordered_cancel_comm_monoid.le_of_mul_le_mul_left

@[to_additive]
instance ordered_cancel_comm_monoid.to_ordered_comm_monoid : ordered_comm_monoid α :=
{ lt_of_mul_lt_mul_left := λ a b c h, lt_of_le_not_le (le_of_mul_le_mul_left' (le_of_lt h)) $
      mt (λ h, ordered_cancel_comm_monoid.mul_le_mul_left _ _ h _) (not_le_of_gt h),
  ..‹ordered_cancel_comm_monoid α› }

@[to_additive add_lt_add_left]
lemma mul_lt_mul_left' (h : a < b) (c : α) : c * a < c * b :=
lt_of_le_not_le (mul_le_mul_left' (le_of_lt h) _) $
  mt le_of_mul_le_mul_left' (not_le_of_gt h)

@[to_additive add_lt_add_right]
lemma mul_lt_mul_right' (h : a < b) (c : α) : a * c < b * c :=
begin
 rw [mul_comm a c, mul_comm b c],
 exact (mul_lt_mul_left' h c)
end

@[to_additive add_lt_add]
lemma mul_lt_mul''' (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
lt_trans (mul_lt_mul_right' h₁ c) (mul_lt_mul_left' h₂ b)

@[to_additive]
lemma mul_lt_mul_of_le_of_lt (h₁ : a ≤ b) (h₂ : c < d) : a * c < b * d :=
lt_of_le_of_lt (mul_le_mul_right' h₁ _) (mul_lt_mul_left' h₂ b)

@[to_additive]
lemma mul_lt_mul_of_lt_of_le (h₁ : a < b) (h₂ : c ≤ d) : a * c < b * d :=
lt_of_lt_of_le (mul_lt_mul_right' h₁ c) (mul_le_mul_left' h₂ _)

@[to_additive]
lemma lt_mul_of_one_lt_right (a : α) {b : α} (h : 1 < b) : a < a * b :=
have a * 1 < a * b, from mul_lt_mul_left' h a,
by rwa [mul_one] at this

@[to_additive]
lemma lt_mul_of_one_lt_left (a : α) {b : α} (h : 1 < b) : a < b * a :=
have 1 * a < b * a, from mul_lt_mul_right' h a,
by rwa [one_mul] at this

@[to_additive le_of_add_le_add_right]
lemma le_of_mul_le_mul_right' (h : a * b ≤ c * b) : a ≤ c :=
le_of_mul_le_mul_left'
  (show b * a ≤ b * c, begin rw [mul_comm b a, mul_comm b c], assumption end)

@[to_additive]
lemma mul_lt_one (ha : a < 1) (hb : b < 1) : a * b < 1 :=
one_mul (1:α) ▸ (mul_lt_mul''' ha hb)

@[to_additive]
lemma mul_lt_one_of_lt_one_of_le_one (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
one_mul (1:α) ▸ (mul_lt_mul_of_lt_of_le ha hb)

@[to_additive]
lemma mul_lt_one_of_le_one_of_lt_one (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
one_mul (1:α) ▸ (mul_lt_mul_of_le_of_lt ha hb)

@[to_additive]
lemma lt_mul_of_one_lt_of_le (ha : 1 < a) (hbc : b ≤ c) : b < a * c :=
one_mul b ▸ mul_lt_mul_of_lt_of_le ha hbc

@[to_additive]
lemma lt_mul_of_le_of_one_lt (hbc : b ≤ c) (ha : 1 < a) : b < c * a :=
mul_one b ▸ mul_lt_mul_of_le_of_lt hbc ha

@[to_additive]
lemma mul_le_of_le_one_of_le (ha : a ≤ 1) (hbc : b ≤ c) : a * b ≤ c :=
one_mul c ▸ mul_le_mul' ha hbc

@[to_additive]
lemma mul_le_of_le_of_le_one (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
mul_one c ▸ mul_le_mul' hbc ha

@[to_additive]
lemma mul_lt_of_lt_one_of_le (ha : a < 1) (hbc : b ≤ c) : a * b < c :=
one_mul c ▸ mul_lt_mul_of_lt_of_le ha hbc

@[to_additive]
lemma mul_lt_of_le_of_lt_one (hbc : b ≤ c) (ha : a < 1) : b * a < c :=
mul_one c ▸ mul_lt_mul_of_le_of_lt hbc ha

@[to_additive]
lemma lt_mul_of_one_le_of_lt (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
one_mul b ▸ mul_lt_mul_of_le_of_lt ha hbc

@[to_additive]
lemma lt_mul_of_lt_of_one_le (hbc : b < c) (ha : 1 ≤ a) : b < c * a :=
mul_one b ▸ mul_lt_mul_of_lt_of_le hbc ha

@[to_additive]
lemma lt_mul_of_one_lt_of_lt (ha : 1 < a) (hbc : b < c) : b < a * c :=
one_mul b ▸ mul_lt_mul''' ha hbc

@[to_additive]
lemma lt_mul_of_lt_of_one_lt (hbc : b < c) (ha : 1 < a) : b < c * a :=
mul_one b ▸ mul_lt_mul''' hbc ha

@[to_additive]
lemma mul_lt_of_le_one_of_lt (ha : a ≤ 1) (hbc : b < c) : a * b < c :=
one_mul c ▸ mul_lt_mul_of_le_of_lt ha hbc

@[to_additive]
lemma mul_lt_of_lt_of_le_one (hbc : b < c) (ha : a ≤ 1)  : b * a < c :=
mul_one c ▸ mul_lt_mul_of_lt_of_le hbc ha

@[to_additive]
lemma mul_lt_of_lt_one_of_lt (ha : a < 1) (hbc : b < c) : a * b < c :=
one_mul c ▸ mul_lt_mul''' ha hbc

@[to_additive]
lemma mul_lt_of_lt_of_lt_one (hbc : b < c) (ha : a < 1) : b * a < c :=
mul_one c ▸ mul_lt_mul''' hbc ha

@[simp, to_additive]
lemma mul_le_mul_iff_left (a : α) {b c : α} : a * b ≤ a * c ↔ b ≤ c :=
⟨le_of_mul_le_mul_left', λ h, mul_le_mul_left' h _⟩

@[simp, to_additive]
lemma mul_le_mul_iff_right (c : α) : a * c ≤ b * c ↔ a ≤ b :=
mul_comm c a ▸ mul_comm c b ▸ mul_le_mul_iff_left c

@[simp, to_additive]
lemma mul_lt_mul_iff_left (a : α) {b c : α} : a * b < a * c ↔ b < c :=
⟨lt_of_mul_lt_mul_left', λ h, mul_lt_mul_left' h _⟩

@[simp, to_additive]
lemma mul_lt_mul_iff_right (c : α) : a * c < b * c ↔ a < b :=
mul_comm c a ▸ mul_comm c b ▸ mul_lt_mul_iff_left c

@[simp, to_additive le_add_iff_nonneg_right]
lemma le_mul_iff_one_le_right' (a : α) {b : α} : a ≤ a * b ↔ 1 ≤ b :=
have a * 1 ≤ a * b ↔ 1 ≤ b, from mul_le_mul_iff_left a,
by rwa mul_one at this

@[simp, to_additive le_add_iff_nonneg_left]
lemma le_mul_iff_one_le_left' (a : α) {b : α} : a ≤ b * a ↔ 1 ≤ b :=
by rw [mul_comm, le_mul_iff_one_le_right']

@[simp, to_additive lt_add_iff_pos_right]
lemma lt_mul_iff_one_lt_right' (a : α) {b : α} : a < a * b ↔ 1 < b :=
have a * 1 < a * b ↔ 1 < b, from mul_lt_mul_iff_left a,
by rwa mul_one at this

@[simp, to_additive lt_add_iff_pos_left]
lemma lt_mul_iff_one_lt_left' (a : α) {b : α} : a < b * a ↔ 1 < b :=
by rw [mul_comm, lt_mul_iff_one_lt_right']

@[simp, to_additive add_le_iff_nonpos_left]
lemma mul_le_iff_le_one_left' : a * b ≤ b ↔ a ≤ 1 :=
by { convert mul_le_mul_iff_right b, rw [one_mul] }

@[simp, to_additive add_le_iff_nonpos_right]
lemma mul_le_iff_le_one_right' : a * b ≤ a ↔ b ≤ 1 :=
by { convert mul_le_mul_iff_left a, rw [mul_one] }

@[simp, to_additive add_lt_iff_neg_right]
lemma mul_lt_iff_lt_one_right' : a * b < b ↔ a < 1 :=
by { convert mul_lt_mul_iff_right b, rw [one_mul] }

@[simp, to_additive add_lt_iff_neg_left]
lemma mul_lt_iff_lt_one_left' : a * b < a ↔ b < 1 :=
by { convert mul_lt_mul_iff_left a, rw [mul_one] }

@[to_additive]
lemma mul_eq_one_iff_eq_one_of_one_le
  (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b = 1 ↔ a = 1 ∧ b = 1 :=
⟨λ hab : a * b = 1,
by split; apply le_antisymm; try {assumption};
   rw ← hab; simp [ha, hb],
λ ⟨ha', hb'⟩, by rw [ha', hb', mul_one]⟩

section mono

variables {β : Type*} [preorder β] {f g : β → α}

@[to_additive monotone.add_strict_mono]
lemma monotone.mul_strict_mono' (hf : monotone f) (hg : strict_mono g) :
  strict_mono (λ x, f x * g x) :=
λ x y h, mul_lt_mul_of_le_of_lt (hf $ le_of_lt h) (hg h)

@[to_additive strict_mono.add_monotone]
lemma strict_mono.mul_monotone' (hf : strict_mono f) (hg : monotone g) :
  strict_mono (λ x, f x * g x) :=
λ x y h, mul_lt_mul_of_lt_of_le (hf h) (hg $ le_of_lt h)

@[to_additive strict_mono.add_const]
lemma strict_mono.mul_const' (hf : strict_mono f) (c : α) :
  strict_mono (λ x, f x * c) :=
hf.mul_monotone' monotone_const

@[to_additive strict_mono.const_add]
lemma strict_mono.const_mul' (hf : strict_mono f) (c : α) :
  strict_mono (λ x, c * f x) :=
monotone_const.mul_strict_mono' hf

end mono

end ordered_cancel_comm_monoid

section ordered_cancel_add_comm_monoid

variable [ordered_cancel_add_comm_monoid α]

lemma with_top.add_lt_add_iff_left :
  ∀{a b c : with_top α}, a < ⊤ → (a + c < a + b ↔ c < b)
| none := assume b c h, (lt_irrefl ⊤ h).elim
| (some a) :=
  begin
    assume b c h,
    cases b; cases c;
      simp [with_top.none_eq_top, with_top.some_eq_coe, with_top.coe_lt_top, with_top.coe_lt_coe],
    { norm_cast, exact with_top.coe_lt_top _ },
    { norm_cast, exact add_lt_add_iff_left _ }
  end

lemma with_top.add_lt_add_iff_right
  {a b c : with_top α} : a < ⊤ → (c + a < b + a ↔ c < b) :=
by simpa [add_comm] using @with_top.add_lt_add_iff_left _ _ a b c

end ordered_cancel_add_comm_monoid

/-- An ordered additive commutative group is an additive commutative group
with a partial order in which addition is strictly monotone. -/
@[protect_proj, ancestor add_comm_group partial_order]
class ordered_add_comm_group (α : Type u) extends add_comm_group α, partial_order α :=
(add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)

/-- An ordered commutative group is an commutative group
with a partial order in which multiplication is strictly monotone. -/
@[protect_proj, ancestor comm_group partial_order]
class ordered_comm_group (α : Type u) extends comm_group α, partial_order α :=
(mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)

attribute [to_additive ordered_add_comm_group] ordered_comm_group

/--The units of an ordered commutative monoid form an ordered commutative group. -/
@[to_additive]
instance units.ordered_comm_group [ordered_comm_monoid α] : ordered_comm_group (units α) :=
{ mul_le_mul_left := λ a b h c, mul_le_mul_left' h _,
  .. units.partial_order,
  .. (infer_instance : comm_group (units α)) }

section ordered_comm_group
variables [ordered_comm_group α] {a b c d : α}

@[to_additive ordered_add_comm_group.add_lt_add_left]
lemma ordered_comm_group.mul_lt_mul_left' (a b : α) (h : a < b) (c : α) : c * a < c * b :=
begin
  rw lt_iff_le_not_le at h ⊢,
  split,
  { apply ordered_comm_group.mul_le_mul_left _ _ h.1 },
  { intro w,
    replace w : c⁻¹ * (c * b) ≤ c⁻¹ * (c * a) := ordered_comm_group.mul_le_mul_left _ _ w _,
    simp only [mul_one, mul_comm, mul_left_inv, mul_left_comm] at w,
    exact h.2 w },
end

@[to_additive ordered_add_comm_group.le_of_add_le_add_left]
lemma ordered_comm_group.le_of_mul_le_mul_left (h : a * b ≤ a * c) : b ≤ c :=
have a⁻¹ * (a * b) ≤ a⁻¹ * (a * c), from ordered_comm_group.mul_le_mul_left _ _ h _,
begin simp [inv_mul_cancel_left] at this, assumption end

@[to_additive]
lemma ordered_comm_group.lt_of_mul_lt_mul_left (h : a * b < a * c) : b < c :=
have a⁻¹ * (a * b) < a⁻¹ * (a * c), from ordered_comm_group.mul_lt_mul_left' _ _ h _,
begin simp [inv_mul_cancel_left] at this, assumption end

@[to_additive]
instance ordered_comm_group.to_ordered_cancel_comm_monoid (α : Type u)
  [s : ordered_comm_group α] : ordered_cancel_comm_monoid α :=
{ mul_left_cancel       := @mul_left_cancel α _,
  mul_right_cancel      := @mul_right_cancel α _,
  le_of_mul_le_mul_left := @ordered_comm_group.le_of_mul_le_mul_left α _,
  ..s }

@[to_additive neg_le_neg]
lemma inv_le_inv' (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
have 1 ≤ a⁻¹ * b,           from mul_left_inv a ▸ mul_le_mul_left' h _,
have 1 * b⁻¹ ≤ a⁻¹ * b * b⁻¹, from mul_le_mul_right' this _,
by rwa [mul_inv_cancel_right, one_mul] at this

@[to_additive]
lemma le_of_inv_le_inv (h : b⁻¹ ≤ a⁻¹) : a ≤ b :=
suffices (a⁻¹)⁻¹ ≤ (b⁻¹)⁻¹, from
  begin simp [inv_inv] at this, assumption end,
inv_le_inv' h

@[to_additive]
lemma one_le_of_inv_le_one (h : a⁻¹ ≤ 1) : 1 ≤ a :=
have a⁻¹ ≤ 1⁻¹, by rwa one_inv,
le_of_inv_le_inv this

@[to_additive]
lemma inv_le_one_of_one_le (h : 1 ≤ a) : a⁻¹ ≤ 1 :=
have a⁻¹ ≤ 1⁻¹, from inv_le_inv' h,
by rwa one_inv at this

@[to_additive nonpos_of_neg_nonneg]
lemma le_one_of_one_le_inv (h : 1 ≤ a⁻¹) : a ≤ 1 :=
have 1⁻¹ ≤ a⁻¹, by rwa one_inv,
le_of_inv_le_inv this

@[to_additive neg_nonneg_of_nonpos]
lemma one_le_inv_of_le_one (h : a ≤ 1) : 1 ≤ a⁻¹ :=
have 1⁻¹ ≤ a⁻¹, from inv_le_inv' h,
by rwa one_inv at this

@[to_additive neg_lt_neg]
lemma inv_lt_inv' (h : a < b) : b⁻¹ < a⁻¹ :=
have 1 < a⁻¹ * b, from mul_left_inv a ▸ mul_lt_mul_left' h (a⁻¹),
have 1 * b⁻¹ < a⁻¹ * b * b⁻¹, from mul_lt_mul_right' this (b⁻¹),
by rwa [mul_inv_cancel_right, one_mul] at this

@[to_additive]
lemma lt_of_inv_lt_inv (h : b⁻¹ < a⁻¹) : a < b :=
inv_inv a ▸ inv_inv b ▸ inv_lt_inv' h

@[to_additive]
lemma one_lt_of_inv_inv (h : a⁻¹ < 1) : 1 < a :=
have a⁻¹ < 1⁻¹, by rwa one_inv,
lt_of_inv_lt_inv this

@[to_additive]
lemma inv_inv_of_one_lt (h : 1 < a) : a⁻¹ < 1 :=
have a⁻¹ < 1⁻¹, from inv_lt_inv' h,
by rwa one_inv at this

@[to_additive neg_of_neg_pos]
lemma inv_of_one_lt_inv (h : 1 < a⁻¹) : a < 1 :=
have 1⁻¹ < a⁻¹, by rwa one_inv,
lt_of_inv_lt_inv this

@[to_additive neg_pos_of_neg]
lemma one_lt_inv_of_inv (h : a < 1) : 1 < a⁻¹ :=
have 1⁻¹ < a⁻¹, from inv_lt_inv' h,
by rwa one_inv at this

@[to_additive]
lemma le_inv_of_le_inv (h : a ≤ b⁻¹) : b ≤ a⁻¹ :=
begin
  have h := inv_le_inv' h,
  rwa inv_inv at h
end

@[to_additive]
lemma inv_le_of_inv_le (h : a⁻¹ ≤ b) : b⁻¹ ≤ a :=
begin
  have h := inv_le_inv' h,
  rwa inv_inv at h
end

@[to_additive]
lemma lt_inv_of_lt_inv (h : a < b⁻¹) : b < a⁻¹ :=
begin
  have h := inv_lt_inv' h,
  rwa inv_inv at h
end

@[to_additive]
lemma inv_lt_of_inv_lt (h : a⁻¹ < b) : b⁻¹ < a :=
begin
  have h := inv_lt_inv' h,
  rwa inv_inv at h
end

@[to_additive]
lemma mul_le_of_le_inv_mul (h : b ≤ a⁻¹ * c) : a * b ≤ c :=
begin
  have h := mul_le_mul_left' h a,
  rwa mul_inv_cancel_left at h
end

@[to_additive]
lemma le_inv_mul_of_mul_le (h : a * b ≤ c) : b ≤ a⁻¹ * c :=
begin
  have h := mul_le_mul_left' h a⁻¹,
  rwa inv_mul_cancel_left at h
end

@[to_additive]
lemma le_mul_of_inv_mul_le (h : b⁻¹ * a ≤ c) : a ≤ b * c :=
begin
  have h := mul_le_mul_left' h b,
  rwa mul_inv_cancel_left at h
end

@[to_additive]
lemma inv_mul_le_of_le_mul (h : a ≤ b * c) : b⁻¹ * a ≤ c :=
begin
  have h := mul_le_mul_left' h b⁻¹,
  rwa inv_mul_cancel_left at h
end

@[to_additive]
lemma le_mul_of_inv_mul_le_left (h : b⁻¹ * a ≤ c) : a ≤ b * c :=
le_mul_of_inv_mul_le h

@[to_additive]
lemma inv_mul_le_left_of_le_mul (h : a ≤ b * c) : b⁻¹ * a ≤ c :=
inv_mul_le_of_le_mul h

@[to_additive]
lemma le_mul_of_inv_mul_le_right (h : c⁻¹ * a ≤ b) : a ≤ b * c :=
by { rw mul_comm, exact le_mul_of_inv_mul_le h }

@[to_additive]
lemma inv_mul_le_right_of_le_mul (h : a ≤ b * c) : c⁻¹ * a ≤ b :=
by { rw mul_comm at h, apply inv_mul_le_left_of_le_mul h }

@[to_additive]
lemma mul_lt_of_lt_inv_mul (h : b < a⁻¹ * c) : a * b < c :=
begin
  have h := mul_lt_mul_left' h a,
  rwa mul_inv_cancel_left at h
end

@[to_additive]
lemma lt_inv_mul_of_mul_lt (h : a * b < c) : b < a⁻¹ * c :=
begin
  have h := mul_lt_mul_left' h (a⁻¹),
  rwa inv_mul_cancel_left at h
end

@[to_additive]
lemma lt_mul_of_inv_mul_lt (h : b⁻¹ * a < c) : a < b * c :=
begin
  have h := mul_lt_mul_left' h b,
  rwa mul_inv_cancel_left at h
end

@[to_additive]
lemma inv_mul_lt_of_lt_mul (h : a < b * c) : b⁻¹ * a < c :=
begin
  have h := mul_lt_mul_left' h (b⁻¹),
  rwa inv_mul_cancel_left at h
end

@[to_additive]
lemma lt_mul_of_inv_mul_lt_left (h : b⁻¹ * a < c) : a < b * c :=
lt_mul_of_inv_mul_lt h

@[to_additive]
lemma inv_mul_lt_left_of_lt_mul (h : a < b * c) : b⁻¹ * a < c :=
inv_mul_lt_of_lt_mul h

@[to_additive]
lemma lt_mul_of_inv_mul_lt_right (h : c⁻¹ * a < b) : a < b * c :=
by { rw mul_comm, exact lt_mul_of_inv_mul_lt h }

@[to_additive]
lemma inv_mul_lt_right_of_lt_mul (h : a < b * c) : c⁻¹ * a < b :=
by { rw mul_comm at h, exact inv_mul_lt_of_lt_mul h }

@[simp, to_additive]
lemma inv_lt_one_iff_one_lt : a⁻¹ < 1 ↔ 1 < a :=
⟨ one_lt_of_inv_inv, inv_inv_of_one_lt ⟩

@[simp, to_additive]
lemma inv_le_inv_iff : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
have a * b * a⁻¹ ≤ a * b * b⁻¹ ↔ a⁻¹ ≤ b⁻¹, from mul_le_mul_iff_left _,
by { rw [mul_inv_cancel_right, mul_comm a, mul_inv_cancel_right] at this, rw [this] }

@[to_additive neg_le]
lemma inv_le' : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
have a⁻¹ ≤ (b⁻¹)⁻¹ ↔ b⁻¹ ≤ a, from inv_le_inv_iff,
by rwa inv_inv at this

@[to_additive le_neg]
lemma le_inv' : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
have (a⁻¹)⁻¹ ≤ b⁻¹ ↔ b ≤ a⁻¹, from inv_le_inv_iff,
by rwa inv_inv at this

@[to_additive neg_le_iff_add_nonneg]
lemma inv_le_iff_one_le_mul : a⁻¹ ≤ b ↔ 1 ≤ a * b :=
(mul_le_mul_iff_left a).symm.trans $ by rw mul_inv_self

@[to_additive]
lemma le_inv_iff_mul_le_one : a ≤ b⁻¹ ↔ a * b ≤ 1 :=
(mul_le_mul_iff_right b).symm.trans $ by rw inv_mul_self

@[simp, to_additive neg_nonpos]
lemma inv_le_one' : a⁻¹ ≤ 1 ↔ 1 ≤ a :=
have a⁻¹ ≤ 1⁻¹ ↔ 1 ≤ a, from inv_le_inv_iff,
by rwa one_inv at this

@[simp, to_additive neg_nonneg]
lemma one_le_inv' : 1 ≤ a⁻¹ ↔ a ≤ 1 :=
have 1⁻¹ ≤ a⁻¹ ↔ a ≤ 1, from inv_le_inv_iff,
by rwa one_inv at this

@[to_additive]
lemma inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a :=
le_trans (inv_le_one'.2 h) h

@[to_additive]
lemma self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ :=
le_trans h (one_le_inv'.2 h)

@[simp, to_additive]
lemma inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a :=
have a * b * a⁻¹ < a * b * b⁻¹ ↔ a⁻¹ < b⁻¹, from mul_lt_mul_iff_left _,
by { rw [mul_inv_cancel_right, mul_comm a, mul_inv_cancel_right] at this, rw [this] }

@[to_additive neg_lt_zero]
lemma inv_lt_one' : a⁻¹ < 1 ↔ 1 < a :=
have a⁻¹ < 1⁻¹ ↔ 1 < a, from inv_lt_inv_iff,
by rwa one_inv at this

@[to_additive neg_pos]
lemma one_lt_inv' : 1 < a⁻¹ ↔ a < 1 :=
have 1⁻¹ < a⁻¹ ↔ a < 1, from inv_lt_inv_iff,
by rwa one_inv at this

@[to_additive neg_lt]
lemma inv_lt' : a⁻¹ < b ↔ b⁻¹ < a :=
have a⁻¹ < (b⁻¹)⁻¹ ↔ b⁻¹ < a, from inv_lt_inv_iff,
by rwa inv_inv at this

@[to_additive lt_neg]
lemma lt_inv' : a < b⁻¹ ↔ b < a⁻¹ :=
have (a⁻¹)⁻¹ < b⁻¹ ↔ b < a⁻¹, from inv_lt_inv_iff,
by rwa inv_inv at this

@[to_additive]
lemma le_inv_mul_iff_mul_le : b ≤ a⁻¹ * c ↔ a * b ≤ c :=
have a⁻¹ * (a * b) ≤ a⁻¹ * c ↔ a * b ≤ c, from mul_le_mul_iff_left _,
by rwa inv_mul_cancel_left at this

@[simp, to_additive]
lemma inv_mul_le_iff_le_mul : b⁻¹ * a ≤ c ↔ a ≤ b * c :=
have b⁻¹ * a ≤ b⁻¹ * (b * c) ↔ a ≤ b * c, from mul_le_mul_iff_left _,
by rwa inv_mul_cancel_left at this

@[to_additive]
lemma mul_inv_le_iff_le_mul : a * c⁻¹ ≤ b ↔ a ≤ b * c :=
by rw [mul_comm a, mul_comm b, inv_mul_le_iff_le_mul]

@[simp, to_additive]
lemma mul_inv_le_iff_le_mul' : a * b⁻¹ ≤ c ↔ a ≤ b * c :=
by rw [← inv_mul_le_iff_le_mul, mul_comm]

@[to_additive]
lemma inv_mul_le_iff_le_mul' : c⁻¹ * a ≤ b ↔ a ≤ b * c :=
by rw [inv_mul_le_iff_le_mul, mul_comm]

@[simp, to_additive]
lemma lt_inv_mul_iff_mul_lt : b < a⁻¹ * c ↔ a * b < c :=
have a⁻¹ * (a * b) < a⁻¹ * c ↔ a * b < c, from mul_lt_mul_iff_left _,
by rwa inv_mul_cancel_left at this

@[simp, to_additive]
lemma inv_mul_lt_iff_lt_mul : b⁻¹ * a < c ↔ a < b * c :=
have b⁻¹ * a < b⁻¹ * (b * c) ↔ a < b * c, from mul_lt_mul_iff_left _,
by rwa inv_mul_cancel_left at this

@[to_additive]
lemma inv_mul_lt_iff_lt_mul_right : c⁻¹ * a < b ↔ a < b * c :=
by rw [inv_mul_lt_iff_lt_mul, mul_comm]

@[to_additive sub_le_sub_iff]
lemma div_le_div_iff' (a b c d : α) : a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b :=
begin
  split ; intro h,
  have := mul_le_mul_right' (mul_le_mul_right' h b) d,
  rwa [inv_mul_cancel_right, mul_assoc _ _ b, mul_comm _ b, ← mul_assoc, inv_mul_cancel_right] at this,
  have := mul_le_mul_right' (mul_le_mul_right' h d⁻¹) b⁻¹,
  rwa [mul_inv_cancel_right, _root_.mul_assoc, _root_.mul_comm d⁻¹ b⁻¹, ← mul_assoc, mul_inv_cancel_right] at this,
end

end ordered_comm_group

section ordered_add_comm_group
variables [ordered_add_comm_group α] {a b c d : α}

lemma sub_nonneg_of_le (h : b ≤ a) : 0 ≤ a - b :=
begin
  have h := add_le_add_right h (-b),
  rwa add_right_neg at h
end

lemma le_of_sub_nonneg (h : 0 ≤ a - b) : b ≤ a :=
begin
  have h := add_le_add_right h b,
  rwa [sub_add_cancel, zero_add] at h
end

lemma sub_nonpos_of_le (h : a ≤ b) : a - b ≤ 0 :=
begin
  have h := add_le_add_right h (-b),
  rwa add_right_neg at h
end

lemma le_of_sub_nonpos (h : a - b ≤ 0) : a ≤ b :=
begin
  have h := add_le_add_right h b,
  rwa [sub_add_cancel, zero_add] at h
end

lemma sub_pos_of_lt (h : b < a) : 0 < a - b :=
begin
  have h := add_lt_add_right h (-b),
  rwa add_right_neg at h
end

lemma lt_of_sub_pos (h : 0 < a - b) : b < a :=
begin
  have h := add_lt_add_right h b,
  rwa [sub_add_cancel, zero_add] at h
end

lemma sub_neg_of_lt (h : a < b) : a - b < 0 :=
begin
  have h := add_lt_add_right h (-b),
  rwa add_right_neg at h
end

lemma lt_of_sub_neg (h : a - b < 0) : a < b :=
begin
  have h := add_lt_add_right h b,
  rwa [sub_add_cancel, zero_add] at h
end

lemma add_le_of_le_sub_left (h : b ≤ c - a) : a + b ≤ c :=
begin
  have h := add_le_add_left h a,
  rwa [← add_sub_assoc, add_comm a c, add_sub_cancel] at h
end

lemma le_sub_left_of_add_le (h : a + b ≤ c) : b ≤ c - a :=
begin
  have h := add_le_add_right h (-a),
  rwa [add_comm a b, add_neg_cancel_right] at h
end

lemma add_le_of_le_sub_right (h : a ≤ c - b) : a + b ≤ c :=
begin
  have h := add_le_add_right h b,
  rwa sub_add_cancel at h
end

lemma le_sub_right_of_add_le (h : a + b ≤ c) : a ≤ c - b :=
begin
  have h := add_le_add_right h (-b),
  rwa add_neg_cancel_right at h
end

lemma le_add_of_sub_left_le (h : a - b ≤ c) : a ≤ b + c :=
begin
  have h := add_le_add_right h b,
  rwa [sub_add_cancel, add_comm] at h
end

lemma sub_left_le_of_le_add (h : a ≤ b + c) : a - b ≤ c :=
begin
  have h := add_le_add_right h (-b),
  rwa [add_comm b c, add_neg_cancel_right] at h
end

lemma le_add_of_sub_right_le (h : a - c ≤ b) : a ≤ b + c :=
begin
  have h := add_le_add_right h c,
  rwa sub_add_cancel at h
end

lemma sub_right_le_of_le_add (h : a ≤ b + c) : a - c ≤ b :=
begin
  have h := add_le_add_right h (-c),
  rwa add_neg_cancel_right at h
end

lemma le_add_of_neg_le_sub_left (h : -a ≤ b - c) : c ≤ a + b :=
le_add_of_neg_add_le_left (add_le_of_le_sub_right h)

lemma neg_le_sub_left_of_le_add (h : c ≤ a + b) : -a ≤ b - c :=
begin
  have h := le_neg_add_of_add_le (sub_left_le_of_le_add h),
  rwa add_comm at h
end

lemma le_add_of_neg_le_sub_right (h : -b ≤ a - c) : c ≤ a + b :=
le_add_of_sub_right_le (add_le_of_le_sub_left h)

lemma neg_le_sub_right_of_le_add (h : c ≤ a + b) : -b ≤ a - c :=
le_sub_left_of_add_le (sub_right_le_of_le_add h)

lemma sub_le_of_sub_le (h : a - b ≤ c) : a - c ≤ b :=
sub_left_le_of_le_add (le_add_of_sub_right_le h)

lemma sub_le_sub_left (h : a ≤ b) (c : α) : c - b ≤ c - a :=
add_le_add_left (neg_le_neg h) c

lemma sub_le_sub_right (h : a ≤ b) (c : α) : a - c ≤ b - c :=
add_le_add_right h (-c)

lemma sub_le_sub (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
add_le_add hab (neg_le_neg hcd)

lemma add_lt_of_lt_sub_left (h : b < c - a) : a + b < c :=
begin
  have h := add_lt_add_left h a,
  rwa [← add_sub_assoc, add_comm a c, add_sub_cancel] at h
end

lemma lt_sub_left_of_add_lt (h : a + b < c) : b < c - a :=
begin
  have h := add_lt_add_right h (-a),
  rwa [add_comm a b, add_neg_cancel_right] at h
end

lemma add_lt_of_lt_sub_right (h : a < c - b) : a + b < c :=
begin
  have h := add_lt_add_right h b,
  rwa sub_add_cancel at h
end

lemma lt_sub_right_of_add_lt (h : a + b < c) : a < c - b :=
begin
  have h := add_lt_add_right h (-b),
  rwa add_neg_cancel_right at h
end

lemma lt_add_of_sub_left_lt (h : a - b < c) : a < b + c :=
begin
  have h := add_lt_add_right h b,
  rwa [sub_add_cancel, add_comm] at h
end

lemma sub_left_lt_of_lt_add (h : a < b + c) : a - b < c :=
begin
  have h := add_lt_add_right h (-b),
  rwa [add_comm b c, add_neg_cancel_right] at h
end

lemma lt_add_of_sub_right_lt (h : a - c < b) : a < b + c :=
begin
  have h := add_lt_add_right h c,
  rwa sub_add_cancel at h
end

lemma sub_right_lt_of_lt_add (h : a < b + c) : a - c < b :=
begin
  have h := add_lt_add_right h (-c),
  rwa add_neg_cancel_right at h
end

lemma lt_add_of_neg_lt_sub_left (h : -a < b - c) : c < a + b :=
lt_add_of_neg_add_lt_left (add_lt_of_lt_sub_right h)

lemma neg_lt_sub_left_of_lt_add (h : c < a + b) : -a < b - c :=
begin
  have h := lt_neg_add_of_add_lt (sub_left_lt_of_lt_add h),
  rwa add_comm at h
end

lemma lt_add_of_neg_lt_sub_right (h : -b < a - c) : c < a + b :=
lt_add_of_sub_right_lt (add_lt_of_lt_sub_left h)

lemma neg_lt_sub_right_of_lt_add (h : c < a + b) : -b < a - c :=
lt_sub_left_of_add_lt (sub_right_lt_of_lt_add h)

lemma sub_lt_of_sub_lt (h : a - b < c) : a - c < b :=
sub_left_lt_of_lt_add (lt_add_of_sub_right_lt h)

lemma sub_lt_sub_left (h : a < b) (c : α) : c - b < c - a :=
add_lt_add_left (neg_lt_neg h) c

lemma sub_lt_sub_right (h : a < b) (c : α) : a - c < b - c :=
add_lt_add_right h (-c)

lemma sub_lt_sub (hab : a < b) (hcd : c < d) : a - d < b - c :=
add_lt_add hab (neg_lt_neg hcd)

lemma sub_lt_sub_of_le_of_lt (hab : a ≤ b) (hcd : c < d) : a - d < b - c :=
add_lt_add_of_le_of_lt hab (neg_lt_neg hcd)

lemma sub_lt_sub_of_lt_of_le (hab : a < b) (hcd : c ≤ d) : a - d < b - c :=
add_lt_add_of_lt_of_le hab (neg_le_neg hcd)

lemma sub_le_self (a : α) {b : α} (h : 0 ≤ b) : a - b ≤ a :=
calc
  a - b = a + -b : rfl
    ... ≤ a + 0  : add_le_add_left (neg_nonpos_of_nonneg h) _
    ... = a      : by rw add_zero

lemma sub_lt_self (a : α) {b : α} (h : 0 < b) : a - b < a :=
calc
  a - b = a + -b : rfl
    ... < a + 0  : add_lt_add_left (neg_neg_of_pos h) _
    ... = a      : by rw add_zero

@[simp]
lemma sub_le_sub_iff_left (a : α) {b c : α} : a - b ≤ a - c ↔ c ≤ b :=
(add_le_add_iff_left _).trans neg_le_neg_iff

@[simp]
lemma sub_le_sub_iff_right (c : α) : a - c ≤ b - c ↔ a ≤ b :=
add_le_add_iff_right _

@[simp]
lemma sub_lt_sub_iff_left (a : α) {b c : α} : a - b < a - c ↔ c < b :=
(add_lt_add_iff_left _).trans neg_lt_neg_iff

@[simp]
lemma sub_lt_sub_iff_right (c : α) : a - c < b - c ↔ a < b :=
add_lt_add_iff_right _

@[simp] lemma sub_nonneg : 0 ≤ a - b ↔ b ≤ a :=
have a - a ≤ a - b ↔ b ≤ a, from sub_le_sub_iff_left a,
by rwa sub_self at this

@[simp] lemma sub_nonpos : a - b ≤ 0 ↔ a ≤ b :=
have a - b ≤ b - b ↔ a ≤ b, from sub_le_sub_iff_right b,
by rwa sub_self at this

@[simp] lemma sub_pos : 0 < a - b ↔ b < a :=
have a - a < a - b ↔ b < a, from sub_lt_sub_iff_left a,
by rwa sub_self at this

@[simp] lemma sub_lt_zero : a - b < 0 ↔ a < b :=
have a - b < b - b ↔ a < b, from sub_lt_sub_iff_right b,
by rwa sub_self at this

lemma le_sub_iff_add_le' : b ≤ c - a ↔ a + b ≤ c :=
by rw [sub_eq_add_neg, add_comm, le_neg_add_iff_add_le]

lemma le_sub_iff_add_le : a ≤ c - b ↔ a + b ≤ c :=
by rw [le_sub_iff_add_le', add_comm]

lemma sub_le_iff_le_add' : a - b ≤ c ↔ a ≤ b + c :=
by rw [sub_eq_add_neg, add_comm, neg_add_le_iff_le_add]

lemma sub_le_iff_le_add : a - c ≤ b ↔ a ≤ b + c :=
by rw [sub_le_iff_le_add', add_comm]

@[simp] lemma neg_le_sub_iff_le_add : -b ≤ a - c ↔ c ≤ a + b :=
le_sub_iff_add_le.trans neg_add_le_iff_le_add'

lemma neg_le_sub_iff_le_add' : -a ≤ b - c ↔ c ≤ a + b :=
by rw [neg_le_sub_iff_le_add, add_comm]

lemma sub_le : a - b ≤ c ↔ a - c ≤ b :=
sub_le_iff_le_add'.trans sub_le_iff_le_add.symm

theorem le_sub : a ≤ b - c ↔ c ≤ b - a :=
le_sub_iff_add_le'.trans le_sub_iff_add_le.symm

lemma lt_sub_iff_add_lt' : b < c - a ↔ a + b < c :=
by rw [sub_eq_add_neg, add_comm, lt_neg_add_iff_add_lt]

lemma lt_sub_iff_add_lt : a < c - b ↔ a + b < c :=
by rw [lt_sub_iff_add_lt', add_comm]

lemma sub_lt_iff_lt_add' : a - b < c ↔ a < b + c :=
by rw [sub_eq_add_neg, add_comm, neg_add_lt_iff_lt_add]

lemma sub_lt_iff_lt_add : a - c < b ↔ a < b + c :=
by rw [sub_lt_iff_lt_add', add_comm]

@[simp] lemma neg_lt_sub_iff_lt_add : -b < a - c ↔ c < a + b :=
lt_sub_iff_add_lt.trans neg_add_lt_iff_lt_add_right

lemma neg_lt_sub_iff_lt_add' : -a < b - c ↔ c < a + b :=
by rw [neg_lt_sub_iff_lt_add, add_comm]

lemma sub_lt : a - b < c ↔ a - c < b :=
sub_lt_iff_lt_add'.trans sub_lt_iff_lt_add.symm

theorem lt_sub : a < b - c ↔ c < b - a :=
lt_sub_iff_add_lt'.trans lt_sub_iff_add_lt.symm

lemma sub_le_self_iff (a : α) {b : α} : a - b ≤ a ↔ 0 ≤ b :=
sub_le_iff_le_add'.trans (le_add_iff_nonneg_left _)

lemma sub_lt_self_iff (a : α) {b : α} : a - b < a ↔ 0 < b :=
sub_lt_iff_lt_add'.trans (lt_add_iff_pos_left _)

end ordered_add_comm_group

/-
TODO:
The `add_lt_add_left` field of `ordered_add_comm_group` is redundant,
and it is no longer in core so we can remove it now.
This alternative constructor is a workaround until someone fixes this.
-/

/-- Alternative constructor for ordered commutative groups,
that avoids the field `mul_lt_mul_left`. -/
@[to_additive "Alternative constructor for ordered commutative groups,
that avoids the field `mul_lt_mul_left`."]
def ordered_comm_group.mk' {α : Type u} [comm_group α] [partial_order α]
  (mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b) :
  ordered_comm_group α :=
{ mul_le_mul_left := mul_le_mul_left,
  ..(by apply_instance : comm_group α),
  ..(by apply_instance : partial_order α) }

/-- A decidable linearly ordered cancellative additive commutative monoid
is an additive commutative monoid with a decidable linear order
in which addition is cancellative and strictly monotone. -/
@[protect_proj] class decidable_linear_ordered_cancel_add_comm_monoid (α : Type u)
  extends ordered_cancel_add_comm_monoid α, decidable_linear_order α

section decidable_linear_ordered_cancel_add_comm_monoid
variables [decidable_linear_ordered_cancel_add_comm_monoid α]

lemma min_add_add_left (a b c : α) : min (a + b) (a + c) = a + min b c :=
eq.symm (eq_min
  (show a + min b c ≤ a + b, from add_le_add_left (min_le_left _ _)  _)
  (show a + min b c ≤ a + c, from add_le_add_left (min_le_right _ _)  _)
  (assume d,
    assume : d ≤ a + b,
    assume : d ≤ a + c,
    decidable.by_cases
      (assume : b ≤ c, by rwa [min_eq_left this])
      (assume : ¬ b ≤ c, by rwa [min_eq_right (le_of_lt (lt_of_not_ge this))])))

lemma min_add_add_right (a b c : α) : min (a + c) (b + c) = min a b + c :=
begin rw [add_comm a c, add_comm b c, add_comm _ c], apply min_add_add_left end

lemma max_add_add_left (a b c : α) : max (a + b) (a + c) = a + max b c :=
eq.symm (eq_max
  (add_le_add_left (le_max_left _ _)  _)
  (add_le_add_left (le_max_right _ _) _)
  (assume d,
    assume : a + b ≤ d,
    assume : a + c ≤ d,
    decidable.by_cases
      (assume : b ≤ c, by rwa [max_eq_right this])
      (assume : ¬ b ≤ c, by rwa [max_eq_left (le_of_lt (lt_of_not_ge this))])))

lemma max_add_add_right (a b c : α) : max (a + c) (b + c) = max a b + c :=
begin rw [add_comm a c, add_comm b c, add_comm _ c], apply max_add_add_left end

end decidable_linear_ordered_cancel_add_comm_monoid

/-- A decidable linearly ordered additive commutative group is an
additive commutative group with a decidable linear order in which
addition is strictly monotone. -/
@[protect_proj] class decidable_linear_ordered_add_comm_group (α : Type u)
  extends add_comm_group α, decidable_linear_order α :=
(add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)

instance decidable_linear_ordered_comm_group.to_ordered_add_comm_group (α : Type u)
  [s : decidable_linear_ordered_add_comm_group α] : ordered_add_comm_group α :=
{ add := s.add, ..s }

section decidable_linear_ordered_add_comm_group
variables [decidable_linear_ordered_add_comm_group α]

@[priority 100] -- see Note [lower instance priority]
instance decidable_linear_ordered_add_comm_group.to_decidable_linear_ordered_cancel_add_comm_monoid :
  decidable_linear_ordered_cancel_add_comm_monoid α :=
{ le_of_add_le_add_left := λ x y z, le_of_add_le_add_left,
  add_left_cancel := λ x y z, add_left_cancel,
  add_right_cancel := λ x y z, add_right_cancel,
  ..‹decidable_linear_ordered_add_comm_group α› }

lemma decidable_linear_ordered_add_comm_group.add_lt_add_left
  (a b : α) (h : a < b) (c : α) : c + a < c + b :=
ordered_add_comm_group.add_lt_add_left a b h c

lemma max_neg_neg (a b : α) : max (-a) (-b) = - min a b  :=
eq.symm (eq_max
  (show -a ≤ -(min a b), from neg_le_neg $ min_le_left a b)
  (show -b ≤ -(min a b), from neg_le_neg $ min_le_right a b)
  (assume d,
    assume H₁ : -a ≤ d,
    assume H₂ : -b ≤ d,
    have H : -d ≤ min a b,
      from le_min (neg_le_of_neg_le  H₁) (neg_le_of_neg_le H₂),
    show -(min a b) ≤ d, from neg_le_of_neg_le H))

lemma min_eq_neg_max_neg_neg (a b : α) : min a b = - max (-a) (-b) :=
by rw [max_neg_neg, neg_neg]

lemma min_neg_neg (a b : α) : min (-a) (-b) = - max a b :=
by rw [min_eq_neg_max_neg_neg, neg_neg, neg_neg]

lemma max_eq_neg_min_neg_neg (a b : α) : max a b = - min (-a) (-b) :=
by rw [min_neg_neg, neg_neg]

/-- `abs a` is the absolute value of `a`. -/
def abs (a : α) : α := max a (-a)

lemma abs_of_nonneg {a : α} (h : 0 ≤ a) : abs a = a :=
have h' : -a ≤ a, from le_trans (neg_nonpos_of_nonneg h) h,
max_eq_left h'

lemma abs_of_pos {a : α} (h : 0 < a) : abs a = a :=
abs_of_nonneg (le_of_lt h)

lemma abs_of_nonpos {a : α} (h : a ≤ 0) : abs a = -a :=
have h' : a ≤ -a, from le_trans h (neg_nonneg_of_nonpos h),
max_eq_right h'

lemma abs_of_neg {a : α} (h : a < 0) : abs a = -a :=
abs_of_nonpos (le_of_lt h)

lemma abs_zero : abs 0 = (0:α) :=
abs_of_nonneg (le_refl _)

lemma abs_neg (a : α) : abs (-a) = abs a :=
begin unfold abs, rw [max_comm, neg_neg] end

lemma abs_pos_of_pos {a : α} (h : 0 < a) : 0 < abs a :=
by rwa (abs_of_pos h)

lemma abs_pos_of_neg {a : α} (h : a < 0) : 0 < abs a :=
abs_neg a ▸ abs_pos_of_pos (neg_pos_of_neg h)

lemma abs_sub (a b : α) : abs (a - b) = abs (b - a) :=
by rw [← neg_sub, abs_neg]

lemma ne_zero_of_abs_ne_zero {a : α} (h : abs a ≠ 0) : a ≠ 0 :=
assume ha, h (eq.symm ha ▸ abs_zero)

/- these assume a linear order -/

lemma eq_zero_of_neg_eq {a : α} (h : -a = a) : a = 0 :=
match lt_trichotomy a 0 with
| or.inl h₁ :=
  have 0 < a, from h ▸ neg_pos_of_neg h₁,
  absurd h₁ (lt_asymm this)
| or.inr (or.inl h₁) := h₁
| or.inr (or.inr h₁) :=
  have a < 0, from h ▸ neg_neg_of_pos h₁,
  absurd h₁ (lt_asymm this)
end

lemma abs_nonneg (a : α) : 0 ≤ abs a :=
or.elim (le_total 0 a)
  (assume h : 0 ≤ a, by rwa (abs_of_nonneg h))
  (assume h : a ≤ 0, calc
       0 ≤ -a    : neg_nonneg_of_nonpos h
     ... = abs a : eq.symm (abs_of_nonpos h))

lemma abs_abs (a : α) : abs (abs a) = abs a :=
abs_of_nonneg $ abs_nonneg a

lemma le_abs_self (a : α) : a ≤ abs a :=
or.elim (le_total 0 a)
  (assume h : 0 ≤ a,
   begin rw [abs_of_nonneg h] end)
  (assume h : a ≤ 0, le_trans h $ abs_nonneg a)

lemma neg_le_abs_self (a : α) : -a ≤ abs a :=
abs_neg a ▸ le_abs_self (-a)

lemma eq_zero_of_abs_eq_zero {a : α} (h : abs a = 0) : a = 0 :=
have h₁ : a ≤ 0, from h ▸ le_abs_self a,
have h₂ : -a ≤ 0, from h ▸ abs_neg a ▸ le_abs_self (-a),
le_antisymm h₁ (nonneg_of_neg_nonpos h₂)

lemma eq_of_abs_sub_eq_zero {a b : α} (h : abs (a - b) = 0) : a = b :=
have a - b = 0, from eq_zero_of_abs_eq_zero h,
show a = b, from eq_of_sub_eq_zero this

lemma abs_pos_of_ne_zero {a : α} (h : a ≠ 0) : 0 < abs a :=
or.elim (lt_or_gt_of_ne h) abs_pos_of_neg abs_pos_of_pos

lemma abs_by_cases (P : α → Prop) {a : α} (h1 : P a) (h2 : P (-a)) : P (abs a) :=
or.elim (le_total 0 a)
  (assume h : 0 ≤ a, eq.symm (abs_of_nonneg h) ▸ h1)
  (assume h : a ≤ 0, eq.symm (abs_of_nonpos h) ▸ h2)

lemma abs_le_of_le_of_neg_le {a b : α} (h1 : a ≤ b) (h2 : -a ≤ b) : abs a ≤ b :=
abs_by_cases (λ x : α, x ≤ b) h1 h2

lemma abs_lt_of_lt_of_neg_lt {a b : α} (h1 : a < b) (h2 : -a < b) : abs a < b :=
abs_by_cases (λ x : α, x < b) h1 h2

private lemma aux1 {a b : α} (h1 : 0 ≤ a + b) (h2 : 0 ≤ a) : abs (a + b) ≤ abs a + abs b :=
decidable.by_cases
  (assume h3 : 0 ≤ b, calc
    abs (a + b) ≤ abs (a + b)   : by apply le_refl
            ... = a + b         : by rw (abs_of_nonneg h1)
            ... = abs a + b     : by rw (abs_of_nonneg h2)
            ... = abs a + abs b : by rw (abs_of_nonneg h3))
 (assume h3 : ¬ 0 ≤ b,
  have h4 : b ≤ 0, from le_of_lt (lt_of_not_ge h3),
  calc
    abs (a + b) = a + b         : by rw (abs_of_nonneg h1)
            ... = abs a + b     : by rw (abs_of_nonneg h2)
            ... ≤ abs a + 0     : add_le_add_left h4 _
            ... ≤ abs a + -b    : add_le_add_left (neg_nonneg_of_nonpos h4) _
            ... = abs a + abs b : by rw (abs_of_nonpos h4))

private lemma aux2 {a b : α} (h1 : 0 ≤ a + b) : abs (a + b) ≤ abs a + abs b :=
or.elim (le_total b 0)
 (assume h2 : b ≤ 0,
  have h3 : ¬ a < 0, from
    assume h4 : a < 0,
    have h5 : a + b < 0,
      begin
        have aux := add_lt_add_of_lt_of_le h4 h2,
        rwa [add_zero] at aux
      end,
    not_lt_of_ge h1 h5,
  aux1 h1 (le_of_not_gt h3))
 (assume h2 : 0 ≤ b,
  begin
    have h3 : abs (b + a) ≤ abs b + abs a,
    begin
      rw add_comm at h1,
      exact aux1 h1 h2
    end,
    rw [add_comm, add_comm (abs a)],
    exact h3
  end)

lemma abs_add_le_abs_add_abs (a b : α) : abs (a + b) ≤ abs a + abs b :=
or.elim (le_total 0 (a + b))
  (assume h2 : 0 ≤ a + b, aux2 h2)
  (assume h2 : a + b ≤ 0,
   have h3 : -a + -b = -(a + b), by rw neg_add,
   have h4 : 0 ≤ -(a + b), from neg_nonneg_of_nonpos h2,
   have h5   : 0 ≤ -a + -b, begin rw [← h3] at h4, exact h4 end,
   calc
      abs (a + b) = abs (-a + -b)   : by rw [← abs_neg, neg_add]
              ... ≤ abs (-a) + abs (-b) : aux2 h5
              ... = abs a + abs b       : by rw [abs_neg, abs_neg])

lemma abs_sub_abs_le_abs_sub (a b : α) : abs a - abs b ≤ abs (a - b) :=
have h1 : abs a - abs b + abs b ≤ abs (a - b) + abs b, from
calc
   abs a - abs b + abs b = abs a                 : by rw sub_add_cancel
                     ... = abs (a - b + b)       : by rw sub_add_cancel
                     ... ≤ abs (a - b) + abs b   : by apply abs_add_le_abs_add_abs,
le_of_add_le_add_right h1

lemma abs_sub_le (a b c : α) : abs (a - c) ≤ abs (a - b) + abs (b - c) :=
calc
    abs (a - c) = abs (a - b + (b - c))     : by rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg,
                                                    add_assoc, neg_add_cancel_left]
            ... ≤ abs (a - b) + abs (b - c) : by apply abs_add_le_abs_add_abs

lemma abs_add_three (a b c : α) : abs (a + b + c) ≤ abs a + abs b + abs c :=
begin
  apply le_trans,
  apply abs_add_le_abs_add_abs,
  apply le_trans,
  apply add_le_add_right,
  apply abs_add_le_abs_add_abs,
  apply le_refl
end

lemma dist_bdd_within_interval {a b lb ub : α} (hal : lb ≤ a) (hau : a ≤ ub)
      (hbl : lb ≤ b) (hbu : b ≤ ub) : abs (a - b) ≤ ub - lb :=
begin
  cases (decidable.em (b ≤ a)) with hba hba,
  rw (abs_of_nonneg (sub_nonneg_of_le hba)),
  apply sub_le_sub,
  apply hau,
  apply hbl,
  rw [abs_of_neg (sub_neg_of_lt (lt_of_not_ge hba)), neg_sub],
  apply sub_le_sub,
  apply hbu,
  apply hal
end

lemma decidable_linear_ordered_add_comm_group.eq_of_abs_sub_nonpos
  {a b : α} (h : abs (a - b) ≤ 0) : a = b :=
eq_of_abs_sub_eq_zero (le_antisymm h (abs_nonneg (a - b)))

end decidable_linear_ordered_add_comm_group

set_option old_structure_cmd true
section prio
set_option default_priority 100 -- see Note [default priority]
/-- This is not so much a new structure as a construction mechanism
  for ordered groups, by specifying only the "positive cone" of the group. -/
class nonneg_add_comm_group (α : Type*) extends add_comm_group α :=
(nonneg : α → Prop)
(pos : α → Prop := λ a, nonneg a ∧ ¬ nonneg (neg a))
(pos_iff : ∀ a, pos a ↔ nonneg a ∧ ¬ nonneg (-a) . order_laws_tac)
(zero_nonneg : nonneg 0)
(add_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a + b))
(nonneg_antisymm : ∀ {a}, nonneg a → nonneg (-a) → a = 0)
end prio

namespace nonneg_add_comm_group
variable [s : nonneg_add_comm_group α]
include s

@[reducible, priority 100] -- see Note [lower instance priority]
instance to_ordered_add_comm_group : ordered_add_comm_group α :=
{ le := λ a b, nonneg (b - a),
  lt := λ a b, pos (b - a),
  lt_iff_le_not_le := λ a b, by simp; rw [pos_iff]; simp,
  le_refl := λ a, by simp [zero_nonneg],
  le_trans := λ a b c nab nbc, by simp [-sub_eq_add_neg];
    rw ← sub_add_sub_cancel; exact add_nonneg nbc nab,
  le_antisymm := λ a b nab nba, eq_of_sub_eq_zero $
    nonneg_antisymm nba (by rw neg_sub; exact nab),
  add_le_add_left := λ a b nab c, by simpa [(≤), preorder.le] using nab,
  ..s }

theorem nonneg_def {a : α} : nonneg a ↔ 0 ≤ a :=
show _ ↔ nonneg _, by simp

theorem pos_def {a : α} : pos a ↔ 0 < a :=
show _ ↔ pos _, by simp

theorem not_zero_pos : ¬ pos (0 : α) :=
mt pos_def.1 (lt_irrefl _)

theorem zero_lt_iff_nonneg_nonneg {a : α} :
  0 < a ↔ nonneg a ∧ ¬ nonneg (-a) :=
pos_def.symm.trans (pos_iff _)

theorem nonneg_total_iff :
  (∀ a : α, nonneg a ∨ nonneg (-a)) ↔
  (∀ a b : α, a ≤ b ∨ b ≤ a) :=
⟨λ h a b, by have := h (b - a); rwa [neg_sub] at this,
 λ h a, by rw [nonneg_def, nonneg_def, neg_nonneg]; apply h⟩

/--
A `nonneg_add_comm_group` is a `decidable_linear_ordered_add_comm_group`
if `nonneg` is total and decidable.
-/
def to_decidable_linear_ordered_add_comm_group
  [decidable_pred (@nonneg α _)]
  (nonneg_total : ∀ a : α, nonneg a ∨ nonneg (-a))
  : decidable_linear_ordered_add_comm_group α :=
{ le := (≤),
  lt := (<),
  lt_iff_le_not_le := @lt_iff_le_not_le _ _,
  le_refl := @le_refl _ _,
  le_trans := @le_trans _ _,
  le_antisymm := @le_antisymm _ _,
  le_total := nonneg_total_iff.1 nonneg_total,
  decidable_le := by apply_instance,
  decidable_lt := by apply_instance,
  ..@nonneg_add_comm_group.to_ordered_add_comm_group _ s }

end nonneg_add_comm_group

namespace order_dual

instance [ordered_add_comm_monoid α] : ordered_add_comm_monoid (order_dual α) :=
{ add_le_add_left := λ a b h c, @add_le_add_left α _ b a h _,
  lt_of_add_lt_add_left := λ a b c h, @lt_of_add_lt_add_left α _ a c b h,
  ..order_dual.partial_order α,
  ..show add_comm_monoid α, by apply_instance }

instance [ordered_cancel_add_comm_monoid α] : ordered_cancel_add_comm_monoid (order_dual α) :=
{ le_of_add_le_add_left := λ a b c : α, le_of_add_le_add_left,
  add_left_cancel := @add_left_cancel α _,
  add_right_cancel := @add_right_cancel α _,
  ..order_dual.ordered_add_comm_monoid }

instance [ordered_add_comm_group α] : ordered_add_comm_group (order_dual α) :=
{ add_left_neg := λ a : α, add_left_neg a,
  ..order_dual.ordered_add_comm_monoid,
  ..show add_comm_group α, by apply_instance }

end order_dual

section type_tags

instance : Π [preorder α], preorder (multiplicative α) := id
instance : Π [preorder α], preorder (additive α) := id
instance : Π [partial_order α], partial_order (multiplicative α) := id
instance : Π [partial_order α], partial_order (additive α) := id
instance : Π [linear_order α], linear_order (multiplicative α) := id
instance : Π [linear_order α], linear_order (additive α) := id
instance : Π [decidable_linear_order α], decidable_linear_order (multiplicative α) := id
instance : Π [decidable_linear_order α], decidable_linear_order (additive α) := id

instance [ordered_add_comm_monoid α] : ordered_comm_monoid (multiplicative α) :=
{ mul_le_mul_left := @ordered_add_comm_monoid.add_le_add_left α _,
  lt_of_mul_lt_mul_left := @ordered_add_comm_monoid.lt_of_add_lt_add_left α _,
  ..multiplicative.partial_order,
  ..multiplicative.comm_monoid }

instance [ordered_comm_monoid α] : ordered_add_comm_monoid (additive α) :=
{ add_le_add_left := @ordered_comm_monoid.mul_le_mul_left α _,
  lt_of_add_lt_add_left := @ordered_comm_monoid.lt_of_mul_lt_mul_left α _,
  ..additive.partial_order,
  ..additive.add_comm_monoid }

instance [ordered_cancel_add_comm_monoid α] : ordered_cancel_comm_monoid (multiplicative α) :=
{ le_of_mul_le_mul_left := @ordered_cancel_add_comm_monoid.le_of_add_le_add_left α _,
  ..multiplicative.right_cancel_semigroup,
  ..multiplicative.left_cancel_semigroup,
  ..multiplicative.ordered_comm_monoid }

instance [ordered_cancel_comm_monoid α] : ordered_cancel_add_comm_monoid (additive α) :=
{ le_of_add_le_add_left := @ordered_cancel_comm_monoid.le_of_mul_le_mul_left α _,
  ..additive.add_right_cancel_semigroup,
  ..additive.add_left_cancel_semigroup,
  ..additive.ordered_add_comm_monoid }

instance [ordered_add_comm_group α] : ordered_comm_group (multiplicative α) :=
{ ..multiplicative.comm_group,
  ..multiplicative.ordered_comm_monoid }

instance [ordered_comm_group α] : ordered_add_comm_group (additive α) :=
{ ..additive.add_comm_group,
  ..additive.ordered_add_comm_monoid }

end type_tags

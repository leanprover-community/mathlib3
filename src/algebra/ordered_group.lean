/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.group.with_one
import algebra.group.type_tags
import algebra.order_functions
import order.bounded_lattice

set_option old_structure_cmd true

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

attribute [to_additive] ordered_comm_monoid

section ordered_comm_monoid
variables [ordered_comm_monoid α] {a b c d : α}

@[to_additive add_le_add_left]
lemma mul_le_mul_left' (h : a ≤ b) (c) : c * a ≤ c * b :=
ordered_comm_monoid.mul_le_mul_left a b h c

@[to_additive add_le_add_right]
lemma mul_le_mul_right' (h : a ≤ b) (c) : a * c ≤ b * c :=
by { convert mul_le_mul_left' h c using 1; rw mul_comm }

@[to_additive lt_of_add_lt_add_left]
lemma lt_of_mul_lt_mul_left' : a * b < a * c → b < c :=
ordered_comm_monoid.lt_of_mul_lt_mul_left a b c

@[to_additive add_le_add]
lemma mul_le_mul' (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
(mul_le_mul_right' h₁ _).trans $ mul_le_mul_left' h₂ _

@[to_additive]
lemma mul_le_mul_three {e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) : a * b * c ≤ d * e * f :=
mul_le_mul' (mul_le_mul' h₁ h₂) h₃

@[to_additive le_add_of_nonneg_right]
lemma le_mul_of_one_le_right' (h : 1 ≤ b) : a ≤ a * b :=
have a * 1 ≤ a * b, from mul_le_mul_left' h _,
by rwa mul_one at this

@[to_additive le_add_of_nonneg_left]
lemma le_mul_of_one_le_left' (h : 1 ≤ b) : a ≤ b * a :=
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
lt_of_lt_of_le ha $ le_mul_of_one_le_right' hb

@[to_additive add_pos_of_nonneg_of_pos]
lemma one_lt_mul_of_le_of_lt' (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
lt_of_lt_of_le hb $ le_mul_of_one_le_left' ha

@[to_additive add_pos]
lemma one_lt_mul' (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
one_lt_mul_of_lt_of_le' ha hb.le

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
(mul_le_of_le_of_le_one' le_rfl hb).trans_lt ha

@[to_additive]
lemma mul_lt_one_of_le_one_of_lt_one' (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
(mul_le_of_le_one_of_le' ha le_rfl).trans_lt hb

@[to_additive]
lemma mul_lt_one' (ha : a < 1) (hb : b < 1) : a * b < 1 :=
mul_lt_one_of_le_one_of_lt_one' ha.le hb

@[to_additive]
lemma lt_mul_of_one_le_of_lt' (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
hbc.trans_le $ le_mul_of_one_le_left' ha

@[to_additive]
lemma lt_mul_of_lt_of_one_le' (hbc : b < c) (ha : 1 ≤ a) : b < c * a :=
hbc.trans_le $ le_mul_of_one_le_right' ha

@[to_additive]
lemma lt_mul_of_one_lt_of_lt' (ha : 1 < a) (hbc : b < c) : b < a * c :=
lt_mul_of_one_le_of_lt' ha.le hbc

@[to_additive]
lemma lt_mul_of_lt_of_one_lt' (hbc : b < c) (ha : 1 < a) : b < c * a :=
lt_mul_of_lt_of_one_le' hbc ha.le

@[to_additive]
lemma mul_lt_of_le_one_of_lt' (ha : a ≤ 1) (hbc : b < c) : a * b < c :=
lt_of_le_of_lt (mul_le_of_le_one_of_le' ha le_rfl) hbc

@[to_additive]
lemma mul_lt_of_lt_of_le_one' (hbc : b < c) (ha : a ≤ 1)  : b * a < c :=
lt_of_le_of_lt (mul_le_of_le_of_le_one' le_rfl ha) hbc

@[to_additive]
lemma mul_lt_of_lt_one_of_lt' (ha : a < 1) (hbc : b < c) : a * b < c :=
mul_lt_of_le_one_of_lt' ha.le hbc

@[to_additive]
lemma mul_lt_of_lt_of_lt_one' (hbc : b < c) (ha : a < 1) : b * a < c :=
mul_lt_of_lt_of_le_one' hbc ha.le

@[to_additive]
lemma mul_eq_one_iff' (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b = 1 ↔ a = 1 ∧ b = 1 :=
iff.intro
  (assume hab : a * b = 1,
   have a ≤ 1, from hab ▸ le_mul_of_le_of_one_le le_rfl hb,
   have a = 1, from le_antisymm this ha,
   have b ≤ 1, from hab ▸ le_mul_of_one_le_of_le ha le_rfl,
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
by by_cases b ≤ a; simp [max, h]

@[simp, to_additive, norm_cast]
theorem min_coe [monoid α] [decidable_linear_order α] {a b : units α} :
  (↑(min a b) : α) = min a b :=
by by_cases a ≤ b; simp [min, h]

end units

namespace with_zero

local attribute [semireducible] with_zero

instance [preorder α] : preorder (with_zero α) := with_bot.preorder

instance [partial_order α] : partial_order (with_zero α) := with_bot.partial_order

instance [partial_order α] : order_bot (with_zero α) := with_bot.order_bot

lemma zero_le [partial_order α] (a : with_zero α) : 0 ≤ a := order_bot.bot_le a

lemma zero_lt_coe [partial_order α] (a : α) : (0 : with_zero α) < a := with_bot.bot_lt_coe a

@[simp, norm_cast] lemma coe_lt_coe [partial_order α] {a b : α} : (a : with_zero α) < b ↔ a < b :=
with_bot.coe_lt_coe

@[simp, norm_cast] lemma coe_le_coe [partial_order α] {a b : α} : (a : with_zero α) ≤ b ↔ a ≤ b :=
with_bot.coe_le_coe

instance [lattice α] : lattice (with_zero α) := with_bot.lattice

instance [linear_order α] : linear_order (with_zero α) := with_bot.linear_order

instance [decidable_linear_order α] :
 decidable_linear_order (with_zero α) := with_bot.decidable_linear_order

lemma mul_le_mul_left {α : Type u}
  [ordered_comm_monoid α] :
  ∀ (a b : with_zero α),
    a ≤ b → ∀ (c : with_zero α), c * a ≤ c * b :=
begin
  rintro (_ | a) (_ | b) h (_ | c),
  { apply with_zero.zero_le },
  { apply with_zero.zero_le },
  { apply with_zero.zero_le },
  { apply with_zero.zero_le },
  { apply with_zero.zero_le },
  { exact false.elim (not_lt_of_le h (with_zero.zero_lt_coe a))},
  { apply with_zero.zero_le },
  { simp_rw [some_eq_coe] at h ⊢,
    norm_cast at h ⊢,
    exact mul_le_mul_left' h c }
end

lemma lt_of_mul_lt_mul_left  {α : Type u}
  [ordered_comm_monoid α] :
  ∀ (a b c : with_zero α), a * b < a * c → b < c :=
begin
  rintro (_ | a) (_ | b) (_ | c) h,
  { exact false.elim (lt_irrefl none h) },
  { exact false.elim (lt_irrefl none h) },
  { exact false.elim (lt_irrefl none h) },
  { exact false.elim (lt_irrefl none h) },
  { exact false.elim (lt_irrefl none h) },
  { exact with_zero.zero_lt_coe c },
  { exact false.elim (not_le_of_lt h (with_zero.zero_le _)) },
  { simp_rw [some_eq_coe] at h ⊢,
    norm_cast at h ⊢,
    apply lt_of_mul_lt_mul_left' h }
end

instance [ordered_comm_monoid α] : ordered_comm_monoid (with_zero α) :=
{ mul_le_mul_left := with_zero.mul_le_mul_left,
  lt_of_mul_lt_mul_left := with_zero.lt_of_mul_lt_mul_left,
  ..with_zero.comm_monoid_with_zero,
  ..with_zero.partial_order
}

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

local attribute [reducible] with_zero

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

/-- Coercion from `α` to `with_top α` as an `add_monoid_hom`. -/
def coe_add_hom [add_monoid α] : α →+ with_top α :=
⟨coe, rfl, λ _ _, rfl⟩

@[simp] lemma coe_coe_add_hom [add_monoid α] : ⇑(coe_add_hom : α →+ with_top α) = coe := rfl

@[simp] lemma zero_lt_top [ordered_add_comm_monoid α] : (0 : with_top α) < ⊤ :=
coe_lt_top 0

@[simp, norm_cast] lemma zero_lt_coe [ordered_add_comm_monoid α] (a : α) :
  (0 : with_top α) < a ↔ 0 < a :=
coe_lt_coe

@[simp] lemma add_top [ordered_add_comm_monoid α] : ∀{a : with_top α}, a + ⊤ = ⊤
| none := rfl
| (some a) := rfl

@[simp] lemma top_add [ordered_add_comm_monoid α] {a : with_top α} : ⊤ + a = ⊤ := rfl

lemma add_eq_top [ordered_add_comm_monoid α] (a b : with_top α) : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
by {cases a; cases b; simp [none_eq_top, some_eq_coe, ←with_top.coe_add, ←with_zero.coe_add]}

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

/-- A canonically ordered additive monoid is an ordered commutative additive monoid
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

lemma exists_pos_add_of_lt (h : a < b) : ∃ c > 0, a + c = b :=
begin
  obtain ⟨c, hc⟩ := le_iff_exists_add.1 h.le,
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

local attribute [semireducible] with_zero

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

/-- A canonically linear-ordered additive monoid is a canonically ordered additive monoid
    whose ordering is a decidable linear order. -/
@[protect_proj]
class canonically_linear_ordered_add_monoid (α : Type*)
      extends canonically_ordered_add_monoid α, decidable_linear_order α

section canonically_linear_ordered_add_monoid
variables [canonically_linear_ordered_add_monoid α]

@[priority 100]  -- see Note [lower instance priority]
instance canonically_linear_ordered_add_monoid.semilattice_sup_bot : semilattice_sup_bot α :=
{ ..lattice_of_decidable_linear_order, ..canonically_ordered_add_monoid.to_order_bot α }

end canonically_linear_ordered_add_monoid

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

attribute [to_additive] ordered_cancel_comm_monoid

section ordered_cancel_comm_monoid
variables [ordered_cancel_comm_monoid α] {a b c d : α}

@[priority 100, to_additive]    -- see Note [lower instance priority]
instance ordered_cancel_comm_monoid.to_left_cancel_monoid :
  left_cancel_monoid α := { ..‹ordered_cancel_comm_monoid α› }

@[to_additive le_of_add_le_add_left]
lemma le_of_mul_le_mul_left' : ∀ {a b c : α}, a * b ≤ a * c → b ≤ c :=
ordered_cancel_comm_monoid.le_of_mul_le_mul_left

@[priority 100, to_additive]    -- see Note [lower instance priority]
instance ordered_cancel_comm_monoid.to_ordered_comm_monoid : ordered_comm_monoid α :=
{ lt_of_mul_lt_mul_left := λ a b c h, lt_of_le_not_le (le_of_mul_le_mul_left' h.le) $
      mt (λ h, ordered_cancel_comm_monoid.mul_le_mul_left _ _ h _) (not_le_of_gt h),
  ..‹ordered_cancel_comm_monoid α› }

@[to_additive add_lt_add_left]
lemma mul_lt_mul_left' (h : a < b) (c : α) : c * a < c * b :=
lt_of_le_not_le (mul_le_mul_left' h.le _) $
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

@[to_additive lt_add_of_pos_right]
lemma lt_mul_of_one_lt_right' (a : α) {b : α} (h : 1 < b) : a < a * b :=
have a * 1 < a * b, from mul_lt_mul_left' h a,
by rwa [mul_one] at this

@[to_additive lt_add_of_pos_left]
lemma lt_mul_of_one_lt_left' (a : α) {b : α} (h : 1 < b) : a < b * a :=
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

lemma with_bot.add_lt_add_iff_left :
  ∀{a b c : with_bot α}, ⊥ < a → (a + c < a + b ↔ c < b)
| none := assume b c h, (lt_irrefl ⊥ h).elim
| (some a) :=
  begin
    assume b c h,
    cases b; cases c;
      simp [with_bot.none_eq_bot, with_bot.some_eq_coe, with_bot.bot_lt_coe, with_bot.coe_lt_coe],
    { norm_cast, exact with_bot.bot_lt_coe _ },
    { norm_cast, exact add_lt_add_iff_left _ }
  end

local attribute [reducible] with_zero

lemma with_top.add_lt_add_iff_right
  {a b c : with_top α} : a < ⊤ → (c + a < b + a ↔ c < b) :=
by simpa [add_comm] using @with_top.add_lt_add_iff_left _ _ a b c

lemma with_bot.add_lt_add_iff_right
  {a b c : with_bot α} : ⊥ < a → (c + a < b + a ↔ c < b) :=
by simpa [add_comm] using @with_bot.add_lt_add_iff_left _ _ a b c

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

attribute [to_additive] ordered_comm_group

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

@[priority 100, to_additive]    -- see Note [lower instance priority]
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

@[to_additive add_neg_le_add_neg_iff]
lemma div_le_div_iff' : a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b :=
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

lemma sub_le_sub_iff : a - b ≤ c - d ↔ a + d ≤ c + b := add_neg_le_add_neg_iff

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

/-! Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/
@[to_additive]
lemma fn_min_mul_fn_max {β} [decidable_linear_order α] [comm_semigroup β] (f : α → β) (n m : α) :
  f (min n m) * f (max n m) = f n * f m :=
by { cases le_total n m with h h; simp [h, mul_comm] }

@[to_additive]
lemma min_mul_max [decidable_linear_order α] [comm_semigroup α] (n m : α) :
  min n m * max n m = n * m :=
fn_min_mul_fn_max id n m

section decidable_linear_ordered_cancel_add_comm_monoid
variables [decidable_linear_ordered_cancel_add_comm_monoid α]

lemma min_add_add_left (a b c : α) : min (a + b) (a + c) = a + min b c :=
(monotone_id.const_add a).map_min.symm

lemma min_add_add_right (a b c : α) : min (a + c) (b + c) = min a b + c :=
(monotone_id.add_const c).map_min.symm

lemma max_add_add_left (a b c : α) : max (a + b) (a + c) = a + max b c :=
(monotone_id.const_add a).map_max.symm

lemma max_add_add_right (a b c : α) : max (a + c) (b + c) = max a b + c :=
(monotone_id.add_const c).map_max.symm

lemma min_le_add_of_nonneg_right {a b : α} (hb : 0 ≤ b) : min a b ≤ a + b :=
min_le_iff.2 $ or.inl $ le_add_of_nonneg_right hb

lemma min_le_add_of_nonneg_left {a b : α} (ha : 0 ≤ a) : min a b ≤ a + b :=
min_le_iff.2 $ or.inr $ le_add_of_nonneg_left ha

lemma max_le_add_of_nonneg {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) : max a b ≤ a + b :=
max_le_iff.2 ⟨le_add_of_nonneg_right hb, le_add_of_nonneg_left ha⟩

end decidable_linear_ordered_cancel_add_comm_monoid

/-- A decidable linearly ordered additive commutative group is an
additive commutative group with a decidable linear order in which
addition is strictly monotone. -/
@[protect_proj] class decidable_linear_ordered_add_comm_group (α : Type u)
  extends add_comm_group α, decidable_linear_order α :=
(add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)

@[priority 100] -- see Note [lower instance priority]
instance decidable_linear_ordered_comm_group.to_ordered_add_comm_group (α : Type u)
  [s : decidable_linear_ordered_add_comm_group α] : ordered_add_comm_group α :=
{ add := s.add, ..s }

section decidable_linear_ordered_add_comm_group
variables [decidable_linear_ordered_add_comm_group α] {a b c : α}

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

lemma min_neg_neg (a b : α) : min (-a) (-b) = -max a b :=
eq.symm $ @monotone.map_max α (order_dual α) _ _ has_neg.neg a b $ λ a b, neg_le_neg

lemma max_neg_neg (a b : α) : max (-a) (-b) = -min a b :=
eq.symm $ @monotone.map_min α (order_dual α) _ _ has_neg.neg a b $ λ a b, neg_le_neg

lemma min_sub_sub_right (a b c : α) : min (a - c) (b - c) = min a b - c :=
min_add_add_right a b (-c)

lemma max_sub_sub_right (a b c : α) : max (a - c) (b - c) = max a b - c :=
max_add_add_right a b (-c)

lemma min_sub_sub_left (a b c : α) : min (a - b) (a - c) = a - max b c :=
by simp only [sub_eq_add_neg, min_add_add_left, min_neg_neg]

lemma max_sub_sub_left (a b c : α) : max (a - b) (a - c) = a - min b c :=
by simp only [sub_eq_add_neg, max_add_add_left, max_neg_neg]

lemma max_zero_sub_eq_self (a : α) : max a 0 - max (-a) 0 = a :=
begin
  rcases le_total a 0,
  { rw [max_eq_right h, max_eq_left, zero_sub, neg_neg], { rwa [le_neg, neg_zero] } },
  { rw [max_eq_left, max_eq_right, sub_zero], { rwa [neg_le, neg_zero] }, exact h }
end

/-- `abs a` is the absolute value of `a`. -/
def abs (a : α) : α := max a (-a)

lemma abs_of_nonneg (h : 0 ≤ a) : abs a = a :=
max_eq_left $ (neg_nonpos.2 h).trans h

lemma abs_of_pos (h : 0 < a) : abs a = a :=
abs_of_nonneg h.le

lemma abs_of_nonpos (h : a ≤ 0) : abs a = -a :=
max_eq_right $ h.trans (neg_nonneg.2 h)

lemma abs_of_neg (h : a < 0) : abs a = -a :=
abs_of_nonpos h.le

@[simp] lemma abs_zero : abs 0 = (0:α) :=
abs_of_nonneg le_rfl

@[simp] lemma abs_neg (a : α) : abs (-a) = abs a :=
begin unfold abs, rw [max_comm, neg_neg] end

@[simp] lemma abs_pos : 0 < abs a ↔ a ≠ 0 :=
begin
  rcases lt_trichotomy a 0 with (ha|rfl|ha),
  { simp [abs_of_neg ha, neg_pos, ha.ne, ha] },
  { simp },
  { simp [abs_of_pos ha, ha, ha.ne.symm] }
end

lemma abs_pos_of_pos (h : 0 < a) : 0 < abs a := abs_pos.2 h.ne.symm

lemma abs_pos_of_neg (h : a < 0) : 0 < abs a := abs_pos.2 h.ne

lemma abs_sub (a b : α) : abs (a - b) = abs (b - a) :=
by rw [← neg_sub, abs_neg]

theorem abs_le' : abs a ≤ b ↔ a ≤ b ∧ -a ≤ b := max_le_iff

theorem abs_le : abs a ≤ b ↔ - b ≤ a ∧ a ≤ b :=
by rw [abs_le', and.comm, neg_le]

lemma le_abs_self (a : α) : a ≤ abs a := le_max_left _ _

lemma neg_le_abs_self (a : α) : -a ≤ abs a := le_max_right _ _

lemma abs_nonneg (a : α) : 0 ≤ abs a :=
(le_total 0 a).elim (λ h, h.trans (le_abs_self a)) (λ h, (neg_nonneg.2 h).trans $ neg_le_abs_self a)

@[simp] lemma abs_abs (a : α) : abs (abs a) = abs a :=
abs_of_nonneg $ abs_nonneg a

@[simp] lemma abs_eq_zero : abs a = 0 ↔ a = 0 :=
not_iff_not.1 $ ne_comm.trans $ (abs_nonneg a).lt_iff_ne.symm.trans abs_pos

@[simp] lemma abs_nonpos_iff {a : α} : abs a ≤ 0 ↔ a = 0 :=
(abs_nonneg a).le_iff_eq.trans abs_eq_zero

lemma abs_lt {a b : α} : abs a < b ↔ - b < a ∧ a < b :=
max_lt_iff.trans $ and.comm.trans $ by rw [neg_lt]

lemma lt_abs {a b : α} : a < abs b ↔ a < b ∨ a < -b := lt_max_iff

lemma max_sub_min_eq_abs' (a b : α) : max a b - min a b = abs (a - b) :=
begin
  cases le_total a b with ab ba,
  { rw [max_eq_right ab, min_eq_left ab, abs_of_nonpos, neg_sub], rwa sub_nonpos },
  { rw [max_eq_left ba, min_eq_right ba, abs_of_nonneg], exact sub_nonneg_of_le ba }
end

lemma max_sub_min_eq_abs (a b : α) : max a b - min a b = abs (b - a) :=
by { rw [abs_sub], exact max_sub_min_eq_abs' _ _ }

lemma abs_add (a b : α) : abs (a + b) ≤ abs a + abs b :=
abs_le.2 ⟨(neg_add (abs a) (abs b)).symm ▸
  add_le_add (neg_le.2 $ neg_le_abs_self _) (neg_le.2 $ neg_le_abs_self _),
  add_le_add (le_abs_self _) (le_abs_self _)⟩

lemma abs_sub_le_iff : abs (a - b) ≤ c ↔ a - b ≤ c ∧ b - a ≤ c :=
by rw [abs_le, neg_le_sub_iff_le_add, @sub_le_iff_le_add' _ _ b, and_comm]

lemma abs_sub_lt_iff : abs (a - b) < c ↔ a - b < c ∧ b - a < c :=
by rw [abs_lt, neg_lt_sub_iff_lt_add, @sub_lt_iff_lt_add' _ _ b, and_comm]

lemma abs_sub_abs_le_abs_sub (a b : α) : abs a - abs b ≤ abs (a - b) :=
sub_le_iff_le_add.2 $
calc abs a = abs (a - b + b)     : by rw [sub_add_cancel]
       ... ≤ abs (a - b) + abs b : abs_add _ _

lemma abs_abs_sub_abs_le_abs_sub (a b : α) : abs (abs a - abs b) ≤ abs (a - b) :=
abs_sub_le_iff.2 ⟨abs_sub_abs_le_abs_sub _ _, by rw abs_sub; apply abs_sub_abs_le_abs_sub⟩

lemma abs_eq (hb : 0 ≤ b) : abs a = b ↔ a = b ∨ a = -b :=
iff.intro
  begin
    cases le_total a 0 with a_nonpos a_nonneg,
    { rw [abs_of_nonpos a_nonpos, neg_eq_iff_neg_eq, eq_comm], exact or.inr },
    { rw [abs_of_nonneg a_nonneg, eq_comm], exact or.inl }
  end
  (by intro h; cases h; subst h; try { rw abs_neg }; exact abs_of_nonneg hb)

lemma abs_le_max_abs_abs (hab : a ≤ b)  (hbc : b ≤ c) : abs b ≤ max (abs a) (abs c) :=
abs_le'.2
  ⟨by simp [hbc.trans (le_abs_self c)],
   by simp [(neg_le_neg hab).trans (neg_le_abs_self a)]⟩

theorem abs_le_abs (h₀ : a ≤ b) (h₁ : -a ≤ b) : abs a ≤ abs b :=
(abs_le'.2 ⟨h₀, h₁⟩).trans (le_abs_self b)

lemma abs_max_sub_max_le_abs (a b c : α) : abs (max a c - max b c) ≤ abs (a - b) :=
begin
  simp_rw [abs_le, le_sub_iff_add_le, sub_le_iff_le_add, ← max_add_add_left],
  split; apply max_le_max; simp only [← le_sub_iff_add_le, ← sub_le_iff_le_add, sub_self, neg_le,
    neg_le_abs_self, neg_zero, abs_nonneg, le_abs_self]
end

lemma eq_zero_of_neg_eq {a : α} (h : -a = a) : a = 0 :=
match lt_trichotomy a 0 with
| or.inl h₁ :=
  have 0 < a, from h ▸ neg_pos_of_neg h₁,
  absurd h₁ this.asymm
| or.inr (or.inl h₁) := h₁
| or.inr (or.inr h₁) :=
  have a < 0, from h ▸ neg_neg_of_pos h₁,
  absurd h₁ this.asymm
end

lemma eq_of_abs_sub_eq_zero {a b : α} (h : abs (a - b) = 0) : a = b :=
sub_eq_zero.1 $ abs_eq_zero.1 h

lemma abs_by_cases (P : α → Prop) {a : α} (h1 : P a) (h2 : P (-a)) : P (abs a) :=
sup_ind _ _ h1 h2

lemma abs_sub_le (a b c : α) : abs (a - c) ≤ abs (a - b) + abs (b - c) :=
calc
    abs (a - c) = abs (a - b + (b - c))     : by rw [sub_add_sub_cancel]
            ... ≤ abs (a - b) + abs (b - c) : abs_add _ _

lemma abs_add_three (a b c : α) : abs (a + b + c) ≤ abs a + abs b + abs c :=
(abs_add _ _).trans (add_le_add_right (abs_add _ _) _)

lemma dist_bdd_within_interval {a b lb ub : α} (hal : lb ≤ a) (hau : a ≤ ub)
      (hbl : lb ≤ b) (hbu : b ≤ ub) : abs (a - b) ≤ ub - lb :=
abs_sub_le_iff.2 ⟨sub_le_sub hau hbl, sub_le_sub hbu hal⟩

lemma eq_of_abs_sub_nonpos (h : abs (a - b) ≤ 0) : a = b :=
eq_of_abs_sub_eq_zero (le_antisymm h (abs_nonneg (a - b)))

end decidable_linear_ordered_add_comm_group

/-- This is not so much a new structure as a construction mechanism
  for ordered groups, by specifying only the "positive cone" of the group. -/
class nonneg_add_comm_group (α : Type*) extends add_comm_group α :=
(nonneg : α → Prop)
(pos : α → Prop := λ a, nonneg a ∧ ¬ nonneg (neg a))
(pos_iff : ∀ a, pos a ↔ nonneg a ∧ ¬ nonneg (-a) . order_laws_tac)
(zero_nonneg : nonneg 0)
(add_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a + b))
(nonneg_antisymm : ∀ {a}, nonneg a → nonneg (-a) → a = 0)

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

instance [decidable_linear_ordered_add_comm_group α] :
  decidable_linear_ordered_add_comm_group (order_dual α) :=
{ add_le_add_left := λ a b h c, @add_le_add_left α _ b a h _,
  ..order_dual.decidable_linear_order α,
  ..show add_comm_group α, by apply_instance }

instance [decidable_linear_ordered_cancel_add_comm_monoid α] :
  decidable_linear_ordered_cancel_add_comm_monoid (order_dual α) :=
{ .. order_dual.decidable_linear_order α,
  .. order_dual.ordered_cancel_add_comm_monoid }

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

/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Ordered monoids and groups.
-/
import algebra.group order.bounded_lattice tactic.basic

universe u
variable {α : Type u}

section old_structure_cmd

set_option old_structure_cmd true

/-- An ordered commutative monoid is a commutative monoid
  with a partial order such that multiplication is an order embedding, i.e.
  `a * b ≤ a * c ↔ b ≤ c`. These monoids are automatically cancellative. -/
-- @[to_additive ordered_add_comm_monoid]
class ordered_comm_monoid (α : Type*) extends comm_monoid α, partial_order α :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
(lt_of_mul_lt_mul_left : ∀ a b c : α, a * b < a * c → b < c)

/-- An ordered (additive) commutative monoid is a commutative monoid
  with a partial order such that addition is an order embedding, i.e.
  `a + b ≤ a + c ↔ b ≤ c`. These monoids are automatically cancellative. -/
class ordered_add_comm_monoid (α : Type*) extends add_comm_monoid α, partial_order α :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(lt_of_add_lt_add_left : ∀ a b c : α, a + b < a + c → b < c)

attribute [to_additive ordered_add_comm_monoid] ordered_comm_monoid
attribute [to_additive ordered_add_comm_monoid.cases_on] ordered_comm_monoid.cases_on
attribute [to_additive ordered_add_comm_monoid.has_sizeof_inst] ordered_comm_monoid.has_sizeof_inst
attribute [to_additive ordered_add_comm_monoid.le] ordered_comm_monoid.le
attribute [to_additive ordered_add_comm_monoid.le_antisymm] ordered_comm_monoid.le_antisymm
attribute [to_additive ordered_add_comm_monoid.le_refl] ordered_comm_monoid.le_refl
attribute [to_additive ordered_add_comm_monoid.le_trans] ordered_comm_monoid.le_trans
attribute [to_additive ordered_add_comm_monoid.lt] ordered_comm_monoid.lt
attribute [to_additive ordered_add_comm_monoid.lt._default] ordered_comm_monoid.lt._default
attribute [to_additive ordered_add_comm_monoid.lt._default.equations._eqn_1] ordered_comm_monoid.lt._default.equations._eqn_1
attribute [to_additive ordered_add_comm_monoid.lt_iff_le_not_le] ordered_comm_monoid.lt_iff_le_not_le
attribute [to_additive ordered_add_comm_monoid.lt_of_add_lt_add_left] ordered_comm_monoid.lt_of_mul_lt_mul_left
attribute [to_additive ordered_add_comm_monoid.mk] ordered_comm_monoid.mk
attribute [to_additive ordered_add_comm_monoid.mk.inj] ordered_comm_monoid.mk.inj
attribute [to_additive ordered_add_comm_monoid.mk.inj_arrow] ordered_comm_monoid.mk.inj_arrow
attribute [to_additive ordered_add_comm_monoid.mk.sizeof_spec] ordered_comm_monoid.mk.sizeof_spec
attribute [to_additive ordered_add_comm_monoid.add] ordered_comm_monoid.mul
attribute [to_additive ordered_add_comm_monoid.add_assoc] ordered_comm_monoid.mul_assoc
attribute [to_additive ordered_add_comm_monoid.add_comm] ordered_comm_monoid.mul_comm
attribute [to_additive ordered_add_comm_monoid.add_le_add_left] ordered_comm_monoid.mul_le_mul_left
attribute [to_additive ordered_add_comm_monoid.add_zero] ordered_comm_monoid.mul_one
attribute [to_additive ordered_add_comm_monoid.no_confusion] ordered_comm_monoid.no_confusion
attribute [to_additive ordered_add_comm_monoid.no_confusion_type] ordered_comm_monoid.no_confusion_type
attribute [to_additive ordered_add_comm_monoid.zero] ordered_comm_monoid.one
attribute [to_additive ordered_add_comm_monoid.zero_add] ordered_comm_monoid.one_mul
attribute [to_additive ordered_add_comm_monoid.rec] ordered_comm_monoid.rec
attribute [to_additive ordered_add_comm_monoid.rec_on] ordered_comm_monoid.rec_on
attribute [to_additive ordered_add_comm_monoid.sizeof] ordered_comm_monoid.sizeof
attribute [to_additive ordered_add_comm_monoid.to_add_comm_monoid] ordered_comm_monoid.to_comm_monoid
attribute [to_additive ordered_add_comm_monoid.to_partial_order] ordered_comm_monoid.to_partial_order

/-- A canonically ordered monoid is an ordered commutative monoid
  in which the ordering coincides with the divisibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a * c`. -/
class canonically_ordered_monoid (α : Type*) extends ordered_comm_monoid α, lattice.order_bot α :=
(le_iff_exists_mul : ∀a b:α, a ≤ b ↔ ∃c, b = a * c)

/-- A canonically ordered (additive) monoid is an ordered commutative monoid
  in which the ordering coincides with the divisibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a + c`.
  This is satisfied by the natural numbers, for example, but not
  the integers or other ordered groups. -/
class canonically_ordered_add_monoid (α : Type*) extends ordered_add_comm_monoid α, lattice.order_bot α :=
(le_iff_exists_add : ∀a b:α, a ≤ b ↔ ∃c, b = a + c)

attribute [to_additive canonically_ordered_add_monoid] canonically_ordered_monoid

attribute [to_additive canonically_ordered_add_monoid.bot] canonically_ordered_monoid.bot
attribute [to_additive canonically_ordered_add_monoid.bot_le] canonically_ordered_monoid.bot_le
attribute [to_additive canonically_ordered_add_monoid.cases_on] canonically_ordered_monoid.cases_on
attribute [to_additive canonically_ordered_add_monoid.has_sizeof_inst] canonically_ordered_monoid.has_sizeof_inst
attribute [to_additive canonically_ordered_add_monoid.le] canonically_ordered_monoid.le
attribute [to_additive canonically_ordered_add_monoid.le_antisymm] canonically_ordered_monoid.le_antisymm
attribute [to_additive canonically_ordered_add_monoid.le_iff_exists_add] canonically_ordered_monoid.le_iff_exists_mul
attribute [to_additive canonically_ordered_add_monoid.le_refl] canonically_ordered_monoid.le_refl
attribute [to_additive canonically_ordered_add_monoid.le_trans] canonically_ordered_monoid.le_trans
attribute [to_additive canonically_ordered_add_monoid.lt] canonically_ordered_monoid.lt
attribute [to_additive canonically_ordered_add_monoid.lt._default] canonically_ordered_monoid.lt._default
attribute [to_additive canonically_ordered_add_monoid.lt._default.equations._eqn_1] canonically_ordered_monoid.lt._default.equations._eqn_1
attribute [to_additive canonically_ordered_add_monoid.lt_iff_le_not_le] canonically_ordered_monoid.lt_iff_le_not_le
attribute [to_additive canonically_ordered_add_monoid.lt_of_add_lt_add_left] canonically_ordered_monoid.lt_of_mul_lt_mul_left
attribute [to_additive canonically_ordered_add_monoid.mk] canonically_ordered_monoid.mk
attribute [to_additive canonically_ordered_add_monoid.mk.inj] canonically_ordered_monoid.mk.inj
attribute [to_additive canonically_ordered_add_monoid.mk.inj_arrow] canonically_ordered_monoid.mk.inj_arrow
attribute [to_additive canonically_ordered_add_monoid.mk.sizeof_spec] canonically_ordered_monoid.mk.sizeof_spec
attribute [to_additive canonically_ordered_add_monoid.add] canonically_ordered_monoid.mul
attribute [to_additive canonically_ordered_add_monoid.add_assoc] canonically_ordered_monoid.mul_assoc
attribute [to_additive canonically_ordered_add_monoid.add_comm] canonically_ordered_monoid.mul_comm
attribute [to_additive canonically_ordered_add_monoid.add_le_add_left] canonically_ordered_monoid.mul_le_mul_left
attribute [to_additive canonically_ordered_add_monoid.add_zero] canonically_ordered_monoid.mul_one
attribute [to_additive canonically_ordered_add_monoid.no_confusion] canonically_ordered_monoid.no_confusion
attribute [to_additive canonically_ordered_add_monoid.no_confusion_type] canonically_ordered_monoid.no_confusion_type
attribute [to_additive canonically_ordered_add_monoid.zero] canonically_ordered_monoid.one
attribute [to_additive canonically_ordered_add_monoid.zero_add] canonically_ordered_monoid.one_mul
attribute [to_additive canonically_ordered_add_monoid.rec] canonically_ordered_monoid.rec
attribute [to_additive canonically_ordered_add_monoid.rec_on] canonically_ordered_monoid.rec_on
attribute [to_additive canonically_ordered_add_monoid.sizeof] canonically_ordered_monoid.sizeof
attribute [to_additive canonically_ordered_add_monoid.to_order_bot] canonically_ordered_monoid.to_order_bot
attribute [to_additive canonically_ordered_add_monoid.to_ordered_add_comm_monoid] canonically_ordered_monoid.to_ordered_comm_monoid

end old_structure_cmd

section ordered_comm_monoid
variables [ordered_comm_monoid α] {a b c d : α}

@[to_additive add_le_add_left']
lemma mul_le_mul_left' (h : a ≤ b) : c * a ≤ c * b :=
ordered_comm_monoid.mul_le_mul_left a b h c

@[to_additive add_le_add_right']
lemma mul_le_mul_right' (h : a ≤ b) : a * c ≤ b * c :=
mul_comm c a ▸ mul_comm c b ▸ mul_le_mul_left' h

@[to_additive lt_of_add_lt_add_left']
lemma lt_of_mul_lt_mul_left' : a * b < a * c → b < c :=
ordered_comm_monoid.lt_of_mul_lt_mul_left a b c

@[to_additive add_le_add']
lemma mul_le_mul' (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
le_trans (mul_le_mul_right' h₁) (mul_le_mul_left' h₂)

@[to_additive le_add_of_nonneg_right']
lemma le_mul_of_right_le_one' (h : 1 ≤ b) : a ≤ a * b :=
have a * b ≥ a * 1, from mul_le_mul_left' h,
by rwa mul_one at this

@[to_additive le_mul_of_nonneg_left']
lemma le_mul_of_left_le_one' (h : 1 ≤ b) : a ≤ b * a :=
have 1 * a ≤ b * a, from mul_le_mul_right' h,
by rwa one_mul at this

@[to_additive lt_of_add_lt_add_right']
lemma lt_of_mul_lt_mul_right' (h : a * b < c * b) : a < c :=
lt_of_mul_lt_mul_left'
  (show b * a < b * c, begin rw [mul_comm b a, mul_comm b c], assumption end)

-- here we start using properties of one.
@[to_additive le_add_of_nonneg_of_le']
lemma le_mul_of_one_le_of_le' (ha : 1 ≤ a) (hbc : b ≤ c) : b ≤ a * c :=
one_mul b ▸ mul_le_mul' ha hbc

@[to_additive le_mul_of_le_of_nonneg']
lemma le_mul_of_le_of_one_le' (hbc : b ≤ c) (ha : 1 ≤ a) : b ≤ c * a :=
mul_one b ▸ mul_le_mul' hbc ha

@[to_additive add_nonneg']
lemma one_le_mul' (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
le_mul_of_one_le_of_le' ha hb

@[to_additive add_pos_of_pos_of_nonneg']
lemma one_lt_of_one_lt_of_one_le' (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
lt_of_lt_of_le ha $ le_mul_of_right_le_one' hb

@[to_additive add_pos']
lemma one_lt_mul' (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
one_lt_of_one_lt_of_one_le' ha $ le_of_lt hb

@[to_additive add_pos_of_nonneg_of_pos']
lemma one_lt_mul_of_one_le_of_one_lt' (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
lt_of_lt_of_le hb $ le_mul_of_left_le_one' ha

@[to_additive add_nonpos']
lemma mul_le_one' (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
one_mul (1:α) ▸ (mul_le_mul' ha hb)

@[to_additive add_le_of_nonpos_of_le']
lemma mul_le_of_le_one_of_le' (ha : a ≤ 1) (hbc : b ≤ c) : a * b ≤ c :=
one_mul c ▸ mul_le_mul' ha hbc

@[to_additive add_le_of_le_of_nonpos']
lemma mul_le_of_le_of_le_one' (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
mul_one c ▸ mul_le_mul' hbc ha

@[to_additive add_neg_of_neg_of_nonpos']
lemma mul_lt_one_of_lt_one_of_le_one' (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
lt_of_le_of_lt (mul_le_of_le_of_le_one' (le_refl _) hb) ha

@[to_additive add_neg_of_nonpos_of_neg']
lemma mul_lt_one_of_le_one_of_lt_one' (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
lt_of_le_of_lt (mul_le_of_le_one_of_le' ha (le_refl _)) hb

@[to_additive add_neg']
lemma mul_lt_one' (ha : a < 1) (hb : b < 1) : a * b < 1 :=
mul_lt_one_of_le_one_of_lt_one' (le_of_lt ha) hb

@[to_additive lt_add_of_nonneg_of_lt']
lemma lt_mul_of_one_le_of_lt' (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
lt_of_lt_of_le hbc $ le_mul_of_left_le_one' ha

@[to_additive lt_add_of_lt_of_nonneg']
lemma lt_mul_of_lt_of_one_le' (hbc : b < c) (ha : 1 ≤ a) : b < c * a :=
lt_of_lt_of_le hbc $ le_mul_of_right_le_one' ha

@[to_additive lt_add_of_pos_of_lt']
lemma lt_mul_of_one_lt_of_lt' (ha : 1 < a) (hbc : b < c) : b < a * c :=
lt_mul_of_one_le_of_lt' (le_of_lt ha) hbc

@[to_additive lt_add_of_lt_of_pos']
lemma lt_mul_of_lt_of_one_lt' (hbc : b < c) (ha : 1 < a) : b < c * a :=
lt_mul_of_lt_of_one_le' hbc (le_of_lt ha)

@[to_additive add_lt_of_nonpos_of_lt']
lemma mul_lt_of_le_one_of_lt' (ha : a ≤ 1) (hbc : b < c) : a * b < c :=
lt_of_le_of_lt (mul_le_of_le_one_of_le' ha (le_refl _)) hbc

@[to_additive add_lt_of_lt_of_nonpos']
lemma mul_lt_of_lt_of_le_one' (hbc : b < c) (ha : a ≤ 1)  : b * a < c :=
lt_of_le_of_lt (mul_le_of_le_of_le_one' (le_refl _) ha) hbc

@[to_additive add_lt_of_neg_of_lt']
lemma mul_lt_of_lt_one_of_lt' (ha : a < 1) (hbc : b < c) : a * b < c :=
mul_lt_of_le_one_of_lt' (le_of_lt ha) hbc

@[to_additive add_lt_of_lt_of_neg']
lemma mul_lt_of_lt_of_lt_one' (hbc : b < c) (ha : a < 1) : b * a < c :=
mul_lt_of_lt_of_le_one' hbc (le_of_lt ha)

@[to_additive add_eq_zero_iff']
lemma mul_eq_one_iff' (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b = 1 ↔ a = 1 ∧ b = 1 :=
iff.intro
  (assume hab : a * b = 1,
   have a ≤ 1, from hab ▸ le_mul_of_le_of_one_le' (le_refl _) hb,
   have a = 1, from le_antisymm this ha,
   have b ≤ 1, from hab ▸ le_mul_of_one_le_of_le' ha (le_refl _),
   have b = 1, from le_antisymm this hb,
   and.intro ‹a = 1› ‹b = 1›)
  (assume ⟨ha', hb'⟩, by rw [ha', hb', mul_one])

end ordered_comm_monoid

lemma bit0_pos [ordered_add_comm_monoid α] {a : α} (h : 0 < a) : 0 < bit0 a :=
add_pos' h h

namespace units

instance [monoid α] [i : preorder α] : preorder (units α) :=
preorder.lift (coe : units α → α) i

@[simp] theorem coe_le_coe [monoid α] [preorder α] {a b : units α} :
  (a : α) ≤ b ↔ a ≤ b := iff.rfl

@[simp] theorem coe_lt_coe [monoid α] [preorder α] {a b : units α} :
  (a : α) < b ↔ a < b := iff.rfl

instance [monoid α] [i : partial_order α] : partial_order (units α) :=
partial_order.lift (coe : units α → α) (by ext) i

instance [monoid α] [i : linear_order α] : linear_order (units α) :=
linear_order.lift (coe : units α → α) (by ext) i

instance [monoid α] [i : decidable_linear_order α] : decidable_linear_order (units α) :=
decidable_linear_order.lift (coe : units α → α) (by ext) i

theorem max_coe [monoid α] [decidable_linear_order α] {a b : units α} :
  (↑(max a b) : α) = max a b :=
by by_cases a ≤ b; simp [max, h]

theorem min_coe [monoid α] [decidable_linear_order α] {a b : units α} :
  (↑(min a b) : α) = min a b :=
by by_cases a ≤ b; simp [min, h]

end units

namespace with_one
open lattice

@[to_additive with_zero.preorder]
instance [preorder α] : preorder (with_one α) := with_bot.preorder
attribute [to_additive with_zero.preorder.equations._eqn_1] with_one.preorder.equations._eqn_1

@[to_additive with_zero.partial_order]
instance [partial_order α] : partial_order (with_one α) := with_bot.partial_order
attribute [to_additive with_zero.partial_order.equations._eqn_1] with_one.partial_order.equations._eqn_1

@[to_additive with_zero.lattice.order_bot]
instance [partial_order α] : order_bot (with_one α) := with_bot.order_bot
attribute [to_additive with_zero.lattice.order_bot.equations._eqn_1] with_one.lattice.order_bot.equations._eqn_1

@[to_additive with_zero.lattice.lattice]
instance [lattice α] : lattice (with_one α) := with_bot.lattice
attribute [to_additive with_zero.lattice.lattice.equations._eqn_1] with_one.lattice.lattice.equations._eqn_1

@[to_additive with_zero.linear_order]
instance [linear_order α] : linear_order (with_one α) := with_bot.linear_order
attribute [to_additive with_zero.linear_order.equations._eqn_1] with_one.linear_order.equations._eqn_1

@[to_additive with_zero.decidable_linear_order]
instance [decidable_linear_order α] :
 decidable_linear_order (with_one α) := with_bot.decidable_linear_order
 attribute [to_additive with_zero.decidable_linear_order.equations._eqn_1] with_one.decidable_linear_order.equations._eqn_1

-- This seems quite evil. Now you have two different 1's in your type. Is this even used?

@[to_additive ordered_add_comm_monoid]
def ordered_comm_monoid [ordered_comm_monoid α]
  (one_le : ∀ a : α, 1 ≤ a) : ordered_comm_monoid (with_one α) :=
begin
  suffices, refine {
    mul_le_mul_left := this,
    ..with_one.partial_order,
    ..with_one.comm_monoid, .. },
  { intros a b c h,
    have h' := lt_iff_le_not_le.1 h,
    rw lt_iff_le_not_le at ⊢,
    refine ⟨λ b h₂, _, λ h₂, h'.2 $ this _ _ h₂ _⟩,
    cases h₂, cases c with c,
    { cases h'.2 (this _ _ bot_le a) },
    { refine ⟨_, rfl, _⟩,
      cases a with a,
      { exact with_bot.some_le_some.1 h'.1 },
      { exact le_of_lt (lt_of_mul_lt_mul_left' $
          with_bot.some_lt_some.1 h), } } },
  { intros a b h c ca h₂,
    cases b with b,
    { rw le_antisymm h bot_le at h₂,
      exact ⟨_, h₂, le_refl _⟩ },
    cases a with a,
    { change c * 1 = some ca at h₂,
      simp at h₂, simp [h₂],
      exact ⟨_, rfl, by simpa using mul_le_mul_left' (one_le b)⟩ },
    { simp at h,
      cases c with c; change some _ = _ at h₂;
        simp [-mul_comm] at h₂; subst ca; refine ⟨_, rfl, _⟩,
      { exact h },
      { exact mul_le_mul_left' h } } }
end

end with_one

namespace with_top
open lattice

instance [semigroup α] : semigroup (with_top α) :=
{ ..with_zero.semigroup }

lemma coe_mul [semigroup α] {a b : α} : ((a * b : α) : with_top α) = a * b := rfl

instance [comm_semigroup α] : comm_semigroup (with_top α) :=
{ ..with_zero.comm_semigroup }

instance [monoid α] : monoid (with_top α) :=
{ ..with_zero.monoid }

instance [comm_monoid α] : comm_monoid (with_top α) :=
{ ..with_zero.comm_monoid }

instance [ordered_comm_monoid α] : ordered_comm_monoid (with_top α) :=
begin
  suffices, refine {
    mul_le_mul_left := this,
    ..with_top.partial_order,
    ..with_top.comm_monoid, ..},
  { intros a b c h,
    refine ⟨λ c h₂, _, λ h₂, h.2 $ this _ _ h₂ _⟩,
    cases h₂, cases a with a,
    { exact (not_le_of_lt h).elim le_top },
    cases b with b,
    { exact (not_le_of_lt h).elim le_top },
    { exact ⟨_, rfl, le_of_lt (lt_of_mul_lt_mul_left' $
        with_top.some_lt_some.1 h)⟩ } },
  { intros a b h c cb h₂,
    cases c with c, {cases h₂},
    cases b with b; cases h₂,
    cases a with a, {cases le_antisymm h le_top},
    simp at h,
    exact ⟨_, rfl, mul_le_mul_left' h⟩, }
end

@[simp] lemma one_lt_top [ordered_comm_monoid α] : (1 : with_top α) < ⊤ :=
coe_lt_top 1

@[simp] lemma one_lt_coe [ordered_comm_monoid α] (a : α) : (1 : with_top α) < a ↔ 1 < a :=
coe_lt_coe

@[simp] lemma mul_top [ordered_comm_monoid α] : ∀{a : with_top α}, a * ⊤ = ⊤
| none := rfl
| (some a) := rfl

@[simp] lemma top_mul [ordered_comm_monoid α] {a : with_top α} : ⊤ * a = ⊤ := rfl

lemma mul_eq_top [ordered_comm_monoid α] (a b : with_top α) : a * b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
by cases a; cases b; simp [none_eq_top, some_eq_coe, coe_mul.symm]

lemma mul_lt_top [ordered_comm_monoid α] (a b : with_top α) : a * b < ⊤ ↔ a < ⊤ ∧ b < ⊤ :=
begin
  apply not_iff_not.1,
  { simp [lt_top_iff_ne_top, mul_eq_top], finish },
  { apply classical.dec _ },
  { apply classical.dec _ }
end

instance [canonically_ordered_monoid α] : canonically_ordered_monoid (with_top α) :=
{ le_iff_exists_mul := assume a b,
  match a, b with
  | a, none     := show a ≤ ⊤ ↔ ∃c, ⊤ = a * c, by simp; refine ⟨⊤, _⟩; cases a; refl
  | (some a), (some b) := show (a:with_top α) ≤ ↑b ↔ ∃c:with_top α, ↑b = ↑a * c,
    begin
      simp only [canonically_ordered_monoid.le_iff_exists_mul, coe_le_coe, -mul_comm],
      split,
      { rintro ⟨c, rfl⟩, refine ⟨c, rfl⟩ },
      { exact assume h, match b, h with _, ⟨some c, rfl⟩ := ⟨_, rfl⟩ end }
    end
  | none, some b := show (⊤ : with_top α) ≤ b ↔ ∃c:with_top α, ↑b = ⊤ * c, by simp
  end,
  .. with_top.order_bot,
  .. with_top.ordered_comm_monoid }

end with_top

namespace with_top
open lattice

instance [add_semigroup α] : add_semigroup (with_top α) :=
{ add := λ o₁ o₂, o₁.bind (λ a, o₂.map (λ b, a + b)),
  ..@additive.add_semigroup _ $ @with_top.semigroup (multiplicative α) _ }

attribute [to_additive with_top.add_semigroup] with_top.semigroup
attribute [to_additive with_top.add_semigroup._proof_1] with_top.semigroup._proof_1
attribute [to_additive with_top.add_semigroup.equations._eqn_1] with_top.semigroup.equations._eqn_1

lemma coe_add [add_semigroup α] {a b : α} : ((a + b : α) : with_top α) = a + b := rfl

attribute [to_additive with_top.coe_add] with_top.coe_mul

instance [add_comm_semigroup α] : add_comm_semigroup (with_top α) :=
{ .. @additive.add_comm_semigroup _ $ @with_top.comm_semigroup (multiplicative α) _ }

attribute [to_additive with_top.add_comm_semigroup] with_top.comm_semigroup
attribute [to_additive with_top.add_comm_semigroup._proof_1] with_top.comm_semigroup._proof_1
attribute [to_additive with_top.add_comm_semigroup._proof_2] with_top.comm_semigroup._proof_2
attribute [to_additive with_top.add_comm_semigroup.equations._eqn_1] with_top.comm_semigroup.equations._eqn_1

instance [add_monoid α] :add_monoid (with_top α) :=
{ zero := some 0,
  add := (+),
  ..@additive.add_monoid _ $ @with_top.monoid (multiplicative α) _ }

attribute [to_additive with_top.add_monoid] with_top.monoid
attribute [to_additive with_top.add_monoid._proof_1] with_top.monoid._proof_1
attribute [to_additive with_top.add_monoid._proof_2] with_top.monoid._proof_2
attribute [to_additive with_top.add_monoid._proof_3] with_top.monoid._proof_3
attribute [to_additive with_top.add_monoid.equations._eqn_1] with_top.monoid.equations._eqn_1

instance [add_comm_monoid α] : add_comm_monoid (with_top α) :=
{ zero := 0,
  add := (+),
  ..@additive.add_comm_monoid _ $ @with_top.comm_monoid (multiplicative α) _ }

attribute [to_additive with_top.add_comm_monoid] with_top.comm_monoid
attribute [to_additive with_top.add_comm_monoid._proof_1] with_top.comm_monoid._proof_1
attribute [to_additive with_top.add_comm_monoid._proof_2] with_top.comm_monoid._proof_2
attribute [to_additive with_top.add_comm_monoid._proof_3] with_top.comm_monoid._proof_3
attribute [to_additive with_top.add_comm_monoid._proof_4] with_top.comm_monoid._proof_4
attribute [to_additive with_top.add_comm_monoid.equations._eqn_1] with_top.comm_monoid.equations._eqn_1

instance [ordered_add_comm_monoid α] : ordered_add_comm_monoid (with_top α) :=
begin
  suffices, refine {
    add_le_add_left := this,
    ..with_top.partial_order,
    ..with_top.add_comm_monoid, ..},
  { intros a b c h,
    refine ⟨λ c h₂, _, λ h₂, h.2 $ this _ _ h₂ _⟩,
    cases h₂, cases a with a,
    { exact (not_le_of_lt h).elim le_top },
    cases b with b,
    { exact (not_le_of_lt h).elim le_top },
    { exact ⟨_, rfl, le_of_lt (lt_of_add_lt_add_left' $
        with_top.some_lt_some.1 h)⟩ } },
  { intros a b h c cb h₂,
    cases c with c, {cases h₂},
    cases b with b; cases h₂,
    cases a with a, {cases le_antisymm h le_top},
    simp at h,
    exact ⟨_, rfl, add_le_add_left' h⟩, }
end

attribute [to_additive with_top.ordered_add_comm_monoid] with_top.ordered_comm_monoid
attribute [to_additive with_top.ordered_add_comm_monoid._proof_1] with_top.ordered_comm_monoid._proof_1
attribute [to_additive with_top.ordered_add_comm_monoid._proof_2] with_top.ordered_comm_monoid._proof_2
attribute [to_additive with_top.ordered_add_comm_monoid._proof_3] with_top.ordered_comm_monoid._proof_3
attribute [to_additive with_top.ordered_add_comm_monoid._proof_4] with_top.ordered_comm_monoid._proof_4
attribute [to_additive with_top.ordered_add_comm_monoid._proof_5] with_top.ordered_comm_monoid._proof_5
attribute [to_additive with_top.ordered_add_comm_monoid._proof_6] with_top.ordered_comm_monoid._proof_6
attribute [to_additive with_top.ordered_add_comm_monoid._proof_7] with_top.ordered_comm_monoid._proof_7
attribute [to_additive with_top.ordered_add_comm_monoid._proof_8] with_top.ordered_comm_monoid._proof_8
attribute [to_additive with_top.ordered_add_comm_monoid._proof_9] with_top.ordered_comm_monoid._proof_9
attribute [to_additive with_top.ordered_add_comm_monoid._proof_10] with_top.ordered_comm_monoid._proof_10
attribute [to_additive with_top.ordered_add_comm_monoid.equations._eqn_1] with_top.ordered_comm_monoid.equations._eqn_1

@[simp] lemma zero_lt_top [ordered_add_comm_monoid α] : (0 : with_top α) < ⊤ :=
coe_lt_top 0

attribute [to_additive with_top.zero_lt_top] with_top.one_lt_top

@[simp] lemma zero_lt_coe [ordered_add_comm_monoid α] (a : α) : (0 : with_top α) < a ↔ 0 < a :=
coe_lt_coe

attribute [to_additive with_top.zero_lt_coe] with_top.one_lt_coe

@[simp] lemma add_top [ordered_add_comm_monoid α] : ∀{a : with_top α}, a + ⊤ = ⊤
| none := rfl
| (some a) := rfl

attribute [to_additive with_top.add_top] with_top.mul_top

@[simp] lemma top_add [ordered_add_comm_monoid α] {a : with_top α} : ⊤ + a = ⊤ := rfl

attribute [to_additive with_top.top_add] with_top.top_mul

lemma add_eq_top [ordered_add_comm_monoid α] (a b : with_top α) : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
by cases a; cases b; simp [none_eq_top, some_eq_coe, coe_add.symm]

attribute [to_additive with_top.add_eq_top] with_top.mul_eq_top

lemma add_lt_top [ordered_add_comm_monoid α] (a b : with_top α) : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ :=
begin
  apply not_iff_not.1,
  { simp [lt_top_iff_ne_top, add_eq_top], finish},
  { apply classical.dec _ },
  { apply classical.dec _ }
end

attribute [to_additive with_top.add_lt_top] with_top.mul_lt_top

instance [canonically_ordered_add_monoid α] : canonically_ordered_add_monoid (with_top α) :=
{ le_iff_exists_add := assume a b,
  match a, b with
  | a, none     := show a ≤ ⊤ ↔ ∃c, ⊤ = a + c, by simp; refine ⟨⊤, _⟩; cases a; refl
  | (some a), (some b) := show (a:with_top α) ≤ ↑b ↔ ∃c:with_top α, ↑b = ↑a + c,
    begin
      simp only [canonically_ordered_add_monoid.le_iff_exists_add, coe_le_coe, -add_comm],
      split,
      { rintro ⟨c, rfl⟩, refine ⟨c, rfl⟩ },
      { exact assume h, match b, h with _, ⟨some c, rfl⟩ := ⟨_, rfl⟩ end }
    end
  | none, some b := show (⊤ : with_top α) ≤ b ↔ ∃c:with_top α, ↑b = ⊤ + c, by simp
  end,
  .. with_top.order_bot,
  .. with_top.ordered_add_comm_monoid }

attribute [to_additive with_top.canonically_ordered_add_monoid._match_1] with_top.canonically_ordered_monoid._match_1
attribute [to_additive with_top.canonically_ordered_add_monoid._match_1.equations._eqn_1] with_top.canonically_ordered_monoid._match_1.equations._eqn_1
attribute [to_additive with_top.canonically_ordered_add_monoid._match_1.equations._eqn_2] with_top.canonically_ordered_monoid._match_1.equations._eqn_2
attribute [to_additive with_top.canonically_ordered_add_monoid._match_1.equations._eqn_3] with_top.canonically_ordered_monoid._match_1.equations._eqn_3
attribute [to_additive with_top.canonically_ordered_add_monoid._match_1.equations._eqn_4] with_top.canonically_ordered_monoid._match_1.equations._eqn_4
attribute [to_additive with_top.canonically_ordered_add_monoid._match_2] with_top.canonically_ordered_monoid._match_2
attribute [to_additive with_top.canonically_ordered_add_monoid._match_2.equations._eqn_1] with_top.canonically_ordered_monoid._match_2.equations._eqn_1
attribute [to_additive with_top.canonically_ordered_add_monoid._proof_1] with_top.canonically_ordered_monoid._proof_1
attribute [to_additive with_top.canonically_ordered_add_monoid._proof_10] with_top.canonically_ordered_monoid._proof_10
attribute [to_additive with_top.canonically_ordered_add_monoid._proof_11] with_top.canonically_ordered_monoid._proof_11
attribute [to_additive with_top.canonically_ordered_add_monoid._proof_12] with_top.canonically_ordered_monoid._proof_12
attribute [to_additive with_top.canonically_ordered_add_monoid._proof_2] with_top.canonically_ordered_monoid._proof_2
attribute [to_additive with_top.canonically_ordered_add_monoid._proof_3] with_top.canonically_ordered_monoid._proof_3
attribute [to_additive with_top.canonically_ordered_add_monoid._proof_4] with_top.canonically_ordered_monoid._proof_4
attribute [to_additive with_top.canonically_ordered_add_monoid._proof_5] with_top.canonically_ordered_monoid._proof_5
attribute [to_additive with_top.canonically_ordered_add_monoid._proof_6] with_top.canonically_ordered_monoid._proof_6
attribute [to_additive with_top.canonically_ordered_add_monoid._proof_7] with_top.canonically_ordered_monoid._proof_7
attribute [to_additive with_top.canonically_ordered_add_monoid._proof_8] with_top.canonically_ordered_monoid._proof_8
attribute [to_additive with_top.canonically_ordered_add_monoid._proof_9] with_top.canonically_ordered_monoid._proof_9
attribute [to_additive with_top.canonically_ordered_add_monoid.equations._eqn_1] with_top.canonically_ordered_monoid.equations._eqn_1

end with_top

namespace with_bot
open lattice

instance [semigroup α] : semigroup (with_bot α) := with_top.semigroup
instance [comm_semigroup α] : comm_semigroup (with_bot α) := with_top.comm_semigroup
instance [monoid α] : monoid (with_bot α) := with_top.monoid
instance [comm_monoid α] : comm_monoid (with_bot α) :=  with_top.comm_monoid

instance [ordered_comm_monoid α] : ordered_comm_monoid (with_bot α) :=
begin
  suffices, refine {
    mul_le_mul_left := this,
    ..with_bot.partial_order,
    ..with_bot.comm_monoid, ..},
  { intros a b c h,
    have h' := h,
    rw lt_iff_le_not_le at h' ⊢,
    refine ⟨λ b h₂, _, λ h₂, h'.2 $ this _ _ h₂ _⟩,
    cases h₂, cases a with a,
    { exact (not_le_of_lt h).elim bot_le },
    cases c with c,
    { exact (not_le_of_lt h).elim bot_le },
    { exact ⟨_, rfl, le_of_lt (lt_of_mul_lt_mul_left' $
        with_bot.some_lt_some.1 h)⟩ } },
  { intros a b h c ca h₂,
    cases c with c, {cases h₂},
    cases a with a; cases h₂,
    cases b with b, {cases le_antisymm h bot_le},
    simp at h,
    exact ⟨_, rfl, mul_le_mul_left' h⟩, }
end

@[simp] lemma coe_one [monoid α] : ((1 : α) : with_bot α) = 1 := rfl

@[simp] lemma coe_mul [semigroup α] (a b : α) : ((a * b : α) : with_bot α) = a * b := rfl

@[simp] lemma bot_mul [ordered_comm_monoid α] (a : with_bot α) : ⊥ * a = ⊥ := rfl

@[simp] lemma mul_bot [ordered_comm_monoid α] (a : with_bot α) : a * ⊥ = ⊥ := by cases a; refl

instance has_one [has_one α] : has_one (with_bot α) := ⟨(1 : α)⟩

-- @[simp] lemma coe_zero [has_zero α] : ((0 : α) : with_bot α) = 0 := rfl

end with_bot

section canonically_ordered_monoid
variables [canonically_ordered_monoid α] {a b c d : α}

lemma le_iff_exists_mul : a ≤ b ↔ ∃c, b = a * c :=
canonically_ordered_monoid.le_iff_exists_mul a b

@[simp] lemma one_le (a : α) : 1 ≤ a := le_iff_exists_mul.mpr ⟨a, by simp⟩

lemma bot_eq_one : (⊥ : α) = 1 :=
le_antisymm lattice.bot_le (one_le ⊥)

@[simp] lemma mul_eq_one_iff : a * b = 1 ↔ a = 1 ∧ b = 1 :=
mul_eq_one_iff' (one_le _) (one_le _)

@[simp] lemma le_one_iff_eq : a ≤ 1 ↔ a = 1 :=
iff.intro
  (assume h, le_antisymm h (one_le a))
  (assume h, h ▸ le_refl a)

protected lemma one_lt_iff_ne_one : 1 < a ↔ a ≠ 1 :=
iff.intro ne_of_gt $ assume hne, lt_of_le_of_ne (one_le _) hne.symm

lemma le_mul_left (h : a ≤ c) : a ≤ b * c :=
calc a = 1 * a : by simp
  ... ≤ b * c : mul_le_mul' (one_le _) h

lemma le_mul_right (h : a ≤ b) : a ≤ b * c :=
calc a = a * 1 : by simp
  ... ≤ b * c : mul_le_mul' h (one_le _)

-- This looks evil... you will have two zeros or ones...
instance with_one.canonically_ordered_monoid :
  canonically_ordered_monoid (with_one α) :=
{ le_iff_exists_mul := λ a b, begin
    cases a with a,
    { exact iff_of_true lattice.bot_le ⟨b, (one_mul b).symm⟩ },
    cases b with b,
    { exact iff_of_false
        (mt (le_antisymm lattice.bot_le) (by simp))
        (λ ⟨c, h⟩, by cases c; cases h) },
    { simp [le_iff_exists_mul, -mul_comm],
      split; intro h; rcases h with ⟨c, h⟩,
      { exact ⟨some c, congr_arg some h⟩ },
      { cases c; cases h,
        { exact ⟨_, (mul_one _).symm⟩ },
        { exact ⟨_, rfl⟩ } } }
  end,
  bot    := 1,
  bot_le := assume a a' h, option.no_confusion h,
  .. with_one.ordered_comm_monoid one_le }

end canonically_ordered_monoid

instance ordered_cancel_comm_monoid.to_ordered_add_comm_monoid
  [H : ordered_cancel_comm_monoid α] : ordered_add_comm_monoid α :=
{ lt_of_add_lt_add_left := @lt_of_add_lt_add_left _ _, ..H }

section ordered_cancel_comm_monoid
variables [ordered_cancel_comm_monoid α] {a b c : α}

@[simp] lemma add_le_add_iff_left (a : α) {b c : α} : a + b ≤ a + c ↔ b ≤ c :=
⟨le_of_add_le_add_left, λ h, add_le_add_left h _⟩

@[simp] lemma add_le_add_iff_right (c : α) : a + c ≤ b + c ↔ a ≤ b :=
add_comm c a ▸ add_comm c b ▸ add_le_add_iff_left c

@[simp] lemma add_lt_add_iff_left (a : α) {b c : α} : a + b < a + c ↔ b < c :=
⟨lt_of_add_lt_add_left, λ h, add_lt_add_left h _⟩

@[simp] lemma add_lt_add_iff_right (c : α) : a + c < b + c ↔ a < b :=
add_comm c a ▸ add_comm c b ▸ add_lt_add_iff_left c

@[simp] lemma le_add_iff_nonneg_right (a : α) {b : α} : a ≤ a + b ↔ 0 ≤ b :=
have a + 0 ≤ a + b ↔ 0 ≤ b, from add_le_add_iff_left a,
by rwa add_zero at this

@[simp] lemma le_add_iff_nonneg_left (a : α) {b : α} : a ≤ b + a ↔ 0 ≤ b :=
by rw [add_comm, le_add_iff_nonneg_right]

@[simp] lemma lt_add_iff_pos_right (a : α) {b : α} : a < a + b ↔ 0 < b :=
have a + 0 < a + b ↔ 0 < b, from add_lt_add_iff_left a,
by rwa add_zero at this

@[simp] lemma lt_add_iff_pos_left (a : α) {b : α} : a < b + a ↔ 0 < b :=
by rw [add_comm, lt_add_iff_pos_right]

lemma add_eq_zero_iff_eq_zero_of_nonneg
  (ha : 0 ≤ a) (hb : 0 ≤ b) : a + b = 0 ↔ a = 0 ∧ b = 0 :=
⟨λ hab : a + b = 0,
by split; apply le_antisymm; try {assumption};
   rw ← hab; simp [ha, hb],
λ ⟨ha', hb'⟩, by rw [ha', hb', add_zero]⟩

lemma with_top.add_lt_add_iff_left :
  ∀{a b c : with_top α}, a < ⊤ → (a + c < a + b ↔ c < b)
| none := assume b c h, (lt_irrefl ⊤ h).elim
| (some a) :=
  begin
    assume b c h,
    cases b; cases c;
      simp [with_top.none_eq_top, with_top.some_eq_coe, with_top.coe_lt_top, with_top.coe_lt_coe],
    { rw [← with_top.coe_add], exact with_top.coe_lt_top _ },
    { rw [← with_top.coe_add, ← with_top.coe_add, with_top.coe_lt_coe],
      exact add_lt_add_iff_left _ }
  end

lemma with_top.add_lt_add_iff_right
  {a b c : with_top α} : a < ⊤ → (c + a < b + a ↔ c < b) :=
by simpa [add_comm] using @with_top.add_lt_add_iff_left _ _ a b c

end ordered_cancel_comm_monoid

section ordered_comm_group
variables [ordered_comm_group α] {a b c : α}

lemma neg_neg_iff_pos {α : Type} [_inst_1 : ordered_comm_group α] {a : α} : -a < 1 ↔ 1 < a :=
⟨ pos_of_neg_neg, neg_neg_of_pos ⟩

@[simp] lemma neg_le_neg_iff : -a ≤ -b ↔ b ≤ a :=
have a * b * -a ≤ a * b * -b ↔ -a ≤ -b, from mul_le_mul_iff_left _,
by simp at this; simp [this]

lemma neg_le : -a ≤ b ↔ -b ≤ a :=
have -a ≤ -(-b) ↔ -b ≤ a, from neg_le_neg_iff,
by rwa neg_neg at this

lemma le_neg : a ≤ -b ↔ b ≤ -a :=
have -(-a) ≤ -b ↔ b ≤ -a, from neg_le_neg_iff,
by rwa neg_neg at this

@[simp] lemma neg_nonpos : -a ≤ 1 ↔ 1 ≤ a :=
have -a ≤ -1 ↔ 1 ≤ a, from neg_le_neg_iff,
by rwa neg_one at this

@[simp] lemma neg_nonneg : 1 ≤ -a ↔ a ≤ 1 :=
have -1 ≤ -a ↔ a ≤ 1, from neg_le_neg_iff,
by rwa neg_one at this

@[simp] lemma neg_lt_neg_iff : -a < -b ↔ b < a :=
have a * b * -a < a * b * -b ↔ -a < -b, from mul_lt_mul_iff_left _,
by simp at this; simp [this]

lemma neg_lt_one : -a < 1 ↔ 1 < a :=
have -a < -1 ↔ 1 < a, from neg_lt_neg_iff,
by rwa neg_one at this

lemma neg_pos : 1 < -a ↔ a < 1 :=
have -1 < -a ↔ a < 1, from neg_lt_neg_iff,
by rwa neg_one at this

lemma neg_lt : -a < b ↔ -b < a :=
have -a < -(-b) ↔ -b < a, from neg_lt_neg_iff,
by rwa neg_neg at this

lemma lt_neg : a < -b ↔ b < -a :=
have -(-a) < -b ↔ b < -a, from neg_lt_neg_iff,
by rwa neg_neg at this

lemma sub_le_sub_iff_left (a : α) {b c : α} : a - b ≤ a - c ↔ c ≤ b :=
(mul_le_mul_iff_left _).trans neg_le_neg_iff

lemma sub_le_sub_iff_right (c : α) : a - c ≤ b - c ↔ a ≤ b :=
mul_le_mul_iff_right _

lemma sub_lt_sub_iff_left (a : α) {b c : α} : a - b < a - c ↔ c < b :=
(mul_lt_mul_iff_left _).trans neg_lt_neg_iff

lemma sub_lt_sub_iff_right (c : α) : a - c < b - c ↔ a < b :=
mul_lt_mul_iff_right _

@[simp] lemma sub_nonneg : 1 ≤ a - b ↔ b ≤ a :=
have a - a ≤ a - b ↔ b ≤ a, from sub_le_sub_iff_left a,
by rwa sub_self at this

@[simp] lemma sub_nonpos : a - b ≤ 1 ↔ a ≤ b :=
have a - b ≤ b - b ↔ a ≤ b, from sub_le_sub_iff_right b,
by rwa sub_self at this

@[simp] lemma sub_pos : 1 < a - b ↔ b < a :=
have a - a < a - b ↔ b < a, from sub_lt_sub_iff_left a,
by rwa sub_self at this

@[simp] lemma sub_lt_one : a - b < 1 ↔ a < b :=
have a - b < b - b ↔ a < b, from sub_lt_sub_iff_right b,
by rwa sub_self at this

lemma le_neg_mul_iff_mul_le : b ≤ -a * c ↔ a * b ≤ c :=
have -a * (a * b) ≤ -a * c ↔ a * b ≤ c, from mul_le_mul_iff_left _,
by rwa neg_mul_cancel_left at this

lemma le_sub_iff_mul_le' : b ≤ c - a ↔ a * b ≤ c :=
by rw [sub_eq_mul_neg, mul_comm, le_neg_mul_iff_mul_le]

lemma le_sub_iff_mul_le : a ≤ c - b ↔ a * b ≤ c :=
by rw [le_sub_iff_mul_le', mul_comm]

@[simp] lemma neg_mul_le_iff_le_mul : -b * a ≤ c ↔ a ≤ b * c :=
have -b * a ≤ -b * (b * c) ↔ a ≤ b * c, from mul_le_mul_iff_left _,
by rwa neg_mul_cancel_left at this

lemma sub_le_iff_le_mul' : a - b ≤ c ↔ a ≤ b * c :=
by rw [sub_eq_mul_neg, mul_comm, neg_mul_le_iff_le_mul]

lemma sub_le_iff_le_mul : a - c ≤ b ↔ a ≤ b * c :=
by rw [sub_le_iff_le_mul', mul_comm]

@[simp] lemma mul_neg_le_iff_le_mul : a * -c ≤ b ↔ a ≤ b * c :=
sub_le_iff_le_mul

@[simp] lemma mul_neg_le_iff_le_mul' : a * -b ≤ c ↔ a ≤ b * c :=
sub_le_iff_le_mul'

lemma neg_mul_le_iff_le_mul' : -c * a ≤ b ↔ a ≤ b * c :=
by rw [neg_mul_le_iff_le_mul, mul_comm]

@[simp] lemma neg_le_sub_iff_le_mul : -b ≤ a - c ↔ c ≤ a * b :=
le_sub_iff_mul_le.trans neg_mul_le_iff_le_mul'

lemma neg_le_sub_iff_le_mul' : -a ≤ b - c ↔ c ≤ a * b :=
by rw [neg_le_sub_iff_le_mul, mul_comm]

lemma sub_le : a - b ≤ c ↔ a - c ≤ b :=
sub_le_iff_le_mul'.trans sub_le_iff_le_mul.symm

theorem le_sub : a ≤ b - c ↔ c ≤ b - a :=
le_sub_iff_mul_le'.trans le_sub_iff_mul_le.symm

@[simp] lemma lt_neg_mul_iff_mul_lt : b < -a * c ↔ a * b < c :=
have -a * (a * b) < -a * c ↔ a * b < c, from mul_lt_mul_iff_left _,
by rwa neg_mul_cancel_left at this

lemma lt_sub_iff_mul_lt' : b < c - a ↔ a * b < c :=
by rw [sub_eq_mul_neg, mul_comm, lt_neg_mul_iff_mul_lt]

lemma lt_sub_iff_mul_lt : a < c - b ↔ a * b < c :=
by rw [lt_sub_iff_mul_lt', mul_comm]

@[simp] lemma neg_mul_lt_iff_lt_mul : -b * a < c ↔ a < b * c :=
have -b * a < -b * (b * c) ↔ a < b * c, from mul_lt_mul_iff_left _,
by rwa neg_mul_cancel_left at this

lemma sub_lt_iff_lt_mul' : a - b < c ↔ a < b * c :=
by rw [sub_eq_mul_neg, mul_comm, neg_mul_lt_iff_lt_mul]

lemma sub_lt_iff_lt_mul : a - c < b ↔ a < b * c :=
by rw [sub_lt_iff_lt_mul', mul_comm]

lemma neg_mul_lt_iff_lt_mul_right : -c * a < b ↔ a < b * c :=
by rw [neg_mul_lt_iff_lt_mul, mul_comm]

@[simp] lemma neg_lt_sub_iff_lt_mul : -b < a - c ↔ c < a * b :=
lt_sub_iff_mul_lt.trans neg_mul_lt_iff_lt_mul_right

lemma neg_lt_sub_iff_lt_mul' : -a < b - c ↔ c < a * b :=
by rw [neg_lt_sub_iff_lt_mul, mul_comm]

lemma sub_lt : a - b < c ↔ a - c < b :=
sub_lt_iff_lt_mul'.trans sub_lt_iff_lt_mul.symm

theorem lt_sub : a < b - c ↔ c < b - a :=
lt_sub_iff_mul_lt'.trans lt_sub_iff_mul_lt.symm

lemma sub_le_self_iff (a : α) {b : α} : a - b ≤ a ↔ 1 ≤ b :=
sub_le_iff_le_mul'.trans (le_mul_iff_nonneg_left _)

lemma sub_lt_self_iff (a : α) {b : α} : a - b < a ↔ 1 < b :=
sub_lt_iff_lt_mul'.trans (lt_mul_iff_pos_left _)

end ordered_comm_group

namespace decidable_linear_ordered_comm_group
variables [s : decidable_linear_ordered_comm_group α]
include s

instance : decidable_linear_ordered_cancel_comm_monoid α :=
{ le_of_mul_le_mul_left := λ x y z, le_of_mul_le_mul_left,
  mul_left_cancel := λ x y z, mul_left_cancel,
  mul_right_cancel := λ x y z, mul_right_cancel,
  ..s }

end decidable_linear_ordered_comm_group

set_option old_structure_cmd true
/-- This is not so much a new structure as a construction mechanism
  for ordered groups, by specifying only the "positive cone" of the group. -/
class nonneg_comm_group (α : Type*) extends comm_group α :=
(nonneg : α → Prop)
(pos : α → Prop := λ a, nonneg a ∧ ¬ nonneg (neg a))
(pos_iff : ∀ a, pos a ↔ nonneg a ∧ ¬ nonneg (-a) . order_laws_tac)
(one_nonneg : nonneg 1)
(mul_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a * b))
(nonneg_antisymm : ∀ {a}, nonneg a → nonneg (-a) → a = 1)

namespace nonneg_comm_group
variable [s : nonneg_comm_group α]
include s

@[reducible] instance to_ordered_comm_group : ordered_comm_group α :=
{ le := λ a b, nonneg (b - a),
  lt := λ a b, pos (b - a),
  lt_iff_le_not_le := λ a b, by simp; rw [pos_iff]; simp,
  le_refl := λ a, by simp [one_nonneg],
  le_trans := λ a b c nab nbc, by simp [-sub_eq_mul_neg];
    rw ← sub_mul_sub_cancel; exact mul_nonneg nbc nab,
  le_antisymm := λ a b nab nba, eq_of_sub_eq_one $
    nonneg_antisymm nba (by rw neg_sub; exact nab),
  mul_le_mul_left := λ a b nab c, by simpa [(≤), preorder.le] using nab,
  mul_lt_mul_left := λ a b nab c, by simpa [(<), preorder.lt] using nab, ..s }

theorem nonneg_def {a : α} : nonneg a ↔ 1 ≤ a :=
show _ ↔ nonneg _, by simp

theorem pos_def {a : α} : pos a ↔ 1 < a :=
show _ ↔ pos _, by simp

theorem not_one_pos : ¬ pos (1 : α) :=
mt pos_def.1 (lt_irrefl _)

theorem one_lt_iff_nonneg_nonneg {a : α} :
  1 < a ↔ nonneg a ∧ ¬ nonneg (-a) :=
pos_def.symm.trans (pos_iff α _)

theorem nonneg_total_iff :
  (∀ a : α, nonneg a ∨ nonneg (-a)) ↔
  (∀ a b : α, a ≤ b ∨ b ≤ a) :=
⟨λ h a b, by have := h (b - a); rwa [neg_sub] at this,
 λ h a, by rw [nonneg_def, nonneg_def, neg_nonneg]; apply h⟩

def to_decidable_linear_ordered_comm_group
  [decidable_pred (@nonneg α _)]
  (nonneg_total : ∀ a : α, nonneg a ∨ nonneg (-a))
  : decidable_linear_ordered_comm_group α :=
{ le := (≤),
  lt := (<),
  lt_iff_le_not_le := @lt_iff_le_not_le _ _,
  le_refl := @le_refl _ _,
  le_trans := @le_trans _ _,
  le_antisymm := @le_antisymm _ _,
  le_total := nonneg_total_iff.1 nonneg_total,
  decidable_le := by apply_instance,
  decidable_eq := by apply_instance,
  decidable_lt := by apply_instance,
  ..@nonneg_comm_group.to_ordered_comm_group _ s }

end nonneg_comm_group

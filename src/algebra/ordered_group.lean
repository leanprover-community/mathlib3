/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.ordered_monoid
/-!
# Ordered groups

This file develops the basics of ordered groups.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/

-- TODO: there are probably "left/right" versions of some of the lemmas in this file
-- that might be proven.

set_option old_structure_cmd true

universe u
variables {α : Type u} {a b c d : α}

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

@[priority 102, to_additive]
instance ordered_comm_group.to_has_mul_le_mul_left [ordered_comm_group α] :
  has_mul_le_mul_left α :=
{ mul_le_mul_left := λ a b ab c, ordered_comm_group.mul_le_mul_left b ab c a }

@[to_additive]
instance units.covariant_class [ordered_comm_monoid α] :
  has_mul_le_mul_left (units α) :=
{ mul_le_mul_left := λ a b c bc, by {
  rcases le_iff_eq_or_lt.mp bc with ⟨rfl, h⟩,
  { exact rfl.le },
  refine le_iff_eq_or_lt.mpr (or.inr _),
  refine units.coe_lt_coe.mp _,
  cases lt_iff_le_and_ne.mp (units.coe_lt_coe.mpr h) with lef rig,
  exact lt_of_le_of_ne (mul_le_mul_left' lef ↑a) (λ hg, rig ((units.mul_right_inj a).mp hg)) } }

/--The units of an ordered commutative monoid form an ordered commutative group. -/
@[to_additive]
instance units.ordered_comm_group [ordered_comm_monoid α] : ordered_comm_group (units α) :=
{ mul_le_mul_left := λ a b h c, (mul_le_mul_left' (units.coe_le_coe.mpr h) _ : (c * a : α) ≤ c * b),
  .. units.partial_order,
  .. (infer_instance : comm_group (units α)) }

section ordered_comm_group
variables [ordered_comm_group α]

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
  [s : ordered_comm_group α] :
  ordered_cancel_comm_monoid α :=
{ mul_left_cancel       := @mul_left_cancel α _,
  le_of_mul_le_mul_left := λ a b c, ordered_comm_group.le_of_mul_le_mul_left,
  ..s }

@[priority 100, to_additive]
instance ordered_comm_group.has_exists_mul_of_le (α : Type u)
  [ordered_comm_group α] :
  has_exists_mul_of_le α :=
⟨λ a b hab, ⟨b * a⁻¹, (mul_inv_cancel_comm_assoc a b).symm⟩⟩

end ordered_comm_group

-- trying out weaker typeclass assumptiona
section group
variable [group α]

section preorder
variable [preorder α]

@[priority 98, to_additive]
instance group.has_mul_le_mul_left.to_has_le_of_mul_le_mul_left [has_mul_le_mul_left α] :
  has_le_of_mul_le_mul_left α :=
{ le_of_mul_le_mul_left := λ a b c bc,
    calc b = a⁻¹ * (a * b) : eq_inv_mul_of_mul_eq rfl
       ... ≤ a⁻¹ * (a * c) : mul_le_mul_left' bc a⁻¹
       ... = c : inv_mul_cancel_left a c }

@[priority 96, to_additive]
instance group.has_mul_le_mul_right.to_has_le_of_mul_le_mul_right [has_mul_le_mul_right α] :
  has_le_of_mul_le_mul_right α :=
{ le_of_mul_le_mul_right := λ a b c bc,
    calc b = b * a * a⁻¹ : eq_mul_inv_of_mul_eq rfl
       ... ≤ c * a * a⁻¹ : mul_le_mul_right' bc a⁻¹
       ... = c : mul_inv_eq_of_eq_mul rfl }

@[to_additive neg_le_iff_add_nonneg']
lemma inv_le_iff_one_le_mul' [has_mul_le_mul_left α] : a⁻¹ ≤ b ↔ 1 ≤ a * b :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw [← mul_inv_cancel_left a 1, mul_one],
    exact mul_le_mul_left' h a },
  { rw [← mul_one a⁻¹, ← inv_mul_cancel_left a b],
    exact mul_le_mul_left' h _ }
end

section left

section has_mul_le_mul_left
variable [has_mul_le_mul_left α]

@[simp, to_additive]
lemma mul_le_mul_iff_left' (c : α) : c * a ≤ c * b ↔ a ≤ b :=
⟨λ h, by simpa using has_mul_le_mul_left.mul_le_mul_left c⁻¹ h,
  λ h, mul_le_mul_left' h c⟩

@[to_additive]
lemma le_inv_mul_iff : b ≤ a⁻¹ * c ↔ a * b ≤ c :=
by rw [← mul_le_mul_iff_left' a, mul_inv_cancel_left]

@[to_additive]
lemma inv_mul_le_iff'' : b⁻¹ * a ≤ c ↔ a ≤ b * c :=
by rw [← mul_le_mul_iff_left' b, mul_inv_cancel_left]

@[to_additive]
lemma le_inv_iff_mul_le_one' : a ≤ b⁻¹ ↔ b * a ≤ 1 :=
(mul_le_mul_iff_left' b).symm.trans $ by rw mul_inv_self

@[simp, to_additive neg_nonpos]
lemma inv_le_one' : a⁻¹ ≤ 1 ↔ 1 ≤ a :=
by rw [← mul_le_mul_iff_left' a, mul_one, mul_right_inv]

@[simp, to_additive neg_nonneg]
lemma one_le_inv' : 1 ≤ a⁻¹ ↔ a ≤ 1 :=
by rw [← mul_le_mul_iff_left' a, mul_right_inv, mul_one]

@[to_additive]
lemma le_self_mul_iff_one_le (a : α) : a ≤ a * b ↔ 1 ≤ b :=
by rw [← mul_le_mul_iff_left' a⁻¹, inv_mul_cancel_left, mul_left_inv]

/- The next lemmas are now redundant, probably: from here... -/
@[to_additive]
lemma mul_le_of_le_inv_mul (h : b ≤ a⁻¹ * c) : a * b ≤ c :=
le_inv_mul_iff.mp h

@[to_additive]
lemma le_inv_mul_of_mul_le (h : a * b ≤ c) : b ≤ a⁻¹ * c :=
le_inv_mul_iff.mpr h

@[to_additive]
lemma le_mul_of_inv_mul_le (h : b⁻¹ * a ≤ c) : a ≤ b * c :=
inv_mul_le_iff''.mp h

@[to_additive]
lemma le_mul_of_inv_mul_le_left (h : b⁻¹ * a ≤ c) : a ≤ b * c :=
le_mul_of_inv_mul_le h

@[to_additive]
lemma inv_mul_le_of_le_mul (h : a ≤ b * c) : b⁻¹ * a ≤ c :=
inv_mul_le_iff''.mpr h

@[to_additive]
lemma inv_mul_le_left_of_le_mul (h : a ≤ b * c) : b⁻¹ * a ≤ c :=
inv_mul_le_of_le_mul h

@[to_additive nonpos_of_neg_nonneg]
lemma one_le_of_inv_le_one (h : a⁻¹ ≤ 1) : 1 ≤ a :=
inv_le_one'.mp h

@[to_additive]
lemma inv_le_one_of_one_le (h : 1 ≤ a) : a⁻¹ ≤ 1 :=
inv_le_one'.mpr h

@[to_additive neg_nonneg_of_nonpos]
lemma one_le_inv_of_le_one (h : a ≤ 1) : 1 ≤ a⁻¹ :=
one_le_inv'.mpr h
/- ...to here. -/

end has_mul_le_mul_left

section has_mul_lt_mul_left
variable [has_mul_lt_mul_left α]

@[simp, to_additive]
lemma mul_lt_mul_iff_left' (a : α) : a * b < a * c ↔ b < c :=
⟨λ h, by simpa using has_mul_lt_mul_left.mul_lt_mul_left a⁻¹ h,
  λ h, has_mul_lt_mul_left.mul_lt_mul_left _ h⟩

@[simp, to_additive]
lemma lt_inv_mul_iff : b < a⁻¹ * c ↔ a * b < c :=
by rw [← mul_lt_mul_iff_left' a, mul_inv_cancel_left]

@[simp, to_additive]
lemma inv_mul_lt_iff'' : b⁻¹ * a < c ↔ a < b * c :=
by rw [← mul_lt_mul_iff_left' b, mul_inv_cancel_left]

@[to_additive neg_lt_iff_add_pos]
lemma inv_lt_iff_one_lt_mul' : a⁻¹ < b ↔ 1 < a * b :=
(mul_lt_mul_iff_left' a).symm.trans $ by rw mul_inv_self

@[to_additive lt_neg_iff_add_neg]
lemma lt_inv_iff_mul_lt_one' : a < b⁻¹ ↔ b * a < 1 :=
(mul_lt_mul_iff_left' b).symm.trans $ by rw mul_inv_self

/- The following lemmas are probably superfluous.  From here... -/
@[to_additive]
lemma mul_lt_of_lt_inv_mul (h : b < a⁻¹ * c) : a * b < c :=
lt_inv_mul_iff.mp h

@[to_additive]
lemma lt_inv_mul_of_mul_lt (h : a * b < c) : b < a⁻¹ * c :=
lt_inv_mul_iff.mpr h

@[to_additive]
lemma lt_mul_of_inv_mul_lt (h : b⁻¹ * a < c) : a < b * c :=
inv_mul_lt_iff''.mp h

@[to_additive]
lemma inv_mul_lt_of_lt_mul (h : a < b * c) : b⁻¹ * a < c :=
inv_mul_lt_iff''.mpr h

@[to_additive]
lemma inv_mul_lt_left_of_lt_mul (h : a < b * c) : b⁻¹ * a < c :=
inv_mul_lt_of_lt_mul h
/- ...to here. -/

end has_mul_lt_mul_left

end left

section right

section has_mul_le_mul_right
variables [has_mul_le_mul_right α]

@[simp, to_additive]
lemma mul_le_mul_iff_right' (c : α) : a * c ≤ b * c ↔ a ≤ b :=
⟨λ h, by simpa using mul_le_mul_right' h c⁻¹, λ h, mul_le_mul_right' h _⟩

@[to_additive]
lemma mul_inv_le_iff'' : a * c⁻¹ ≤ b ↔ a ≤ b * c :=
by rwa [← mul_le_mul_iff_right' c, inv_mul_cancel_right]

@[to_additive neg_nonpos_iff]
lemma inv_le_one_iff' : a⁻¹ ≤ 1 ↔ 1 ≤ a :=
by rw [← mul_le_mul_iff_right' a, mul_left_inv, one_mul]

@[to_additive right.nonpos_of_neg_nonneg]
lemma right.le_one_of_one_le_inv : 1 ≤ a⁻¹ ↔ a ≤ 1 :=
by rw [← mul_le_mul_iff_right' a, mul_left_inv, one_mul]

@[to_additive]
lemma le_inv_iff_mul_le_one : a ≤ b⁻¹ ↔ a * b ≤ 1 :=
by rw [← mul_le_mul_iff_right' b, mul_left_inv]
@[simp, to_additive]
lemma div_le_div_iff_right (c : α) : a / c ≤ b / c ↔ a ≤ b :=
by { rw [div_eq_mul_inv, div_eq_mul_inv], exact mul_le_mul_iff_right' c⁻¹ }

@[simp, to_additive sub_nonneg]
lemma one_le_div'' : 1 ≤ a / b ↔ b ≤ a :=
by rw [← mul_le_mul_iff_right' b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_nonneg ↔ le_of_sub_nonneg sub_nonneg_of_le

@[simp, to_additive sub_nonpos]
lemma div_le_one'' : a / b ≤ 1 ↔ a ≤ b :=
by rw [← mul_le_mul_iff_right' b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_nonpos ↔ le_of_sub_nonpos sub_nonpos_of_le

@[to_additive]
lemma le_div_iff_mul_le_right : b ≤ c / a ↔ b * a ≤ c :=
by rw [← mul_le_mul_iff_right' a, div_eq_mul_inv, inv_mul_cancel_right]

@[to_additive]
lemma le_div_iff_mul_le : a ≤ c / b ↔ a * b ≤ c :=
by rw [← mul_le_mul_iff_right' b, div_eq_mul_inv, inv_mul_cancel_right]

alias le_sub_iff_add_le ↔ add_le_of_le_sub_right le_sub_right_of_add_le

@[to_additive]
lemma div_le_iff_le_mul_left : a / b ≤ c ↔ a ≤ c * b :=
by rw [← mul_le_mul_iff_right' b, div_eq_mul_inv, inv_mul_cancel_right]

alias le_sub_iff_add_le_right ↔ add_le_of_le_sub_left le_sub_left_of_add_le

@[to_additive]
lemma div_le_iff_le_mul : a / c ≤ b ↔ a ≤ b * c :=
by rw [← mul_le_mul_iff_right' c, div_eq_mul_inv, inv_mul_cancel_right]

/- The following lemmas are probably superfluous. From here... -/
@[to_additive]
lemma div_le_div_right'' (h : a ≤ b) (c : α) : a / c ≤ b / c :=
(div_le_div_iff_right c).mpr h

@[to_additive]
lemma le_mul_of_mul_inv_le_right (h : a * c⁻¹ ≤ b) : a ≤ b * c :=
mul_inv_le_iff''.mp h
/- ...to here. -/

end has_mul_le_mul_right

section has_mul_lt_mul_right
variable [has_mul_lt_mul_right α]

@[simp, to_additive]
lemma mul_lt_mul_iff_right' (c : α) : a * c < b * c ↔ a < b :=
begin
  refine ⟨λ h, _, λ h, has_mul_lt_mul_right.mul_lt_mul_right _ h⟩,
  obtain F : a * c * c⁻¹ < b * c * c⁻¹ := has_mul_lt_mul_right.mul_lt_mul_right c⁻¹ h,
  simpa only [mul_inv_cancel_right] using F,
end


@[simp, to_additive]
lemma div_lt_div_iff_right (c : α) : a / c < b / c ↔ a < b :=
by { rw [← mul_lt_mul_iff_right' c], simp [div_eq_mul_inv] }

/- The following lemma is probably superfluous. -/
@[to_additive]
lemma div_lt_div_right'' (h : a < b) (c : α) : a / c < b / c :=
(div_lt_div_iff_right c).2 h

@[simp, to_additive sub_pos]
lemma one_lt_div'' : 1 < a / b ↔ b < a :=
by rw [← mul_lt_mul_iff_right' b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_pos ↔ lt_of_sub_pos sub_pos_of_lt

@[simp, to_additive sub_lt_zero]
lemma div_lt_one'' : a / b < 1 ↔ a < b :=
by rw [← mul_lt_mul_iff_right' b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_lt_zero ↔ lt_of_sub_neg sub_neg_of_lt

/- The non-primed versions of the same lemma, except that multiplication/addition on had been
commuted.  Since now there is no longer a commutativity assumption, I removed the other lemmas. -/
@[to_additive]
lemma lt_mul_inv_iff_mul_lt' : b < c * a⁻¹ ↔ b * a < c :=
by rw [← mul_lt_mul_iff_right' a, inv_mul_cancel_right]

/- The non-primed versions of the same lemma, except that multiplication/addition on had been
commuted.  Since now there is no longer a commutativity assumption, I removed the other lemmas. -/
@[to_additive lt_sub_iff_add_lt]
lemma lt_div_iff_mul_lt : b < c / a ↔ b * a < c :=
by rw [div_eq_mul_inv, lt_mul_inv_iff_mul_lt']

/- The non-primed versions of the same lemma, except that multiplication/addition on had been
commuted.  Since now there is no longer a commutativity assumption, I removed the other lemmas. -/
@[to_additive]
lemma mul_inv_lt_iff_lt_mul' : a * b⁻¹ < c ↔ a < c * b :=
by rw [← mul_lt_mul_iff_right' b, inv_mul_cancel_right]

@[to_additive]
lemma div_lt_iff_lt_mul' : a / b < c ↔ a < c * b :=
by rw [div_eq_mul_inv, mul_inv_lt_iff_lt_mul']

alias sub_lt_iff_lt_add' ↔ lt_add_of_sub_left_lt sub_left_lt_of_lt_add

end has_mul_lt_mul_right
end right

section le_left_right
variables [has_mul_le_mul_left α] [has_mul_le_mul_right α]

@[to_additive]
lemma mul_inv_le_inv_mul_iff : a * b⁻¹ ≤ c⁻¹ * d ↔ c * a ≤ d * b :=
by rw [← mul_le_mul_iff_left' c, ← mul_le_mul_iff_right' b, mul_inv_cancel_left, mul_assoc,
    inv_mul_cancel_right]

@[simp, to_additive]
lemma inv_le_inv_iff : b⁻¹ ≤ a⁻¹ ↔ a ≤ b :=
by rw [← mul_le_mul_iff_left' b, ← mul_le_mul_iff_right' a, mul_right_inv, inv_mul_cancel_right,
      one_mul]

@[to_additive le_neg]
lemma le_inv' : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
⟨λ h, inv_le_inv_iff.mp ((inv_inv _).le.trans h), λ h, inv_le_inv_iff.mp ((inv_inv _).le.trans h)⟩

@[to_additive neg_le]
lemma inv_le' : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
⟨λ h, inv_le_inv_iff.mp (h.trans (inv_inv _).symm.le),
  λ h, inv_le_inv_iff.mp (h.trans (inv_inv _).symm.le)⟩

@[simp, to_additive]
lemma div_le_self_iff (a : α) : a / b ≤ a ↔ 1 ≤ b :=
by rw [div_eq_mul_inv, mul_inv_le_iff'', le_self_mul_iff_one_le]

@[to_additive]
lemma mul_inv_le_mul_inv (hab : a ≤ b) (hcd : c ≤ d) : a * d⁻¹ ≤ b * c⁻¹ :=
calc a * d⁻¹ ≤ b * d⁻¹ : mul_le_mul_right' hab d⁻¹
         ... ≤ b * c⁻¹ : mul_le_mul_left' (inv_le_inv_iff.mpr hcd) _

@[to_additive sub_le_sub]
lemma div_le_div'' (hab : a ≤ b) (hcd : c ≤ d) : a / d ≤ b / c :=
calc a / d = a * d⁻¹ : div_eq_mul_inv _ _
       ... ≤ b * c⁻¹ : mul_inv_le_mul_inv hab hcd
       ... = b / c   : (div_eq_mul_inv b c).symm

@[to_additive]
lemma inv_mul_le_mul_inv_of (h : b⁻¹ * a ≤ c * d⁻¹) : a * d ≤ b * c :=
begin
  refine (_ : _ ≤ b * (c * d⁻¹) * d).trans (by rw [mul_assoc, inv_mul_cancel_right]),
  refine mul_le_mul_right' _ d,
  rw [← inv_mul_cancel_left b⁻¹ a, inv_inv],
  refine mul_le_mul_left' h b
end

@[to_additive]
lemma inv_mul_le_mul_inv_iff' : b⁻¹ * a ≤ c * d⁻¹ ↔ a * d ≤ b * c :=
begin
  refine ⟨λ h, inv_mul_le_mul_inv_of h, λ h, inv_mul_le_mul_inv_of _⟩,
  rw [← mul_inv_rev, ← mul_inv_rev],
  exact inv_le_inv_iff.mpr h,
end

@[to_additive]
lemma inv_mul_le_mul_inv_iff : a * b⁻¹ ≤ c⁻¹ * d ↔ c * a ≤ d * b :=
by rw [← inv_mul_le_mul_inv_iff', inv_inv, inv_inv]

@[simp, to_additive]
lemma mul_inv_le_mul_inv_iff_left (a : α) : a * b⁻¹ ≤ a * c⁻¹ ↔ c ≤ b :=
(mul_le_mul_iff_left' a).trans inv_le_inv_iff

@[simp, to_additive]
lemma div_le_div_iff_left (a : α) : a / b ≤ a / c ↔ c ≤ b :=
by { simp only [div_eq_mul_inv, mul_inv_le_mul_inv_iff_left] }

@[to_additive]
lemma mul_inv_le_mul_inv_left (h : a ≤ b) (c : α) : c * b⁻¹ ≤ c * a⁻¹ :=
(mul_inv_le_mul_inv_iff_left c).mpr h

/- The following lemma is probably superfluous. -/
@[to_additive]
lemma div_le_div_left'' (h : a ≤ b) (c : α) : c / b ≤ c / a :=
(div_le_div_iff_left c).2 h

alias sub_le_self_iff ↔ _ sub_le_self

@[simp, to_additive]
lemma inv_le_mul_inv_iff_le_mul : b⁻¹ ≤ a * c⁻¹ ↔ c ≤ b * a :=
by rw [← mul_le_mul_iff_right' c, ← mul_le_mul_iff_left' b, ← mul_assoc, mul_right_inv,
      inv_mul_cancel_right, one_mul]

/- This version is to get a slightly different `to_additive` statement. -/
@[simp, to_additive]
lemma inv_le_div_iff_le_mul_left : b⁻¹ ≤ a / c ↔ c ≤ b * a :=
by rw [div_eq_mul_inv, inv_le_mul_inv_iff_le_mul]

@[to_additive]
lemma inv_le_mul_inv_iff_le_mul' : a⁻¹ ≤ b * c⁻¹ ↔ c ≤ a * b :=
by rw [← mul_le_mul_iff_right' c, ← mul_le_mul_iff_left' a, ← mul_assoc, mul_right_inv,
      inv_mul_cancel_right, one_mul]

@[to_additive]
lemma one_div_le_div_iff_le_mul' : 1 / a ≤ b / c ↔ c ≤ a * b :=
by rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, inv_le_mul_inv_iff_le_mul']

@[to_additive]
lemma inv_le_div_iff_le_mul' : a⁻¹ ≤ b / c ↔ c ≤ a * b :=
by rw [div_eq_mul_inv, inv_le_mul_inv_iff_le_mul]

@[to_additive]
lemma mul_inv_le : a * b⁻¹ ≤ c ↔ c⁻¹ * a ≤ b :=
by rw [← mul_le_mul_iff_left' c⁻¹, ← mul_le_mul_iff_right' b, ← mul_assoc, mul_left_inv,
      inv_mul_cancel_right, one_mul]

@[to_additive]
lemma div_le_left : a / b ≤ c ↔ c⁻¹ * a ≤ b :=
by rw [div_eq_mul_inv, mul_inv_le]

@[to_additive]
theorem le_mul_inv : a ≤ b * c⁻¹ ↔ c ≤ a⁻¹ * b :=
by rw [← mul_le_mul_iff_left' a⁻¹, ← mul_le_mul_iff_right' c, ← mul_assoc, mul_left_inv,
      inv_mul_cancel_right, one_mul]

@[to_additive]
theorem le_div_left : a ≤ b / c ↔ c ≤ a⁻¹ * b :=
by rw [div_eq_mul_inv, le_mul_inv]

/- The following lemmas are probably superfluous.  From here... -/
@[to_additive neg_le_neg]
lemma inv_le_inv' (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
inv_le_inv_iff.mpr h

@[to_additive]
lemma le_of_inv_le_inv (h : b⁻¹ ≤ a⁻¹) : a ≤ b :=
inv_le_inv_iff.mp h

@[to_additive]
lemma le_inv_of_le_inv (h : a ≤ b⁻¹) : b ≤ a⁻¹ :=
le_inv'.mp h

@[to_additive]
lemma inv_le_of_inv_le (h : a⁻¹ ≤ b) : b⁻¹ ≤ a :=
inv_le'.mp h
/- ...to here. -/

end le_left_right

section lt_left
variables [has_mul_lt_mul_left α]

@[simp, to_additive]
lemma inv_lt_one_iff_one_lt : a⁻¹ < 1 ↔ 1 < a :=
by rw [← mul_lt_mul_iff_left' a, mul_right_inv, mul_one]

@[to_additive neg_pos_iff_neg]
lemma one_lt_inv_iff_lt_one : 1 < a⁻¹ ↔ a < 1 :=
by rw [← mul_lt_mul_iff_left' a, mul_right_inv, mul_one]

@[simp, to_additive]
lemma self_mul_lt_iff (a : α) : a * b < a ↔ b < 1 :=
by rw [← mul_lt_mul_iff_left' a⁻¹, inv_mul_cancel_left, mul_left_inv]

@[simp, to_additive]
lemma div_lt_self_iff (a : α) : a / b < a ↔ 1 < b :=
by simp only [div_eq_mul_inv, inv_lt_one_iff_one_lt, self_mul_lt_iff]

alias sub_lt_self_iff ↔ _ sub_lt_self

/- The following lemmas are probably superfluous.  From here... -/
@[to_additive]
lemma one_lt_of_inv_inv (h : a⁻¹ < 1) : 1 < a :=
inv_lt_one_iff_one_lt.mp h

@[to_additive]
lemma inv_inv_of_one_lt (h : 1 < a) : a⁻¹ < 1 :=
inv_lt_one_iff_one_lt.mpr h

@[to_additive neg_of_neg_pos]
lemma inv_of_one_lt_inv (h : 1 < a⁻¹) : a < 1 :=
one_lt_inv_iff_lt_one.mp h

@[to_additive neg_pos_of_neg]
lemma one_lt_inv_of_inv (h : a < 1) : 1 < a⁻¹ :=
one_lt_inv_iff_lt_one.mpr h
/- ...to here. -/

end lt_left

section lt_left_right
variables [has_mul_lt_mul_left α] [has_mul_lt_mul_right α]

@[simp, to_additive]
lemma inv_lt_inv_iff : b⁻¹ < a⁻¹ ↔ a < b :=
by rwa [← mul_lt_mul_iff_left' a, ← mul_lt_mul_iff_right' b, inv_mul_cancel_right, mul_right_inv,
    one_mul]

@[to_additive]
lemma lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹ :=
by rw [← inv_lt_inv_iff, inv_inv]

@[to_additive]
lemma inv_lt_iff_inv_lt : a⁻¹ < b ↔ b⁻¹ < a :=
by rw [← inv_lt_inv_iff, inv_inv]

@[to_additive]
lemma mul_inv_lt_mul_inv (hab : a < b) (hcd : c < d) : a * d⁻¹ < b * c⁻¹ :=
calc a * d⁻¹ < b * d⁻¹ : (mul_lt_mul_iff_right' d⁻¹).mpr hab
         ... < b * c⁻¹ : has_mul_lt_mul_left.mul_lt_mul_left b (inv_lt_inv_iff.mpr hcd)

@[to_additive]
lemma div_lt_div'' (hab : a < b) (hcd : c < d) : a / d < b / c :=
by { rw [div_eq_mul_inv, div_eq_mul_inv], exact mul_inv_lt_mul_inv hab hcd }

@[simp, to_additive]
lemma div_lt_div_iff_left (a : α) : a / b < a / c ↔ c < b :=
by rw [div_eq_mul_inv, div_eq_mul_inv, mul_lt_mul_iff_left', inv_lt_inv_iff]

/- The following lemma is probably superfluous. -/
@[to_additive]
lemma div_lt_div_left'' (h : a < b) (c : α) : c / b < c / a :=
(div_lt_div_iff_left c).2 h

/- The primed versions of the same lemma, except that multiplication/addition on had been
commuted.  Since now there is no longer a commutativity assumption, I removed the other lemmas. -/
@[simp, to_additive]
lemma inv_lt_mul_inv_iff_lt_mul : b⁻¹ < a * c⁻¹ ↔ c < b * a :=
by rw [← mul_lt_mul_iff_left' b, ← mul_lt_mul_iff_right' c, mul_right_inv, one_mul,
      mul_assoc, mul_assoc a, mul_left_inv, mul_one]

/- The primed versions of the same lemma, except that multiplication/addition on had been
commuted.  Since now there is no longer a commutativity assumption, I removed the other lemmas. -/
@[simp, to_additive]
lemma inv_lt_div_iff_lt_mul : b⁻¹ < a / c ↔ c < b * a :=
by rw [div_eq_mul_inv, inv_lt_mul_inv_iff_lt_mul]

@[to_additive]
lemma mul_inv_lt : a * b⁻¹ < c ↔ c⁻¹ * a < b :=
by rw [← mul_lt_mul_iff_left' c⁻¹, ← mul_lt_mul_iff_right' b, mul_left_inv, one_mul,
      mul_assoc, mul_assoc a, mul_left_inv, mul_one]

@[to_additive]
lemma div_lt_left : a / b < c ↔ c⁻¹ * a < b :=
by rw [div_eq_mul_inv, mul_inv_lt]

@[to_additive]
theorem lt_mul_inv : a < b * c⁻¹ ↔ c < a⁻¹ * b :=
by rw [← mul_lt_mul_iff_left' a⁻¹, ← mul_lt_mul_iff_right' c, mul_left_inv, one_mul,
      mul_assoc, mul_assoc b, mul_left_inv, mul_one]

@[to_additive]
theorem lt_div_left : a < b / c ↔ c < a⁻¹ * b :=
by rw [div_eq_mul_inv, lt_mul_inv]

/- The following lemmas are probably superfluous.  From here... -/
@[to_additive neg_lt_neg]
lemma inv_lt_inv' (h : a < b) : b⁻¹ < a⁻¹ :=
inv_lt_inv_iff.mpr h

@[to_additive]
lemma lt_of_inv_lt_inv (h : b⁻¹ < a⁻¹) : a < b :=
inv_lt_inv_iff.mp h

@[to_additive]
lemma lt_inv_of_lt_inv (h : a < b⁻¹) : b < a⁻¹ :=
lt_inv_iff_lt_inv.mp h

@[to_additive]
lemma inv_lt_of_inv_lt (h : a⁻¹ < b) : b⁻¹ < a :=
inv_lt_iff_inv_lt.mp h
/- ...to here. -/

end lt_left_right
section le_right_lt_left_right
variables [has_mul_le_mul_right α] [has_mul_lt_mul_left α] [has_mul_lt_mul_right α]

@[to_additive]
lemma mul_inv_lt_mul_inv_of_le_of_lt (hab : a ≤ b) (hcd : c < d) : a * d⁻¹ < b * c⁻¹ :=
calc a * d⁻¹ ≤ b * d⁻¹ : mul_le_mul_right' hab d⁻¹
         ... < b * c⁻¹ : (mul_lt_mul_iff_left' _).mpr (inv_lt_inv' hcd)

@[to_additive]
lemma div_lt_div_of_le_of_lt (hab : a ≤ b) (hcd : c < d) : a / d < b / c :=
calc a / d = a * d⁻¹ : div_eq_mul_inv a d
       ... < b * c⁻¹ : mul_inv_lt_mul_inv_of_le_of_lt hab hcd
       ... = b / c   : (div_eq_mul_inv _ _).symm

end le_right_lt_left_right

section le_left_right_lt_right
variables [has_mul_le_mul_left α] [has_mul_le_mul_right α] [has_mul_lt_mul_right α]

@[to_additive]
lemma mul_inv_lt_mul_inv_of_lt_of_le (hab : a < b) (hcd : c ≤ d) : a * d⁻¹ < b * c⁻¹ :=
calc a * d⁻¹ < b * d⁻¹ : (mul_lt_mul_iff_right' d⁻¹).mpr hab
         ... ≤ b * c⁻¹ : (mul_le_mul_iff_left' _).mpr (inv_le_inv' hcd)

@[to_additive]
lemma div_lt_div_of_lt_of_le (hab : a < b) (hcd : c ≤ d) : a / d < b / c :=
calc a / d = a * d⁻¹ : div_eq_mul_inv a d
       ... < b * c⁻¹ : mul_inv_lt_mul_inv_of_lt_of_le hab hcd
       ... = b / c   : (div_eq_mul_inv _ _).symm

end le_left_right_lt_right

end preorder

end group


/-
section partial_order
variables [partial_order α]

@[priority 99, to_additive]
instance group.has_mul_le_mul_left.to_has_mul_lt_mul_left [has_mul_le_mul_left α] :
  has_mul_lt_mul_left α :=
{ mul_lt_mul_left := λ a b c bc, mul_lt_mul_left' bc a }

@[priority 101, to_additive]
instance group.has_mul_le_mul_right.to_has_mul_lt_mul_right [has_mul_le_mul_right α] :
  has_mul_lt_mul_right α :=
{ mul_lt_mul_right := λ a b c bc, mul_lt_mul_right' bc a }

end partial_order
-/

section comm_group
variables [comm_group α] [preorder α]

section le_left
variable [has_mul_le_mul_left α]

@[to_additive]
lemma inv_mul_le_iff_le_mul : c⁻¹ * a ≤ b ↔ a ≤ b * c :=
by rw [inv_mul_le_iff'', mul_comm]

@[to_additive]
lemma inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a :=
(inv_le_one'.2 h).trans h

@[to_additive]
lemma self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ :=
le_trans h (one_le_inv'.2 h)

@[to_additive neg_le_iff_add_nonneg]
lemma inv_le_iff_one_le_mul : a⁻¹ ≤ b ↔ 1 ≤ b * a :=
(mul_le_mul_iff_right' a).symm.trans $ by rw inv_mul_self

@[simp, to_additive]
lemma mul_inv_le_iff_le_mul' : a * b⁻¹ ≤ c ↔ a ≤ b * c :=
by rw [mul_inv_le_iff'', mul_comm]

@[to_additive]
lemma inv_mul_le_iff_le_mul' : c⁻¹ * a ≤ b ↔ a ≤ b * c :=
by rw [inv_mul_le_iff_le_mul, mul_comm]

@[to_additive add_neg_le_add_neg_iff]
lemma mul_inv_le_mul_inv_iff' : a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b :=
by rw [mul_comm c, mul_inv_le_inv_mul_iff, mul_comm]

@[to_additive sub_le_sub_iff]
lemma div_le_div_iff' : a / b ≤ c / d ↔ a * d ≤ c * b :=
by rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_le_mul_inv_iff']

@[to_additive]
lemma div_le : a / b ≤ c ↔ a / c ≤ b :=
by rw [div_le_left, mul_comm, div_eq_mul_inv]

@[to_additive]
theorem le_div : a ≤ b / c ↔ c ≤ b / a :=
by rw [le_div_left, mul_comm, div_eq_mul_inv]

@[simp, to_additive]
lemma inv_le_div_iff_le_mul : b⁻¹ ≤ a / c ↔ c ≤ a * b :=
by rw [inv_le_div_iff_le_mul_left, mul_comm]

@[to_additive]
lemma div_le_iff_le_mul' : a / b ≤ c ↔ a ≤ b * c :=
by rw [mul_comm, div_le_iff_le_mul]

@[to_additive]
lemma le_div_iff_mul_le' : b ≤ c / a ↔ a * b ≤ c :=
by rw [mul_comm, le_div_iff_mul_le]

/- The following lemmas are probably superfluous.  From here... -/
@[to_additive]
lemma inv_mul_le_right_of_le_mul (h : a ≤ b * c) : c⁻¹ * a ≤ b :=
inv_mul_le_iff_le_mul.mpr h

@[to_additive]
lemma le_mul_of_inv_mul_le_right (h : c⁻¹ * a ≤ b) : a ≤ b * c :=
inv_mul_le_iff_le_mul.mp h
/- ...to here. -/

end le_left

section lt_left
variable [has_mul_lt_mul_left α]

@[to_additive]
lemma lt_mul_of_inv_mul_lt_right (h : c⁻¹ * a < b) : a < b * c :=
by { rw mul_comm, exact lt_mul_of_inv_mul_lt h }

@[to_additive]
lemma inv_mul_lt_right_of_lt_mul (h : a < b * c) : c⁻¹ * a < b :=
by { rw mul_comm at h, exact inv_mul_lt_of_lt_mul h }

@[to_additive]
lemma inv_lt_iff_one_lt_mul : a⁻¹ < b ↔ 1 < b * a :=
by rw [inv_lt_iff_one_lt_mul', mul_comm]

@[to_additive]
lemma lt_inv_iff_mul_lt_one : a < b⁻¹ ↔ a * b < 1 :=
by rw [lt_inv_iff_mul_lt_one', mul_comm]

@[to_additive]
lemma inv_lt_self (h : 1 < a) : a⁻¹ < a :=
(inv_lt_one_iff_one_lt.mpr h).trans h

@[to_additive]
lemma inv_mul_lt_iff_lt_mul_right : c⁻¹ * a < b ↔ a < b * c :=
by rw [inv_mul_lt_iff'', mul_comm]

@[to_additive]
lemma div_lt : a / b < c ↔ a / c < b :=
by rw [div_lt_left, mul_comm, div_eq_mul_inv]

@[to_additive]
theorem lt_div : a < b / c ↔ c < b / a :=
by rw [lt_div_left, mul_comm, div_eq_mul_inv]

@[to_additive]
lemma lt_div_iff_mul_lt' : b < c / a ↔ a * b < c :=
by rw [mul_comm, lt_div_iff_mul_lt]

@[to_additive]
lemma div_lt_iff_mul : c / a < b ↔ c < a * b :=
by rw [mul_comm, div_lt_iff_lt_mul']

@[simp, to_additive]
lemma div_lt_iff_lt_mul : a / b < c ↔ a < b * c :=
by rw [mul_comm, div_lt_iff_lt_mul']

/- The following lemmas are probably superfluous.  From here... -/
@[to_additive neg_lt_zero]
lemma inv_lt_one' : a⁻¹ < 1 ↔ 1 < a :=
inv_lt_one_iff_one_lt

@[to_additive neg_pos]
lemma one_lt_inv' : 1 < a⁻¹ ↔ a < 1 :=
one_lt_inv_iff_lt_one

@[to_additive neg_lt]
lemma inv_lt' : a⁻¹ < b ↔ b⁻¹ < a :=
inv_lt_iff_inv_lt

@[to_additive lt_neg]
lemma lt_inv' : a < b⁻¹ ↔ b < a⁻¹ :=
lt_inv_iff_lt_inv
/- ...to here. -/

/-- Pullback an `ordered_comm_group` under an injective map. -/
@[to_additive function.injective.ordered_add_comm_group
"Pullback an `ordered_add_comm_group` under an injective map."]
def function.injective.ordered_comm_group {α β : Type*}
  [comm_group α] [partial_order α] [has_mul_le_mul_left α]
  [has_one β] [has_mul β] [has_inv β] [has_div β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) :
  ordered_comm_group β :=
{ mul_le_mul_left := λ a b ab c, begin
      change f (c * a) ≤ f (c * b),
      rw [mul, mul],
      exact has_mul_le_mul_left.mul_le_mul_left _ ab
    end,
  ..partial_order.lift f hf,
  ..hf.comm_group f one mul inv div }

end lt_left

end comm_group

/-!

### Linearly ordered commutative groups

-/

/-- A linearly ordered additive commutative group is an
additive commutative group with a linear order in which
addition is monotone. -/
@[protect_proj, ancestor add_comm_group linear_order]
class linear_ordered_add_comm_group (α : Type u) extends add_comm_group α, linear_order α :=
(add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined.` -/
@[protect_proj, ancestor linear_ordered_add_comm_monoid_with_top sub_neg_monoid nontrivial]
class linear_ordered_add_comm_group_with_top (α : Type*)
  extends linear_ordered_add_comm_monoid_with_top α, sub_neg_monoid α, nontrivial α :=
(neg_top : - (⊤ : α) = ⊤)
(add_neg_cancel : ∀ a:α, a ≠ ⊤ → a + (- a) = 0)

/-- A linearly ordered commutative group is a
commutative group with a linear order in which
multiplication is monotone. -/
@[protect_proj, ancestor comm_group linear_order, to_additive]
class linear_ordered_comm_group (α : Type u) extends comm_group α, linear_order α :=
(mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)

section linear_ordered_comm_group
variable [linear_ordered_comm_group α]

@[priority 100, to_additive] -- see Note [lower instance priority]
instance linear_ordered_comm_group.to_ordered_comm_group : ordered_comm_group α :=
{ ..‹linear_ordered_comm_group α› }

@[priority 100, to_additive] -- see Note [lower instance priority]
instance linear_ordered_comm_group.to_linear_ordered_cancel_comm_monoid :
  linear_ordered_cancel_comm_monoid α :=
{ le_of_mul_le_mul_left := λ x y z, le_of_mul_le_mul_left',
  mul_left_cancel := λ x y z, mul_left_cancel,
  ..‹linear_ordered_comm_group α› }

/-- Pullback a `linear_ordered_comm_group` under an injective map. -/
@[to_additive function.injective.linear_ordered_add_comm_group
"Pullback a `linear_ordered_add_comm_group` under an injective map."]
def function.injective.linear_ordered_comm_group {β : Type*}
  [has_one β] [has_mul β] [has_inv β] [has_div β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y)  :
  linear_ordered_comm_group β :=
{ ..linear_order.lift f hf,
  ..hf.ordered_comm_group f one mul inv div }

@[to_additive linear_ordered_add_comm_group.add_lt_add_left]
lemma linear_ordered_comm_group.mul_lt_mul_left'
  (a b : α) (h : a < b) (c : α) : c * a < c * b :=
mul_lt_mul_left' h c

@[to_additive min_neg_neg]
lemma min_inv_inv' (a b : α) : min (a⁻¹) (b⁻¹) = (max a b)⁻¹ :=
eq.symm $ @monotone.map_max α (order_dual α) _ _ has_inv.inv a b $ λ a b, inv_le_inv'

@[to_additive max_neg_neg]
lemma max_inv_inv' (a b : α) : max (a⁻¹) (b⁻¹) = (min a b)⁻¹ :=
eq.symm $ @monotone.map_min α (order_dual α) _ _ has_inv.inv a b $ λ a b, inv_le_inv'

@[to_additive min_sub_sub_right]
lemma min_div_div_right' (a b c : α) : min (a / c) (b / c) = min a b / c :=
by simpa only [div_eq_mul_inv] using min_mul_mul_right a b (c⁻¹)

@[to_additive max_sub_sub_right]
lemma max_div_div_right' (a b c : α) : max (a / c) (b / c) = max a b / c :=
by simpa only [div_eq_mul_inv] using max_mul_mul_right a b (c⁻¹)

@[to_additive min_sub_sub_left]
lemma min_div_div_left' (a b c : α) : min (a / b) (a / c) = a / max b c :=
by simp only [div_eq_mul_inv, min_mul_mul_left, min_inv_inv']

@[to_additive max_sub_sub_left]
lemma max_div_div_left' (a b c : α) : max (a / b) (a / c) = a / min b c :=
by simp only [div_eq_mul_inv, max_mul_mul_left, max_inv_inv']

@[to_additive max_zero_sub_eq_self]
lemma max_one_div_eq_self' (a : α) : max a 1 / max (a⁻¹) 1 = a :=
begin
  rcases le_total a 1,
  { rw [max_eq_right h, max_eq_left, one_div, inv_inv], { rwa [le_inv', one_inv] } },
  { rw [max_eq_left, max_eq_right, div_eq_mul_inv, one_inv, mul_one],
    { rwa [inv_le', one_inv] }, exact h }
end

@[to_additive eq_zero_of_neg_eq]
lemma eq_one_of_inv_eq' (h : a⁻¹ = a) : a = 1 :=
match lt_trichotomy a 1 with
| or.inl h₁ :=
  have 1 < a, from h ▸ one_lt_inv_of_inv h₁,
  absurd h₁ this.asymm
| or.inr (or.inl h₁) := h₁
| or.inr (or.inr h₁) :=
  have a < 1, from h ▸ inv_inv_of_one_lt h₁,
  absurd h₁ this.asymm
end

@[to_additive exists_zero_lt]
lemma exists_one_lt' [nontrivial α] : ∃ (a:α), 1 < a :=
begin
  obtain ⟨y, hy⟩ := decidable.exists_ne (1 : α),
  cases hy.lt_or_lt,
  { exact ⟨y⁻¹, one_lt_inv'.mpr h⟩ },
  { exact ⟨y, h⟩ }
end

@[priority 100, to_additive] -- see Note [lower instance priority]
instance linear_ordered_comm_group.to_no_top_order [nontrivial α] :
  no_top_order α :=
⟨ begin
    obtain ⟨y, hy⟩ : ∃ (a:α), 1 < a := exists_one_lt',
    exact λ a, ⟨a * y, lt_mul_of_one_lt_right' a hy⟩
  end ⟩

@[priority 100, to_additive] -- see Note [lower instance priority]
instance linear_ordered_comm_group.to_no_bot_order [nontrivial α] : no_bot_order α :=
⟨ begin
    obtain ⟨y, hy⟩ : ∃ (a:α), 1 < a := exists_one_lt',
    exact λ a, ⟨a / y, (div_lt_self_iff a).mpr hy⟩
  end ⟩

end linear_ordered_comm_group

section linear_ordered_add_comm_group

variables [linear_ordered_add_comm_group α]

@[simp]
lemma sub_le_sub_flip : a - b ≤ b - a ↔ a ≤ b :=
begin
  rw [sub_le_iff_le_add, sub_add_eq_add_sub, le_sub_iff_add_le],
  split,
  { intro h,
    by_contra H,
    rw not_le at H,
    apply not_lt.2 h,
    exact add_lt_add H H, },
  { intro h,
    exact add_le_add h h, }
end

lemma le_of_forall_pos_le_add [densely_ordered α] (h : ∀ ε : α, 0 < ε → a ≤ b + ε) : a ≤ b :=
le_of_forall_le_of_dense $ λ c hc,
calc a ≤ b + (c - b) : h _ (sub_pos_of_lt hc)
   ... = c           : add_sub_cancel'_right _ _

lemma le_iff_forall_pos_le_add [densely_ordered α] : a ≤ b ↔ ∀ ε, 0 < ε → a ≤ b + ε :=
⟨λ h ε ε_pos, le_add_of_le_of_nonneg h ε_pos.le, le_of_forall_pos_le_add⟩

lemma le_of_forall_pos_lt_add (h : ∀ ε : α, 0 < ε → a < b + ε) : a ≤ b :=
le_of_not_lt $ λ h₁, by simpa using h _ (sub_pos_of_lt h₁)

lemma le_iff_forall_pos_lt_add : a ≤ b ↔ ∀ ε, 0 < ε → a < b + ε :=
⟨λ h ε, lt_add_of_le_of_pos h, le_of_forall_pos_lt_add⟩

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

lemma abs_le' : abs a ≤ b ↔ a ≤ b ∧ -a ≤ b := max_le_iff

lemma abs_le : abs a ≤ b ↔ - b ≤ a ∧ a ≤ b :=
by rw [abs_le', and.comm, neg_le]

lemma neg_le_of_abs_le (h : abs a ≤ b) : -b ≤ a := (abs_le.mp h).1

lemma le_of_abs_le (h : abs a ≤ b) : a ≤ b := (abs_le.mp h).2

lemma le_abs : a ≤ abs b ↔ a ≤ b ∨ a ≤ -b := le_max_iff

lemma le_abs_self (a : α) : a ≤ abs a := le_max_left _ _

lemma neg_le_abs_self (a : α) : -a ≤ abs a := le_max_right _ _

lemma abs_nonneg (a : α) : 0 ≤ abs a :=
(le_total 0 a).elim (λ h, h.trans (le_abs_self a)) (λ h, (neg_nonneg.2 h).trans $ neg_le_abs_self a)

@[simp] lemma abs_abs (a : α) : abs (abs a) = abs a :=
abs_of_nonneg $ abs_nonneg a

@[simp] lemma abs_eq_zero : abs a = 0 ↔ a = 0 :=
decidable.not_iff_not.1 $ ne_comm.trans $ (abs_nonneg a).lt_iff_ne.symm.trans abs_pos

@[simp] lemma abs_nonpos_iff {a : α} : abs a ≤ 0 ↔ a = 0 :=
(abs_nonneg a).le_iff_eq.trans abs_eq_zero

lemma abs_lt : abs a < b ↔ - b < a ∧ a < b :=
max_lt_iff.trans $ and.comm.trans $ by rw [neg_lt]

lemma neg_lt_of_abs_lt (h : abs a < b) : -b < a := (abs_lt.mp h).1

lemma lt_of_abs_lt (h : abs a < b) : a < b := (abs_lt.mp h).2

lemma lt_abs : a < abs b ↔ a < b ∨ a < -b := lt_max_iff

lemma max_sub_min_eq_abs' (a b : α) : max a b - min a b = abs (a - b) :=
begin
  cases le_total a b with ab ba,
  { rw [max_eq_right ab, min_eq_left ab, abs_of_nonpos, neg_sub], rwa sub_nonpos },
  { rw [max_eq_left ba, min_eq_right ba, abs_of_nonneg], rwa sub_nonneg }
end

lemma max_sub_min_eq_abs (a b : α) : max a b - min a b = abs (b - a) :=
by { rw [abs_sub], exact max_sub_min_eq_abs' _ _ }

lemma abs_add (a b : α) : abs (a + b) ≤ abs a + abs b :=
abs_le.2 ⟨(neg_add (abs a) (abs b)).symm ▸
  add_le_add (neg_le.2 $ neg_le_abs_self _) (neg_le.2 $ neg_le_abs_self _),
  add_le_add (le_abs_self _) (le_abs_self _)⟩

lemma abs_sub_le_iff : abs (a - b) ≤ c ↔ a - b ≤ c ∧ b - a ≤ c :=
begin
  rw [abs_le, neg_le_sub_iff_le_add_left, @sub_le_iff_le_add_left _ _ b, and_comm,
    and.congr_right_iff, sub_le_iff_le_add_left, iff_self, implies_true_iff],
  exact trivial,
end

lemma abs_sub_lt_iff : abs (a - b) < c ↔ a - b < c ∧ b - a < c :=
begin
  rwa [abs_lt, neg_lt_sub_iff_lt_add, @sub_lt_iff_lt_add' _ _ b, and_comm, and.congr_right_iff,
    sub_lt_iff_lt_add', iff_self, implies_true_iff],
  exact trivial,
end

lemma sub_le_of_abs_sub_le_left (h : abs (a - b) ≤ c) : b - c ≤ a :=
sub_le.1 (abs_sub_le_iff.1 h).2

lemma sub_le_of_abs_sub_le_right (h : abs (a - b) ≤ c) : a - c ≤ b :=
sub_le_of_abs_sub_le_left (abs_sub a b ▸ h)

lemma sub_lt_of_abs_sub_lt_left (h : abs (a - b) < c) : b - c < a :=
sub_lt.1 (abs_sub_lt_iff.1 h).2

lemma sub_lt_of_abs_sub_lt_right (h : abs (a - b) < c) : a - c < b :=
sub_lt_of_abs_sub_lt_left (abs_sub a b ▸ h)

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

instance with_top.linear_ordered_add_comm_group_with_top :
  linear_ordered_add_comm_group_with_top (with_top α) :=
{ neg := option.map (λ a : α, -a),
  neg_top := @option.map_none _ _ (λ a : α, -a),
  add_neg_cancel := begin
    rintro (a | a) ha,
    { exact (ha rfl).elim },
    exact with_top.coe_add.symm.trans (with_top.coe_eq_coe.2 (add_neg_self a)),
  end,
  .. with_top.linear_ordered_add_comm_monoid_with_top,
  .. option.nontrivial }

end linear_ordered_add_comm_group

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
A `nonneg_add_comm_group` is a `linear_ordered_add_comm_group`
if `nonneg` is total and decidable.
-/
def to_linear_ordered_add_comm_group
  [decidable_pred (@nonneg α _)]
  (nonneg_total : ∀ a : α, nonneg a ∨ nonneg (-a))
  : linear_ordered_add_comm_group α :=
{ le := (≤),
  lt := (<),
  le_total := nonneg_total_iff.1 nonneg_total,
  decidable_le := by apply_instance,
  decidable_lt := by apply_instance,
  ..@nonneg_add_comm_group.to_ordered_add_comm_group _ s }

end nonneg_add_comm_group

namespace order_dual

instance [ordered_add_comm_group α] : ordered_add_comm_group (order_dual α) :=
{ add_left_neg := λ a : α, add_left_neg a,
  sub := λ a b, (a - b : α),
  ..order_dual.ordered_add_comm_monoid,
  ..show add_comm_group α, by apply_instance }

instance [linear_ordered_add_comm_group α] :
  linear_ordered_add_comm_group (order_dual α) :=
{ add_le_add_left := λ a b h c, @add_le_add_left α b a _ _ _ h _,
  ..order_dual.linear_order α,
  ..show add_comm_group α, by apply_instance }

end order_dual

namespace prod

variables {G H : Type*}

@[to_additive]
instance [ordered_comm_group G] [ordered_comm_group H] :
  ordered_comm_group (G × H) :=
{ .. prod.comm_group, .. prod.partial_order G H, .. prod.ordered_cancel_comm_monoid }

end prod

section type_tags

instance [ordered_add_comm_group α] : ordered_comm_group (multiplicative α) :=
{ ..multiplicative.comm_group,
  ..multiplicative.ordered_comm_monoid }

instance [ordered_comm_group α] : ordered_add_comm_group (additive α) :=
{ ..additive.add_comm_group,
  ..additive.ordered_add_comm_monoid }

instance [linear_ordered_add_comm_group α] : linear_ordered_comm_group (multiplicative α) :=
{ ..multiplicative.linear_order,
  ..multiplicative.ordered_comm_group }

instance [linear_ordered_comm_group α] : linear_ordered_add_comm_group (additive α) :=
{ ..additive.linear_order,
  ..additive.ordered_add_comm_group }

end type_tags

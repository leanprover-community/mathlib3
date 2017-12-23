/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Various multiplicative and additive structures.
-/


section pending_1857

/- Transport multiplicative to additive -/
section transport
open tactic

@[user_attribute]
meta def to_additive_attr : user_attribute (name_map name) name :=
{ name      := `to_additive,
  descr     := "Transport multiplicative to additive",
  cache_cfg := ⟨λ ns, ns.mfoldl (λ dict n, do
    val ← to_additive_attr.get_param n,
    pure $ dict.insert n val) mk_name_map, []⟩,
  parser    := lean.parser.ident,
  after_set := some $ λ src _ _, do
    env ← get_env,
    dict ← to_additive_attr.get_cache,
    tgt ← to_additive_attr.get_param src,
    (get_decl tgt >> skip) <|>
      transport_with_dict dict src tgt }

end transport

/- map operations -/
attribute [to_additive has_add.add] has_mul.mul
attribute [to_additive has_zero.zero] has_one.one
attribute [to_additive has_neg.neg] has_inv.inv
attribute [to_additive has_add] has_mul
attribute [to_additive has_zero] has_one
attribute [to_additive has_neg] has_inv

/- map constructors -/
attribute [to_additive has_add.mk] has_mul.mk
attribute [to_additive has_zero.mk] has_one.mk
attribute [to_additive has_neg.mk] has_neg.mk

/- map structures -/
attribute [to_additive add_semigroup] semigroup
attribute [to_additive add_semigroup.mk] semigroup.mk
attribute [to_additive add_semigroup.to_has_add] semigroup.to_has_mul
attribute [to_additive add_semigroup.add_assoc] semigroup.mul_assoc

attribute [to_additive add_comm_semigroup] comm_semigroup
attribute [to_additive add_comm_semigroup.mk] comm_semigroup.mk
attribute [to_additive add_comm_semigroup.to_add_semigroup] comm_semigroup.to_semigroup
attribute [to_additive add_comm_semigroup.add_comm] comm_semigroup.mul_comm

attribute [to_additive add_left_cancel_semigroup] left_cancel_semigroup
attribute [to_additive add_left_cancel_semigroup.mk] left_cancel_semigroup.mk
attribute [to_additive add_left_cancel_semigroup.to_add_semigroup] left_cancel_semigroup.to_semigroup
attribute [to_additive add_left_cancel_semigroup.add_left_cancel] left_cancel_semigroup.mul_left_cancel

attribute [to_additive add_right_cancel_semigroup] right_cancel_semigroup
attribute [to_additive add_right_cancel_semigroup.mk] right_cancel_semigroup.mk
attribute [to_additive add_right_cancel_semigroup.to_add_semigroup] right_cancel_semigroup.to_semigroup
attribute [to_additive add_right_cancel_semigroup.add_right_cancel] right_cancel_semigroup.mul_right_cancel

attribute [to_additive add_monoid] monoid
attribute [to_additive add_monoid.mk] monoid.mk
attribute [to_additive add_monoid.to_has_zero] monoid.to_has_one
attribute [to_additive add_monoid.to_add_semigroup] monoid.to_semigroup
attribute [to_additive add_monoid.zero_add] monoid.one_mul
attribute [to_additive add_monoid.add_zero] monoid.mul_one

attribute [to_additive add_comm_monoid] comm_monoid
attribute [to_additive add_comm_monoid.mk] comm_monoid.mk
attribute [to_additive add_comm_monoid.to_add_monoid] comm_monoid.to_monoid
attribute [to_additive add_comm_monoid.to_add_comm_semigroup] comm_monoid.to_comm_semigroup

attribute [to_additive add_group] group
attribute [to_additive add_group.mk] group.mk
attribute [to_additive add_group.to_has_neg] group.to_has_inv
attribute [to_additive add_group.to_add_monoid] group.to_monoid
attribute [to_additive add_group.add_left_neg] group.mul_left_inv
attribute [to_additive add_group.add] group.mul
attribute [to_additive add_group.add_assoc] group.mul_assoc

attribute [to_additive add_comm_group] comm_group
attribute [to_additive add_comm_group.mk] comm_group.mk
attribute [to_additive add_comm_group.to_add_group] comm_group.to_group
attribute [to_additive add_comm_group.to_add_comm_monoid] comm_group.to_comm_monoid

/- map theorems -/
attribute [to_additive add_assoc] mul_assoc
attribute [to_additive add_semigroup_to_is_associative] semigroup_to_is_associative
attribute [to_additive add_comm] mul_comm
attribute [to_additive add_comm_semigroup_to_is_commutative] comm_semigroup_to_is_commutative
attribute [to_additive add_left_comm] mul_left_comm
attribute [to_additive add_right_comm] mul_right_comm
attribute [to_additive add_left_cancel] mul_left_cancel
attribute [to_additive add_right_cancel] mul_right_cancel
attribute [to_additive add_left_cancel_iff] mul_left_cancel_iff
attribute [to_additive add_right_cancel_iff] mul_right_cancel_iff
attribute [to_additive zero_add] one_mul
attribute [to_additive add_zero] mul_one
attribute [to_additive add_left_neg] mul_left_inv
attribute [to_additive neg_add_self] inv_mul_self
attribute [to_additive neg_add_cancel_left] inv_mul_cancel_left
attribute [to_additive neg_add_cancel_right] inv_mul_cancel_right
attribute [to_additive neg_eq_of_add_eq_zero] inv_eq_of_mul_eq_one
attribute [to_additive neg_zero] one_inv
attribute [to_additive neg_neg] inv_inv
attribute [to_additive add_right_neg] mul_right_inv
attribute [to_additive add_neg_self] mul_inv_self
attribute [to_additive neg_inj] inv_inj
attribute [to_additive add_group.add_left_cancel] group.mul_left_cancel
attribute [to_additive add_group.add_right_cancel] group.mul_right_cancel
attribute [to_additive add_group.to_left_cancel_add_semigroup] group.to_left_cancel_semigroup
attribute [to_additive add_group.to_right_cancel_add_semigroup] group.to_right_cancel_semigroup
attribute [to_additive add_neg_cancel_left] mul_inv_cancel_left
attribute [to_additive add_neg_cancel_right] mul_inv_cancel_right
attribute [to_additive neg_add_rev] mul_inv_rev
attribute [to_additive eq_neg_of_eq_neg] eq_inv_of_eq_inv
attribute [to_additive eq_neg_of_add_eq_zero] eq_inv_of_mul_eq_one
attribute [to_additive eq_add_neg_of_add_eq] eq_mul_inv_of_mul_eq
attribute [to_additive eq_neg_add_of_add_eq] eq_inv_mul_of_mul_eq
attribute [to_additive neg_add_eq_of_eq_add] inv_mul_eq_of_eq_mul
attribute [to_additive add_neg_eq_of_eq_add] mul_inv_eq_of_eq_mul
attribute [to_additive eq_add_of_add_neg_eq] eq_mul_of_mul_inv_eq
attribute [to_additive eq_add_of_neg_add_eq] eq_mul_of_inv_mul_eq
attribute [to_additive add_eq_of_eq_neg_add] mul_eq_of_eq_inv_mul
attribute [to_additive add_eq_of_eq_add_neg] mul_eq_of_eq_mul_inv
attribute [to_additive neg_add] mul_inv

end pending_1857

universe u
variables {α : Type u}

@[simp, to_additive add_left_inj]
theorem mul_left_inj [left_cancel_semigroup α] {a b c : α} : a * b = a * c ↔ b = c :=
⟨mul_left_cancel, congr_arg _⟩

@[simp, to_additive add_right_inj]
theorem mul_right_inj [right_cancel_semigroup α] {a b c : α} : b * a = c * a ↔ b = c :=
⟨mul_right_cancel, congr_arg _⟩

section group
  variables [group α] {a b c : α}

  @[simp, to_additive neg_inj']
  theorem inv_inj' : a⁻¹ = b⁻¹ ↔ a = b :=
  ⟨λ h, by rw ← inv_inv a; simp [h], congr_arg _⟩

  @[to_additive eq_of_neg_eq_neg]
  theorem eq_of_inv_eq_inv : a⁻¹ = b⁻¹ → a = b :=
  inv_inj'.1

  @[simp, to_additive add_self_iff_eq_zero]
  theorem mul_self_iff_eq_one : a * a = a ↔ a = 1 :=
  by have := @mul_left_inj _ _ a a 1; rwa mul_one at this

  @[simp, to_additive neg_eq_zero]
  theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
  by rw [← @inv_inj' _ _ a 1, one_inv]

  @[simp, to_additive neg_ne_zero]
  theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
  not_congr inv_eq_one

  @[to_additive left_inverse_neg]
  theorem left_inverse_inv (α) [group α] :
    function.left_inverse (λ a : α, a⁻¹) (λ a, a⁻¹) :=
  assume a, inv_inv a

  attribute [simp] mul_inv_cancel_left add_neg_cancel_left
                   mul_inv_cancel_right add_neg_cancel_right

  @[to_additive eq_neg_iff_eq_neg]
  theorem eq_inv_iff_eq_inv : a = b⁻¹ ↔ b = a⁻¹ :=
  ⟨eq_inv_of_eq_inv, eq_inv_of_eq_inv⟩

  @[to_additive neg_eq_iff_neg_eq]
  theorem inv_eq_iff_inv_eq : a⁻¹ = b ↔ b⁻¹ = a :=
  by rw [eq_comm, @eq_comm _ _ a, eq_inv_iff_eq_inv]

  @[to_additive add_eq_zero_iff_eq_neg]
  theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
  have a * b = b⁻¹ * b ↔ a = b⁻¹, from mul_right_inj,
  by rwa mul_left_inv at this

  @[to_additive add_eq_zero_iff_neg_eq]
  theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b :=
  by rw [mul_eq_one_iff_eq_inv, eq_inv_iff_eq_inv, eq_comm]

  @[to_additive eq_neg_iff_add_eq_zero]
  theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
  mul_eq_one_iff_eq_inv.symm

  @[to_additive neg_eq_iff_add_eq_zero]
  theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 :=
  mul_eq_one_iff_inv_eq.symm

  @[to_additive eq_add_neg_iff_add_eq]
  theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
  ⟨λ h, by simp [h], λ h, by simp [h.symm]⟩

  @[to_additive eq_neg_add_iff_add_eq]
  theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
  ⟨λ h, by simp [h], λ h, by simp [h.symm]⟩

  @[to_additive neg_add_eq_iff_eq_add]
  theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
  ⟨λ h, by simp [h.symm], λ h, by simp [h]⟩

  @[to_additive add_neg_eq_iff_eq_add]
  theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
  ⟨λ h, by simp [h.symm], λ h, by simp [h]⟩

  @[to_additive add_neg_eq_zero]
  theorem mul_inv_eq_one {a b : α} : a * b⁻¹ = 1 ↔ a = b :=
  by rw [mul_eq_one_iff_eq_inv, inv_inv]

  @[to_additive neg_comm_of_comm]
  theorem inv_comm_of_comm {a b : α} (H : a * b = b * a) : a⁻¹ * b = b * a⁻¹ :=
  begin
    have : a⁻¹ * (b * a) * a⁻¹ = a⁻¹ * (a * b) * a⁻¹ :=
      congr_arg (λ x:α, a⁻¹ * x * a⁻¹) H.symm,
    rwa [mul_assoc, mul_assoc, mul_inv_self, mul_one,
        ← mul_assoc, inv_mul_self, one_mul] at this; exact h
  end
end group

section add_monoid
  variables [add_monoid α] {a b c : α}

  @[simp] lemma bit0_zero : bit0 0 = 0 := add_zero _
  @[simp] lemma bit1_zero : bit1 0 = 1 := add_zero _
end add_monoid

section add_group
  variables [add_group α] {a b c : α}

  local attribute [simp] sub_eq_add_neg

  @[simp] lemma sub_left_inj : a - b = a - c ↔ b = c :=
  add_left_inj.trans neg_inj'

  @[simp] lemma sub_right_inj : b - a = c - a ↔ b = c :=
  add_right_inj

  lemma sub_add_sub_cancel (a b c : α) : (a - b) + (b - c) = a - c :=
  by simp

  lemma sub_sub_sub_cancel_right (a b c : α) : (a - c) - (b - c) = a - b :=
  by simp

  theorem sub_eq_zero : a - b = 0 ↔ a = b :=
  ⟨eq_of_sub_eq_zero, λ h, by simp [h]⟩

  theorem sub_ne_zero : a - b ≠ 0 ↔ a ≠ b :=
  not_congr sub_eq_zero

  theorem eq_sub_iff_add_eq : a = b - c ↔ a + c = b :=
  by split; intro h; simp [h, eq_add_neg_iff_add_eq]

  theorem sub_eq_iff_eq_add : a - b = c ↔ a = c + b :=
  by split; intro h; simp [*, add_neg_eq_iff_eq_add] at *

  theorem eq_iff_eq_of_sub_eq_sub {a b c d : α} (H : a - b = c - d) : a = b ↔ c = d :=
  by rw [← sub_eq_zero, H, sub_eq_zero]

  theorem left_inverse_sub_add_left (c : α) : function.left_inverse (λ x, x - c) (λ x, x + c) :=
  assume x, add_sub_cancel x c

  theorem left_inverse_add_left_sub (c : α) : function.left_inverse (λ x, x + c) (λ x, x - c) :=
  assume x, sub_add_cancel x c

  theorem left_inverse_add_right_neg_add (c : α) :
      function.left_inverse (λ x, c + x) (λ x, - c + x) :=
  assume x, add_neg_cancel_left c x

  theorem left_inverse_neg_add_add_right (c : α) :
      function.left_inverse (λ x, - c + x) (λ x, c + x) :=
  assume x, neg_add_cancel_left c x
end add_group

section add_comm_group
  variables [add_comm_group α] {a b c : α}

  lemma sub_eq_neg_add (a b : α) : a - b = -b + a :=
  by simp

  theorem neg_add' (a b : α) : -(a + b) = -a - b := neg_add a b

  lemma eq_sub_iff_add_eq' : a = b - c ↔ c + a = b :=
  by rw [eq_sub_iff_add_eq, add_comm]

  lemma sub_eq_iff_eq_add' : a - b = c ↔ a = b + c :=
  by rw [sub_eq_iff_eq_add, add_comm]

  lemma add_sub_cancel' (a b : α) : a + b - a = b :=
  by simp

  lemma add_sub_cancel'_right (a b : α) : a + (b - a) = b :=
  by rw [← add_sub_assoc, add_sub_cancel']

  lemma sub_sub_swap (a b c : α) : a - b - c = a - c - b :=
  by simp

  lemma sub_sub_sub_cancel_left (a b c : α) : (c - a) - (c - b) = b - a :=
  by simp

end add_comm_group

section ordered_comm_group
variables [ordered_comm_group α]

theorem le_sub_iff_add_le {a b c : α} : a ≤ b - c ↔ a + c ≤ b :=
by rw [add_comm]; exact ⟨add_le_of_le_sub_left, le_sub_left_of_add_le⟩

theorem sub_le_iff_le_add {a b c : α} : a - c ≤ b ↔ a ≤ b + c :=
by rw [add_comm]; exact ⟨le_add_of_sub_left_le, sub_left_le_of_le_add⟩

end ordered_comm_group

section morphisms
variables { β : Type*} [group α] [group β] {a b : α}

@[simp]
def is_mph (f : α → β) : Prop :=
∀ a b : α, f(a*b) = f(a)*f(b)

@[simp]
lemma mph_one { f : α → β } (H : is_mph f) : f 1 = 1 :=
mul_self_iff_eq_one.1 (eq.symm (
  calc f 1 = f (1*1)     : by simp
       ... = (f 1)*(f 1) : by rw[H 1 1]))

@[simp]
lemma mph_inv { f : α → β } (H : is_mph f) : (f a)⁻¹ = f (a⁻¹) :=
inv_eq_of_mul_eq_one (
  calc (f a) * (f a⁻¹) = f (a * a⁻¹) : by rw[H a a⁻¹]
                  ...  = f 1 : by simp
                  ...  = 1   : by rw[mph_one H])

end morphisms

section anti_morphisms
variables { β : Type*} [group α] [group β] {a : α}

@[simp]
def is_anti_mph (f : α → β) : Prop :=
∀ a b : α, f(a*b) = f(b)*f(a)

@[simp]
lemma anti_mph_one { f : α → β } (H : is_anti_mph f) : f 1 = 1 :=
mul_self_iff_eq_one.1 (eq.symm (
  calc f 1 = f (1*1)     : by simp
       ... = (f 1)*(f 1) : by rw[H 1 1]))

@[simp]
lemma anti_mph_inv { f : α → β } (H : is_anti_mph f) : (f a)⁻¹ = f (a⁻¹) :=
inv_eq_of_mul_eq_one (
  calc (f a) * (f a⁻¹) = f (a⁻¹ * a) : by rw[H a⁻¹ a]
                  ...  = f 1 : by simp
                  ...  = 1   : by rw[anti_mph_one H])


lemma inv_anti_mph : is_anti_mph (λ x : α, x⁻¹) :=
mul_inv_rev

end anti_morphisms
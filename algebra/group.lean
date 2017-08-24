/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Various multiplicative and additive structures.
-/
universe variable u
variable {α : Type u}

section group
  variable [group α]

  variable (α)
  theorem left_inverse_inv : function.left_inverse (λ a : α, a⁻¹) (λ a, a⁻¹) :=
  assume a, inv_inv a
  variable {α}

  theorem inv_eq_inv_iff_eq (a b : α) : a⁻¹ = b⁻¹ ↔ a = b :=
  iff.intro inv_inj (begin intro h, simp [h] end)

  theorem inv_eq_one_iff_eq_one (a : α) : a⁻¹ = 1 ↔ a = 1 :=
  have a⁻¹ = 1⁻¹ ↔ a = 1, from inv_eq_inv_iff_eq a 1,
  begin rewrite this.symm, simp end

  theorem eq_one_of_inv_eq_one (a : α) : a⁻¹ = 1 → a = 1 :=
  iff.mp (inv_eq_one_iff_eq_one a)

  theorem eq_inv_iff_eq_inv (a b : α) : a = b⁻¹ ↔ b = a⁻¹ :=
  iff.intro eq_inv_of_eq_inv eq_inv_of_eq_inv

  theorem eq_of_mul_inv_eq_one {a b : α} (H : a * b⁻¹ = 1) : a = b :=
  calc
    a    = a * b⁻¹ * b : by simp
     ... = b           : begin rewrite H, simp end

  theorem mul_eq_iff_eq_inv_mul (a b c : α) : a * b = c ↔ b = a⁻¹ * c :=
  iff.intro eq_inv_mul_of_mul_eq mul_eq_of_eq_inv_mul

  theorem mul_eq_iff_eq_mul_inv (a b c : α) : a * b = c ↔ a = c * b⁻¹ :=
  iff.intro eq_mul_inv_of_mul_eq mul_eq_of_eq_mul_inv
end group

/- transport versions to additive -/
run_cmd transport_multiplicative_to_additive [
  /- map operations -/
  (`has_mul.mul, `has_add.add), (`has_one.one, `has_zero.zero), (`has_inv.inv, `has_neg.neg),
  (`has_mul, `has_add), (`has_one, `has_zero), (`has_inv, `has_neg),
  /- map constructors -/
  (`has_mul.mk, `has_add.mk), (`has_one, `has_zero.mk), (`has_inv, `has_neg.mk),
  /- map structures -/
  (`semigroup, `add_semigroup),
  (`monoid, `add_monoid),
  (`group, `add_group),
  (`comm_semigroup, `add_comm_semigroup),
  (`comm_monoid, `add_comm_monoid),
  (`comm_group, `add_comm_group),
  (`left_cancel_semigroup, `add_left_cancel_semigroup),
  (`right_cancel_semigroup, `add_right_cancel_semigroup),
  (`left_cancel_semigroup.mk, `add_left_cancel_semigroup.mk),
  (`right_cancel_semigroup.mk, `add_right_cancel_semigroup.mk),
  /- map instances -/
  (`semigroup.to_has_mul, `add_semigroup.to_has_add),
  (`monoid.to_has_one, `add_monoid.to_has_zero),
  (`group.to_has_inv, `add_group.to_has_neg),
  (`comm_semigroup.to_semigroup, `add_comm_semigroup.to_add_semigroup),
  (`monoid.to_semigroup, `add_monoid.to_add_semigroup),
  (`comm_monoid.to_monoid, `add_comm_monoid.to_add_monoid),
  (`comm_monoid.to_comm_semigroup, `add_comm_monoid.to_add_comm_semigroup),
  (`group.to_monoid, `add_group.to_add_monoid),
  (`comm_group.to_group, `add_comm_group.to_add_group),
  (`comm_group.to_comm_monoid, `add_comm_group.to_add_comm_monoid),
  (`left_cancel_semigroup.to_semigroup, `add_left_cancel_semigroup.to_add_semigroup),
  (`right_cancel_semigroup.to_semigroup, `add_right_cancel_semigroup.to_add_semigroup),
  /- map projections -/
  (`semigroup.mul_assoc, `add_semigroup.add_assoc),
  (`comm_semigroup.mul_comm, `add_comm_semigroup.add_comm),
  (`left_cancel_semigroup.mul_left_cancel, `add_left_cancel_semigroup.add_left_cancel),
  (`right_cancel_semigroup.mul_right_cancel, `add_right_cancel_semigroup.add_right_cancel),
  (`monoid.one_mul, `add_monoid.zero_add),
  (`monoid.mul_one, `add_monoid.add_zero),
  (`group.mul_left_inv, `add_group.add_left_neg),
  (`group.mul, `add_group.add),
  (`group.mul_assoc, `add_group.add_assoc),
  /- map lemmas -/
  (`mul_assoc, `add_assoc),
  (`mul_comm, `add_comm),
  (`mul_left_comm, `add_left_comm),
  (`mul_right_comm, `add_right_comm),
  (`one_mul, `zero_add),
  (`mul_one, `add_zero),
  (`mul_left_inv, `add_left_neg),
  (`mul_left_cancel, `add_left_cancel),
  (`mul_right_cancel, `add_right_cancel),
  (`mul_left_cancel_iff, `add_left_cancel_iff),
  (`mul_right_cancel_iff, `add_right_cancel_iff),
  (`inv_mul_cancel_left, `neg_add_cancel_left),
  (`inv_mul_cancel_right, `neg_add_cancel_right),
  (`eq_inv_mul_of_mul_eq, `eq_neg_add_of_add_eq),
  (`inv_eq_of_mul_eq_one, `neg_eq_of_add_eq_zero),
  (`inv_inv, `neg_neg),
  (`mul_right_inv, `add_right_neg),
  (`mul_inv_cancel_left, `add_neg_cancel_left),
  (`mul_inv_cancel_right, `add_neg_cancel_right),
  (`mul_inv_rev, `neg_add_rev),
  (`mul_inv, `neg_add),
  (`inv_inj, `neg_inj),
  (`group.mul_left_cancel, `add_group.add_left_cancel),
  (`group.mul_right_cancel, `add_group.add_right_cancel),
  (`group.to_left_cancel_semigroup, `add_group.to_left_cancel_add_semigroup),
  (`group.to_right_cancel_semigroup, `add_group.to_right_cancel_add_semigroup),
  (`eq_inv_of_eq_inv, `eq_neg_of_eq_neg),
  (`eq_inv_of_mul_eq_one, `eq_neg_of_add_eq_zero),
  (`eq_mul_inv_of_mul_eq, `eq_add_neg_of_add_eq),
  (`inv_mul_eq_of_eq_mul, `neg_add_eq_of_eq_add),
  (`mul_inv_eq_of_eq_mul, `add_neg_eq_of_eq_add),
  (`eq_mul_of_mul_inv_eq, `eq_add_of_add_neg_eq),
  (`eq_mul_of_inv_mul_eq, `eq_add_of_neg_add_eq),
  (`mul_eq_of_eq_inv_mul, `add_eq_of_eq_neg_add),
  (`mul_eq_of_eq_mul_inv, `add_eq_of_eq_add_neg),
  (`one_inv, `neg_zero),
  (`left_inverse_inv, `left_inverse_neg),
  (`inv_eq_inv_iff_eq, `neg_eq_neg_iff_eq),
  (`inv_eq_one_iff_eq_one, `neg_eq_zero_iff_eq_zero),
  (`eq_one_of_inv_eq_one, `eq_zero_of_neg_eq_zero),
  (`eq_inv_iff_eq_inv, `eq_neg_iff_eq_neg),
  (`eq_of_mul_inv_eq_one, `eq_of_add_neg_eq_zero),
  (`mul_eq_iff_eq_inv_mul, `add_eq_iff_eq_neg_add),
  (`mul_eq_iff_eq_mul_inv, `add_eq_iff_eq_add_neg)
  -- (`mul_eq_one_of_mul_eq_one, `add_eq_zero_of_add_eq_zero)   not needed for commutative groups
  -- (`muleq_one_iff_mul_eq_one, `add_eq_zero_iff_add_eq_zero)
  ]

section add_group
  variable [add_group α]

  local attribute [simp] sub_eq_add_neg

  theorem eq_iff_sub_eq_zero (a b : α) : a = b ↔ a - b = 0 :=
  iff.intro (assume h, by simp [h]) (assume h, eq_of_sub_eq_zero h)

  theorem sub_eq_iff_eq_add (a b c : α) : a - b = c ↔ a = c + b :=
  iff.intro (assume H, eq_add_of_add_neg_eq H) (assume H, add_neg_eq_of_eq_add H)

  theorem eq_sub_iff_add_eq (a b c : α) : a = b - c ↔ a + c = b :=
  iff.intro (assume H, add_eq_of_eq_add_neg H) (assume H, eq_add_neg_of_add_eq H)

  theorem eq_iff_eq_of_sub_eq_sub {a b c d : α} (H : a - b = c - d) : a = b ↔ c = d :=
  calc
    a = b ↔ a - b = 0   : eq_iff_sub_eq_zero a b
      ... = (c - d = 0) : by rewrite H
      ... ↔ c = d       : iff.symm (eq_iff_sub_eq_zero c d)

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

section ordered_comm_group
variables [ordered_comm_group α]

lemma le_sub_iff_add_le {a b c : α} : a ≤ b - c ↔ a + c ≤ b :=
by rw [add_comm]; exact ⟨add_le_of_le_sub_left, le_sub_left_of_add_le⟩

lemma sub_le_iff_le_add {a b c : α} : a - c ≤ b ↔ a ≤ b + c :=
by rw [add_comm]; exact ⟨le_add_of_sub_left_le, sub_left_le_of_le_add⟩

end ordered_comm_group

section decidable_linear_ordered_comm_group
variables [decidable_linear_ordered_comm_group α] {a b : α}

lemma abs_le_iff  : abs a ≤ b ↔ (- b ≤ a ∧ a ≤ b) :=
⟨assume h, ⟨neg_le_of_neg_le $ le_trans (neg_le_abs_self _) h, le_trans (le_abs_self _) h⟩,
  assume ⟨h₁, h₂⟩, abs_le_of_le_of_neg_le h₂ $ neg_le_of_neg_le h₁⟩

@[simp] lemma abs_eq_zero_iff : abs a = 0 ↔ a = 0 :=
⟨eq_zero_of_abs_eq_zero, by simp [abs_zero] {contextual := tt}⟩

end decidable_linear_ordered_comm_group

/-
namespace norm_num
reveal add.assoc

def add1 [has_add A] [has_one A] (a : A) : A := add a one

local attribute add1 bit0 bit1 [reducible]

theorem add_comm_four [add_comm_semigroup A] (a b : A) : a + a + (b + b) = (a + b) + (a + b) :=
sorry -- by simp

theorem add_comm_middle [add_comm_semigroup A] (a b c : A) : a + b + c = a + c + b :=
sorry -- by simp

theorem bit0_add_bit0 [add_comm_semigroup A] (a b : A) : bit0 a + bit0 b = bit0 (a + b) :=
sorry -- by simp

theorem bit0_add_bit0_helper [add_comm_semigroup A] (a b t : A) (H : a + b = t) :
        bit0 a + bit0 b = bit0 t :=
sorry -- by rewrite -H; simp

theorem bit1_add_bit0 [add_comm_semigroup A] [has_one A] (a b : A) :
        bit1 a + bit0 b = bit1 (a + b) :=
sorry -- by simp

theorem bit1_add_bit0_helper [add_comm_semigroup A] [has_one A] (a b t : A)
        (H : a + b = t) : bit1 a + bit0 b = bit1 t :=
sorry -- by rewrite -H; simp

theorem bit0_add_bit1 [add_comm_semigroup A] [has_one A] (a b : A) :
        bit0 a + bit1 b = bit1 (a + b) :=
sorry -- by simp

theorem bit0_add_bit1_helper [add_comm_semigroup A] [has_one A] (a b t : A)
        (H : a + b = t) : bit0 a + bit1 b = bit1 t :=
sorry -- by rewrite -H; simp

theorem bit1_add_bit1 [add_comm_semigroup A] [has_one A] (a b : A) :
        bit1 a + bit1 b = bit0 (add1 (a + b)) :=
sorry -- by simp

theorem bit1_add_bit1_helper [add_comm_semigroup A] [has_one A] (a b t s: A)
        (H : (a + b) = t) (H2 : add1 t = s) : bit1 a + bit1 b = bit0 s :=
sorry -- by inst_simp

theorem bin_add_zero [add_monoid A] (a : A) : a + zero = a :=
sorry -- by simp

theorem bin_zero_add [add_monoid A] (a : A) : zero + a = a :=
sorry -- by simp

theorem one_add_bit0 [add_comm_semigroup A] [has_one A] (a : A) : one + bit0 a = bit1 a :=
sorry -- by simp

theorem bit0_add_one [has_add A] [has_one A] (a : A) : bit0 a + one = bit1 a := rfl

theorem bit1_add_one [has_add A] [has_one A] (a : A) : bit1 a + one = add1 (bit1 a) := rfl

theorem bit1_add_one_helper [has_add A] [has_one A] (a t : A) (H : add1 (bit1 a) = t) :
        bit1 a + one = t :=
sorry -- by inst_simp

theorem one_add_bit1 [add_comm_semigroup A] [has_one A] (a : A) : one + bit1 a = add1 (bit1 a) :=
sorry -- by simp

theorem one_add_bit1_helper [add_comm_semigroup A] [has_one A] (a t : A)
        (H : add1 (bit1 a) = t) : one + bit1 a = t :=
sorry -- by inst_simp

theorem add1_bit0 [has_add A] [has_one A] (a : A) : add1 (bit0 a) = bit1 a := rfl

theorem add1_bit1 [add_comm_semigroup A] [has_one A] (a : A) :
        add1 (bit1 a) = bit0 (add1 a) :=
sorry -- by simp

theorem add1_bit1_helper [add_comm_semigroup A] [has_one A] (a t : A) (H : add1 a = t) :
        add1 (bit1 a) = bit0 t :=
sorry -- by inst_simp

theorem add1_one [has_add A] [has_one A] : add1 (one : A) = bit0 one := rfl

theorem add1_zero [add_monoid A] [has_one A] : add1 (zero : A) = one :=
sorry -- by simp

theorem one_add_one [has_add A] [has_one A] : (one : A) + one = bit0 one := rfl

theorem subst_into_sum [has_add A] (l r tl tr t : A) (prl : l = tl) (prr : r = tr)
        (prt : tl + tr = t) : l + r = t :=
sorry -- by simp

theorem neg_zero_helper [add_group A] (a : A) (H : a = 0) : - a = 0 :=
sorry -- by simp

end norm_num

attribute [simp]
  zero_add add_zero one_mul mul_one

attribute [simp]
  neg_neg sub_eq_add_neg

attribute [simp]
  add.assoc add.comm add.left_comm
  mul.left_comm mul.comm mul.assoc
-/

/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Various multiplicative and additive structures.
-/
universe variable u
variable {α : Type u}

@[simp] theorem mul_left_inj [left_cancel_semigroup α] {a b c : α} : a * b = a * c ↔ b = c :=
⟨mul_left_cancel, congr_arg _⟩

@[simp] theorem mul_right_inj [right_cancel_semigroup α] {a b c : α} : b * a = c * a ↔ b = c :=
⟨mul_right_cancel, congr_arg _⟩

section group
  variables [group α] {a b c : α}

  @[simp] theorem inv_inj' : a⁻¹ = b⁻¹ ↔ a = b :=
  ⟨λ h, by rw ← inv_inv a; simp [h], congr_arg _⟩

  theorem eq_of_inv_eq_inv : a⁻¹ = b⁻¹ → a = b :=
  inv_inj'.1

  @[simp] theorem mul_self_iff_eq_one : a * a = a ↔ a = 1 :=
  by have := @mul_left_inj _ _ a a 1; rwa mul_one at this

  @[simp] theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
  by rw [← @inv_inj' _ _ a 1, one_inv]

  @[simp] theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
  not_congr inv_eq_one

  theorem left_inverse_inv (α) [group α] :
    function.left_inverse (λ a : α, a⁻¹) (λ a, a⁻¹) :=
  assume a, inv_inv a

  attribute [simp] mul_inv_cancel_left mul_inv_cancel_right

  theorem eq_inv_iff_eq_inv : a = b⁻¹ ↔ b = a⁻¹ :=
  ⟨eq_inv_of_eq_inv, eq_inv_of_eq_inv⟩

  theorem inv_eq_iff_inv_eq : a⁻¹ = b ↔ b⁻¹ = a :=
  by rw [eq_comm, @eq_comm _ _ a, eq_inv_iff_eq_inv]

  theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
  have a * b = b⁻¹ * b ↔ a = b⁻¹, from mul_right_inj,
  by rwa mul_left_inv at this

  theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b :=
  by rw [mul_eq_one_iff_eq_inv, eq_inv_iff_eq_inv, eq_comm]

  theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
  mul_eq_one_iff_eq_inv.symm

  theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 :=
  mul_eq_one_iff_inv_eq.symm

  theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
  ⟨λ h, by simp [h], λ h, by simp [h.symm]⟩

  theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
  ⟨λ h, by simp [h], λ h, by simp [h.symm]⟩

  theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
  ⟨λ h, by simp [h.symm], λ h, by simp [h]⟩

  theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
  ⟨λ h, by simp [h.symm], λ h, by simp [h]⟩

  theorem mul_inv_eq_one {a b : α} : a * b⁻¹ = 1 ↔ a = b :=
  by rw [mul_eq_one_iff_eq_inv, inv_inv]
end group

/- transport versions to additive -/
run_cmd transport_multiplicative_to_additive [
  /- map operations -/
  (`has_mul.mul, `has_add.add), (`has_one.one, `has_zero.zero), (`has_inv.inv, `has_neg.neg),
  (`has_mul, `has_add), (`has_inv, `has_neg),
  /- map structures -/
  (`group, `add_group),
  (`left_cancel_semigroup, `add_left_cancel_semigroup),
  (`right_cancel_semigroup, `add_right_cancel_semigroup),
  /- map instances -/
  (`semigroup.to_has_mul, `add_semigroup.to_has_add),
  (`monoid.to_has_one, `add_monoid.to_has_zero),
  (`group.to_has_inv, `add_group.to_has_neg),
  (`monoid.to_semigroup, `add_monoid.to_add_semigroup),
  (`group.to_monoid, `add_group.to_add_monoid),
  (`left_cancel_semigroup.to_semigroup, `add_left_cancel_semigroup.to_add_semigroup),
  (`right_cancel_semigroup.to_semigroup, `add_right_cancel_semigroup.to_add_semigroup),
  /- map lemmas -/
  (`mul_one, `add_zero),
  (`mul_left_inv, `add_left_neg),
  (`mul_left_cancel, `add_left_cancel),
  (`mul_right_cancel, `add_right_cancel),
  (`inv_mul_cancel_left, `neg_add_cancel_left),
  (`inv_mul_cancel_right, `neg_add_cancel_right),
  (`inv_inv, `neg_neg),
  (`mul_inv_cancel_left, `add_neg_cancel_left),
  (`mul_inv_cancel_right, `add_neg_cancel_right),
  (`group.to_left_cancel_semigroup, `add_group.to_left_cancel_add_semigroup),
  (`group.to_right_cancel_semigroup, `add_group.to_right_cancel_add_semigroup),
  (`eq_inv_of_eq_inv, `eq_neg_of_eq_neg),
  (`one_inv, `neg_zero),
  /- new lemmas -/
  (`mul_left_inj, `add_left_inj),
  (`mul_right_inj, `add_right_inj),
  (`inv_inj', `neg_inj'),
  (`mul_self_iff_eq_one, `add_self_iff_eq_zero),
  (`inv_eq_one, `neg_eq_zero),
  (`inv_ne_one, `neg_ne_zero),
  (`left_inverse_inv, `left_inverse_neg),
  (`eq_inv_iff_eq_inv, `eq_neg_iff_eq_neg),
  (`inv_eq_iff_inv_eq, `neg_eq_iff_neg_eq),
  (`mul_eq_one_iff_eq_inv, `add_eq_zero_iff_eq_neg),
  (`mul_eq_one_iff_inv_eq, `add_eq_zero_iff_neg_eq),
  (`eq_inv_iff_mul_eq_one, `eq_neg_iff_add_eq_zero),
  (`inv_eq_iff_mul_eq_one, `neg_eq_iff_add_eq_zero),
  (`eq_mul_inv_iff_mul_eq, `eq_add_neg_iff_add_eq),
  (`eq_inv_mul_iff_mul_eq, `eq_neg_add_iff_add_eq),
  (`inv_mul_eq_iff_eq_mul, `neg_add_eq_iff_eq_add),
  (`mul_inv_eq_iff_eq_mul, `add_neg_eq_iff_eq_add),
  (`mul_inv_eq_one, `add_neg_eq_zero)]

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

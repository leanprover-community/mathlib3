/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import algebra.periodic

/-!
# Reducing to an interval modulo its length

This file defines operations that reduce a number (in an `archimedean`
`linear_ordered_add_comm_group`) to a number in a given interval, modulo the length of that
interval.

## Main definitions

* `to_Ico_div a hb x` (where `hb : 0 < b`): The unique integer such that this multiple of `b`,
  added to `x`, is in `Ico a (a + b)`.
* `to_Ico_mod a hb x` (where `hb : 0 < b`): Reduce `x` to the interval `Ico a (a + b)`.
* `to_Ioc_div a hb x` (where `hb : 0 < b`): The unique integer such that this multiple of `b`,
  added to `x`, is in `Ioc a (a + b)`.
* `to_Ioc_mod a hb x` (where `hb : 0 < b`): Reduce `x` to the interval `Ioc a (a + b)`.

-/

noncomputable theory

section linear_ordered_add_comm_group

variables {α : Type*} [linear_ordered_add_comm_group α] [archimedean α]

/-- The unique integer such that this multiple of `b`, added to `x`, is in `Ico a (a + b)`. -/
def to_Ico_div (a : α) {b : α} (hb : 0 < b) (x : α) : ℤ :=
(exists_unique_add_zsmul_mem_Ico hb x a).some

lemma add_to_Ico_div_zsmul_mem_Ico (a : α) {b : α} (hb : 0 < b) (x : α) :
  x + to_Ico_div a hb x • b ∈ set.Ico a (a + b) :=
(exists_unique_add_zsmul_mem_Ico hb x a).some_spec.1

lemma eq_to_Ico_div_of_add_zsmul_mem_Ico {a b x : α} (hb : 0 < b) {y : ℤ}
  (hy : x + y • b ∈ set.Ico a (a + b)) : y = to_Ico_div a hb x :=
(exists_unique_add_zsmul_mem_Ico hb x a).some_spec.2 y hy

/-- The unique integer such that this multiple of `b`, added to `x`, is in `Ioc a (a + b)`. -/
def to_Ioc_div (a : α) {b : α} (hb : 0 < b) (x : α) : ℤ :=
(exists_unique_add_zsmul_mem_Ioc hb x a).some

lemma add_to_Ioc_div_zsmul_mem_Ioc (a : α) {b : α} (hb : 0 < b) (x : α) :
  x + to_Ioc_div a hb x • b ∈ set.Ioc a (a + b) :=
(exists_unique_add_zsmul_mem_Ioc hb x a).some_spec.1

lemma eq_to_Ioc_div_of_add_zsmul_mem_Ioc {a b x : α} (hb : 0 < b) {y : ℤ}
  (hy : x + y • b ∈ set.Ioc a (a + b)) : y = to_Ioc_div a hb x :=
(exists_unique_add_zsmul_mem_Ioc hb x a).some_spec.2 y hy

/-- Reduce `x` to the interval `Ico a (a + b)`. -/
def to_Ico_mod (a : α) {b : α} (hb : 0 < b) (x : α) : α := x + to_Ico_div a hb x • b

/-- Reduce `x` to the interval `Ioc a (a + b)`. -/
def to_Ioc_mod (a : α) {b : α} (hb : 0 < b) (x : α) : α := x + to_Ioc_div a hb x • b

lemma to_Ico_mod_mem_Ico (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a hb x ∈ set.Ico a (a + b) :=
add_to_Ico_div_zsmul_mem_Ico a hb x

lemma to_Ioc_mod_mem_Ioc (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a hb x ∈ set.Ioc a (a + b) :=
add_to_Ioc_div_zsmul_mem_Ioc a hb x

lemma left_le_to_Ico_mod (a : α) {b : α} (hb : 0 < b) (x : α) : a ≤ to_Ico_mod a hb x :=
(set.mem_Ico.1 (to_Ico_mod_mem_Ico a hb x)).1

lemma left_lt_to_Ioc_mod (a : α) {b : α} (hb : 0 < b) (x : α) : a < to_Ioc_mod a hb x :=
(set.mem_Ioc.1 (to_Ioc_mod_mem_Ioc a hb x)).1

lemma to_Ico_mod_lt_right (a : α) {b : α} (hb : 0 < b) (x : α) : to_Ico_mod a hb x < a + b :=
(set.mem_Ico.1 (to_Ico_mod_mem_Ico a hb x)).2

lemma to_Ioc_mod_le_right (a : α) {b : α} (hb : 0 < b) (x : α) : to_Ioc_mod a hb x ≤ a + b :=
(set.mem_Ioc.1 (to_Ioc_mod_mem_Ioc a hb x)).2

@[simp] lemma self_add_to_Ico_div_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) :
  x + to_Ico_div a hb x • b = to_Ico_mod a hb x :=
rfl

@[simp] lemma self_add_to_Ioc_div_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) :
  x + to_Ioc_div a hb x • b = to_Ioc_mod a hb x :=
rfl

@[simp] lemma to_Ico_div_zsmul_add_self (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_div a hb x • b + x = to_Ico_mod a hb x :=
by rw [add_comm, to_Ico_mod]

@[simp] lemma to_Ioc_div_zsmul_add_self (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_div a hb x • b + x = to_Ioc_mod a hb x :=
by rw [add_comm, to_Ioc_mod]

@[simp] lemma to_Ico_mod_sub_self (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a hb x - x = to_Ico_div a hb x • b :=
by rw [to_Ico_mod, add_sub_cancel']

@[simp] lemma to_Ioc_mod_sub_self (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a hb x - x = to_Ioc_div a hb x • b :=
by rw [to_Ioc_mod, add_sub_cancel']

@[simp] lemma self_sub_to_Ico_mod (a : α) {b : α} (hb : 0 < b) (x : α) :
  x - to_Ico_mod a hb x = -to_Ico_div a hb x • b :=
by rw [to_Ico_mod, sub_add_cancel', neg_smul]

@[simp] lemma self_sub_to_Ioc_mod (a : α) {b : α} (hb : 0 < b) (x : α) :
  x - to_Ioc_mod a hb x = -to_Ioc_div a hb x • b :=
by rw [to_Ioc_mod, sub_add_cancel', neg_smul]

@[simp] lemma to_Ico_mod_sub_to_Ico_div_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a hb x - to_Ico_div a hb x • b = x :=
by rw [to_Ico_mod, add_sub_cancel]

@[simp] lemma to_Ioc_mod_sub_to_Ioc_div_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a hb x - to_Ioc_div a hb x • b = x :=
by rw [to_Ioc_mod, add_sub_cancel]

@[simp] lemma to_Ico_div_zsmul_sub_to_Ico_mod (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_div a hb x • b - to_Ico_mod a hb x = -x :=
by rw [←neg_sub, to_Ico_mod_sub_to_Ico_div_zsmul]

@[simp] lemma to_Ioc_div_zsmul_sub_to_Ioc_mod (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_div a hb x • b - to_Ioc_mod a hb x = -x :=
by rw [←neg_sub, to_Ioc_mod_sub_to_Ioc_div_zsmul]

lemma to_Ico_mod_eq_iff {a b x y : α} (hb : 0 < b) :
  to_Ico_mod a hb x = y ↔ a ≤ y ∧ y < a + b ∧ ∃ z : ℤ, y - x = z • b :=
begin
  refine ⟨λ h, ⟨h ▸ left_le_to_Ico_mod a hb x,
                h ▸ to_Ico_mod_lt_right a hb x,
                to_Ico_div a hb x,
                h ▸ to_Ico_mod_sub_self a hb x⟩,
          λ h, _⟩,
  rcases h with ⟨ha, hab, z, hz⟩,
  rw sub_eq_iff_eq_add' at hz,
  subst hz,
  rw eq_to_Ico_div_of_add_zsmul_mem_Ico hb (set.mem_Ico.2 ⟨ha, hab⟩),
  refl
end

lemma to_Ioc_mod_eq_iff {a b x y : α} (hb : 0 < b) :
  to_Ioc_mod a hb x = y ↔ a < y ∧ y ≤ a + b ∧ ∃ z : ℤ, y - x = z • b :=
begin
  refine ⟨λ h, ⟨h ▸ left_lt_to_Ioc_mod a hb x,
                h ▸ to_Ioc_mod_le_right a hb x,
                to_Ioc_div a hb x,
                h ▸ to_Ioc_mod_sub_self a hb x⟩,
          λ h, _⟩,
  rcases h with ⟨ha, hab, z, hz⟩,
  rw sub_eq_iff_eq_add' at hz,
  subst hz,
  rw eq_to_Ioc_div_of_add_zsmul_mem_Ioc hb (set.mem_Ioc.2 ⟨ha, hab⟩),
  refl
end

@[simp] lemma to_Ico_div_apply_left (a : α) {b : α} (hb : 0 < b) : to_Ico_div a hb a = 0 :=
begin
  refine (eq_to_Ico_div_of_add_zsmul_mem_Ico hb _).symm,
  simp [hb]
end

@[simp] lemma to_Ioc_div_apply_left (a : α) {b : α} (hb : 0 < b) : to_Ioc_div a hb a = 1 :=
begin
  refine (eq_to_Ioc_div_of_add_zsmul_mem_Ioc hb _).symm,
  simp [hb]
end

@[simp] lemma to_Ico_mod_apply_left (a : α) {b : α} (hb : 0 < b) : to_Ico_mod a hb a = a :=
begin
  rw to_Ico_mod_eq_iff hb,
  refine ⟨le_refl _, lt_add_of_pos_right _ hb, 0, _⟩,
  simp
end

@[simp] lemma to_Ioc_mod_apply_left (a : α) {b : α} (hb : 0 < b) : to_Ioc_mod a hb a = a + b :=
begin
  rw to_Ioc_mod_eq_iff hb,
  refine ⟨lt_add_of_pos_right _ hb, le_refl _, 1, _⟩,
  simp
end

lemma to_Ico_div_apply_right (a : α) {b : α} (hb : 0 < b) :
  to_Ico_div a hb (a + b) = -1 :=
begin
  refine (eq_to_Ico_div_of_add_zsmul_mem_Ico hb _).symm,
  simp [hb]
end

lemma to_Ioc_div_apply_right (a : α) {b : α} (hb : 0 < b) :
  to_Ioc_div a hb (a + b) = 0 :=
begin
  refine (eq_to_Ioc_div_of_add_zsmul_mem_Ioc hb _).symm,
  simp [hb]
end

lemma to_Ico_mod_apply_right (a : α) {b : α} (hb : 0 < b) : to_Ico_mod a hb (a + b) = a :=
begin
  rw to_Ico_mod_eq_iff hb,
  refine ⟨le_refl _, lt_add_of_pos_right _ hb, -1, _⟩,
  simp
end

lemma to_Ioc_mod_apply_right (a : α) {b : α} (hb : 0 < b) :
  to_Ioc_mod a hb (a + b) = a + b :=
begin
  rw to_Ioc_mod_eq_iff hb,
  refine ⟨lt_add_of_pos_right _ hb, le_refl _, 0, _⟩,
  simp
end

@[simp] lemma to_Ico_div_add_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ico_div a hb (x + m • b) = to_Ico_div a hb x - m :=
begin
  refine (eq_to_Ico_div_of_add_zsmul_mem_Ico hb _).symm,
  convert add_to_Ico_div_zsmul_mem_Ico a hb x using 1,
  simp [sub_smul]
end

@[simp] lemma to_Ioc_div_add_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ioc_div a hb (x + m • b) = to_Ioc_div a hb x - m :=
begin
  refine (eq_to_Ioc_div_of_add_zsmul_mem_Ioc hb _).symm,
  convert add_to_Ioc_div_zsmul_mem_Ioc a hb x using 1,
  simp [sub_smul]
end

@[simp] lemma to_Ico_div_zsmul_add (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ico_div a hb (m • b + x) = to_Ico_div a hb x - m :=
by rw [add_comm, to_Ico_div_add_zsmul]

@[simp] lemma to_Ioc_div_zsmul_add (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ioc_div a hb (m • b + x) = to_Ioc_div a hb x - m :=
by rw [add_comm, to_Ioc_div_add_zsmul]

@[simp] lemma to_Ico_div_sub_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ico_div a hb (x - m • b) = to_Ico_div a hb x + m :=
by rw [sub_eq_add_neg, ←neg_smul, to_Ico_div_add_zsmul, sub_neg_eq_add]

@[simp] lemma to_Ioc_div_sub_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ioc_div a hb (x - m • b) = to_Ioc_div a hb x + m :=
by rw [sub_eq_add_neg, ←neg_smul, to_Ioc_div_add_zsmul, sub_neg_eq_add]

@[simp] lemma to_Ico_div_add_right (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_div a hb (x + b) = to_Ico_div a hb x - 1 :=
begin
  convert to_Ico_div_add_zsmul a hb x 1,
  exact (one_zsmul _).symm
end

@[simp] lemma to_Ioc_div_add_right (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_div a hb (x + b) = to_Ioc_div a hb x - 1 :=
begin
  convert to_Ioc_div_add_zsmul a hb x 1,
  exact (one_zsmul _).symm
end

@[simp] lemma to_Ico_div_add_left (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_div a hb (b + x) = to_Ico_div a hb x - 1 :=
by rw [add_comm, to_Ico_div_add_right]

@[simp] lemma to_Ioc_div_add_left (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_div a hb (b + x) = to_Ioc_div a hb x - 1 :=
by rw [add_comm, to_Ioc_div_add_right]

@[simp] lemma to_Ico_div_sub (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_div a hb (x - b) = to_Ico_div a hb x + 1 :=
begin
  convert to_Ico_div_sub_zsmul a hb x 1,
  exact (one_zsmul _).symm
end

@[simp] lemma to_Ioc_div_sub (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_div a hb (x - b) = to_Ioc_div a hb x + 1 :=
begin
  convert to_Ioc_div_sub_zsmul a hb x 1,
  exact (one_zsmul _).symm
end

@[simp] lemma to_Ico_mod_add_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ico_mod a hb (x + m • b) = to_Ico_mod a hb x :=
begin
  rw [to_Ico_mod, to_Ico_div_add_zsmul, to_Ico_mod, sub_smul],
  abel
end

@[simp] lemma to_Ioc_mod_add_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ioc_mod a hb (x + m • b) = to_Ioc_mod a hb x :=
begin
  rw [to_Ioc_mod, to_Ioc_div_add_zsmul, to_Ioc_mod, sub_smul],
  abel
end

@[simp] lemma to_Ico_mod_zsmul_add (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ico_mod a hb (m • b + x) = to_Ico_mod a hb x :=
by rw [add_comm, to_Ico_mod_add_zsmul]

@[simp] lemma to_Ioc_mod_zsmul_add (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ioc_mod a hb (m • b + x) = to_Ioc_mod a hb x :=
by rw [add_comm, to_Ioc_mod_add_zsmul]

@[simp] lemma to_Ico_mod_sub_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ico_mod a hb (x - m • b) = to_Ico_mod a hb x :=
by rw [sub_eq_add_neg, ←neg_smul, to_Ico_mod_add_zsmul]

@[simp] lemma to_Ioc_mod_sub_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ioc_mod a hb (x - m • b) = to_Ioc_mod a hb x :=
by rw [sub_eq_add_neg, ←neg_smul, to_Ioc_mod_add_zsmul]

@[simp] lemma to_Ico_mod_add_right (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a hb (x + b) = to_Ico_mod a hb x :=
begin
  convert to_Ico_mod_add_zsmul a hb x 1,
  exact (one_zsmul _).symm
end

@[simp] lemma to_Ioc_mod_add_right (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a hb (x + b) = to_Ioc_mod a hb x :=
begin
  convert to_Ioc_mod_add_zsmul a hb x 1,
  exact (one_zsmul _).symm
end

@[simp] lemma to_Ico_mod_add_left (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a hb (b + x) = to_Ico_mod a hb x :=
by rw [add_comm, to_Ico_mod_add_right]

@[simp] lemma to_Ioc_mod_add_left (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a hb (b + x) = to_Ioc_mod a hb x :=
by rw [add_comm, to_Ioc_mod_add_right]

@[simp] lemma to_Ico_mod_sub (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a hb (x - b) = to_Ico_mod a hb x :=
begin
  convert to_Ico_mod_sub_zsmul a hb x 1,
  exact (one_zsmul _).symm
end

@[simp] lemma to_Ioc_mod_sub (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a hb (x - b) = to_Ioc_mod a hb x :=
begin
  convert to_Ioc_mod_sub_zsmul a hb x 1,
  exact (one_zsmul _).symm
end

lemma to_Ico_mod_eq_to_Ico_mod (a : α) {b x y : α} (hb : 0 < b) :
  to_Ico_mod a hb x = to_Ico_mod a hb y ↔ ∃ z : ℤ, y - x = z • b :=
begin
  refine ⟨λ h, ⟨to_Ico_div a hb x - to_Ico_div a hb y, _⟩, λ h, _⟩,
  { conv_lhs { rw [←to_Ico_mod_sub_to_Ico_div_zsmul a hb x,
                   ←to_Ico_mod_sub_to_Ico_div_zsmul a hb y] },
    rw [h, sub_smul],
    abel },
  { rcases h with ⟨z, hz⟩,
    rw sub_eq_iff_eq_add at hz,
    rw [hz, to_Ico_mod_zsmul_add] }
end

lemma to_Ioc_mod_eq_to_Ioc_mod (a : α) {b x y : α} (hb : 0 < b) :
  to_Ioc_mod a hb x = to_Ioc_mod a hb y ↔ ∃ z : ℤ, y - x = z • b :=
begin
  refine ⟨λ h, ⟨to_Ioc_div a hb x - to_Ioc_div a hb y, _⟩, λ h, _⟩,
  { conv_lhs { rw [←to_Ioc_mod_sub_to_Ioc_div_zsmul a hb x,
                   ←to_Ioc_mod_sub_to_Ioc_div_zsmul a hb y] },
    rw [h, sub_smul],
    abel },
  { rcases h with ⟨z, hz⟩,
    rw sub_eq_iff_eq_add at hz,
    rw [hz, to_Ioc_mod_zsmul_add] }
end

lemma to_Ico_mod_eq_self {a b x : α} (hb : 0 < b) : to_Ico_mod a hb x = x ↔ a ≤ x ∧ x < a + b :=
begin
  rw to_Ico_mod_eq_iff,
  refine ⟨λ h, ⟨h.1, h.2.1⟩, λ h, ⟨h.1, h.2, 0, _⟩⟩,
  simp
end

lemma to_Ioc_mod_eq_self {a b x : α} (hb : 0 < b) : to_Ioc_mod a hb x = x ↔ a < x ∧ x ≤ a + b :=
begin
  rw to_Ioc_mod_eq_iff,
  refine ⟨λ h, ⟨h.1, h.2.1⟩, λ h, ⟨h.1, h.2, 0, _⟩⟩,
  simp
end

@[simp] lemma to_Ico_mod_to_Ico_mod (a₁ a₂ : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a₁ hb (to_Ico_mod a₂ hb x) = to_Ico_mod a₁ hb x :=
begin
  rw to_Ico_mod_eq_to_Ico_mod,
  exact ⟨-to_Ico_div a₂ hb x, self_sub_to_Ico_mod a₂ hb x⟩
end

@[simp] lemma to_Ico_mod_to_Ioc_mod (a₁ a₂ : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a₁ hb (to_Ioc_mod a₂ hb x) = to_Ico_mod a₁ hb x :=
begin
  rw to_Ico_mod_eq_to_Ico_mod,
  exact ⟨-to_Ioc_div a₂ hb x, self_sub_to_Ioc_mod a₂ hb x⟩
end

@[simp] lemma to_Ioc_mod_to_Ioc_mod (a₁ a₂ : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a₁ hb (to_Ioc_mod a₂ hb x) = to_Ioc_mod a₁ hb x :=
begin
  rw to_Ioc_mod_eq_to_Ioc_mod,
  exact ⟨-to_Ioc_div a₂ hb x, self_sub_to_Ioc_mod a₂ hb x⟩
end

@[simp] lemma to_Ioc_mod_to_Ico_mod (a₁ a₂ : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a₁ hb (to_Ico_mod a₂ hb x) = to_Ioc_mod a₁ hb x :=
begin
  rw to_Ioc_mod_eq_to_Ioc_mod,
  exact ⟨-to_Ico_div a₂ hb x, self_sub_to_Ico_mod a₂ hb x⟩
end

lemma to_Ico_mod_periodic (a : α) {b : α} (hb : 0 < b) : function.periodic (to_Ico_mod a hb) b :=
to_Ico_mod_add_right a hb

lemma to_Ioc_mod_periodic (a : α) {b : α} (hb : 0 < b) : function.periodic (to_Ioc_mod a hb) b :=
to_Ioc_mod_add_right a hb

end linear_ordered_add_comm_group

section linear_ordered_field

variables {α : Type*} [linear_ordered_field α] [floor_ring α]

local attribute [instance] floor_ring.archimedean

lemma to_Ico_div_eq_neg_floor (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_div a hb x = -⌊(x - a) / b⌋ :=
begin
  refine (eq_to_Ico_div_of_add_zsmul_mem_Ico hb _).symm,
  rw [set.mem_Ico, zsmul_eq_mul, int.cast_neg, neg_mul, ←sub_nonneg, add_comm, add_sub_assoc,
      add_comm, ←sub_eq_add_neg],
  refine ⟨int.sub_floor_div_mul_nonneg _ hb, _⟩,
  rw [add_comm a, ←sub_lt_iff_lt_add, add_sub_assoc, add_comm, ←sub_eq_add_neg],
  exact int.sub_floor_div_mul_lt _ hb
end

lemma to_Ioc_div_eq_floor (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_div a hb x = ⌊(a + b - x) / b⌋ :=
begin
  refine (eq_to_Ioc_div_of_add_zsmul_mem_Ioc hb _).symm,
  rw [set.mem_Ioc, zsmul_eq_mul, ←sub_nonneg, sub_add_eq_sub_sub],
  refine ⟨_, int.sub_floor_div_mul_nonneg _ hb⟩,
  rw [←add_lt_add_iff_right b, add_assoc, add_comm x, ←sub_lt_iff_lt_add, add_comm (_ * _),
      ←sub_lt_iff_lt_add],
  exact int.sub_floor_div_mul_lt _ hb
end

lemma to_Ico_div_zero_one (x : α) : to_Ico_div (0 : α) zero_lt_one x = -⌊x⌋ :=
by simp [to_Ico_div_eq_neg_floor]

lemma to_Ico_mod_eq_add_fract_mul (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a hb x = a + int.fract ((x - a) / b) * b :=
begin
  rw [to_Ico_mod, to_Ico_div_eq_neg_floor, int.fract],
  field_simp [hb.ne.symm],
  ring
end

lemma to_Ioc_mod_eq_sub_fract_mul (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a hb x = a + b - int.fract ((a + b - x) / b) * b :=
begin
  rw [to_Ioc_mod, to_Ioc_div_eq_floor, int.fract],
  field_simp [hb.ne.symm],
  ring
end

lemma to_Ico_mod_zero_one (x : α) : to_Ico_mod (0 : α) zero_lt_one x = int.fract x :=
by simp [to_Ico_mod_eq_add_fract_mul]

end linear_ordered_field

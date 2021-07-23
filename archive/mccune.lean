/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import tactic

class mccune_group (α : Type*) extends has_mul α, has_inv α, inhabited α :=
(mccune (x y z u : α) : x * (y * (((z * z⁻¹) * (u * y)⁻¹) * x))⁻¹ = u)

namespace mccune_group
variables {α : Type*} [mccune_group α] (x y z u v w : α)

lemma l5 : x * (y * (z * z⁻¹ * (u * y)⁻¹ * x))⁻¹ = u := mccune _ _ _ _

lemma l7 : x * (y * y⁻¹ * (z * u)⁻¹ * (v * v⁻¹) * (z * x))⁻¹ = u :=
by simpa [l5] using l5 x (y * y⁻¹ * (z * u)⁻¹ * (v * v⁻¹)) v u

lemma l9 : x * (y * (z * z⁻¹) * (u * x))⁻¹ = v * v⁻¹ * (y * u)⁻¹ * (w * w⁻¹) :=
by simpa [l5] using l7 x w u (v * v⁻¹ * (y * u)⁻¹ * (w * w⁻¹)) z

lemma l10 : y * y⁻¹ * (z * z⁻¹ * (u * x)⁻¹ * u)⁻¹ * (v * v⁻¹) = x :=
by simpa [l9 _ _ _ u y v] using l7 x z u x

lemma l12 : x * x⁻¹ * y⁻¹⁻¹ * (z * z⁻¹) = y :=
by simpa [l10] using l10 y x x (y * y⁻¹ * (y * y⁻¹)⁻¹) z

lemma l14 : x * x⁻¹ * (y * z)⁻¹ = u * u⁻¹ * (y * z)⁻¹ :=
by simpa [l10] using l5 (x * x⁻¹) y x (u * u⁻¹ * (y * z)⁻¹)

lemma l15 : (x * x⁻¹) * y⁻¹ = (z * z⁻¹) * y⁻¹ :=
by simpa [l12] using l14 x ((x * x⁻¹) * y⁻¹⁻¹) (z * z⁻¹) z

lemma l17 : u * u⁻¹ = v * v⁻¹ := by simpa [l15 v u u, l5] using l5 u u⁻¹ u (v * v⁻¹)
instance : has_one α := ⟨default α * (default α)⁻¹⟩
@[simp] lemma mul_right_inv : u * u⁻¹ = 1 := l17 _ _
lemma l20 : 1 * (1 * z)⁻¹ * 1 = z⁻¹ := by simpa using l10 z⁻¹ z z z z
lemma l22 : x * (y⁻¹ * (1 * x))⁻¹ = y := by simpa using l5 x y⁻¹ x y
lemma l25 : x * (1⁻¹⁻¹ * (w * x))⁻¹ = w⁻¹ := by simpa [←l20 (1 : α)⁻¹] using l7 x x w w⁻¹
lemma l32 : 1⁻¹ * (y⁻¹ * 1)⁻¹ = y := by simpa using l22 1⁻¹ y
lemma l34 : x⁻¹ * (1⁻¹⁻¹ * 1)⁻¹ = x⁻¹ := by simpa using l25 x⁻¹ x
lemma l36 : (1 * (x * 1⁻¹⁻¹)⁻¹)⁻¹ = x := by simpa [l25] using l5 x 1⁻¹⁻¹ x x
lemma l44 : x * (1⁻¹⁻¹ * 1)⁻¹ = x := by simpa [l36] using l34 (1 * (x * 1⁻¹⁻¹)⁻¹)
lemma l48 : (1 : α)⁻¹⁻¹ * 1 = 1 := by simpa using (l44 ((1 : α)⁻¹⁻¹ * 1)).symm
lemma l52 : x * 1⁻¹ = x := by simpa [l48] using l44 x
lemma l57 : (1⁻¹ * u)⁻¹⁻¹ = u := by simpa [l52, l20] using l10 u u u 1⁻¹ u
lemma l62 : (x⁻¹ * 1)⁻¹ = x⁻¹⁻¹ := by simpa [l32] using (l57 (x⁻¹ * 1)⁻¹).symm
lemma l76 : (x * 1)⁻¹ = x⁻¹ := by simpa [l57] using l62 (1⁻¹ * x)⁻¹
lemma l88 : 1⁻¹ * x⁻¹⁻¹ = x := by simpa [l76] using l32 x
@[simp] lemma mul_one : y * 1 = y := by simpa [l76, l88] using (l88 (y * 1)).symm
lemma one_inv_inv : (1 : α)⁻¹⁻¹ = 1 := by simpa using l48
@[simp] lemma one_inv : (1 : α)⁻¹ = 1 := by simpa [one_inv_inv] using l88 (1 : α)
lemma l92 : (1 * y⁻¹)⁻¹ = y := by simpa using l36 y

lemma l126 : (y * z) * z⁻¹ = y :=
begin
  have := l5 ((1 : α) * (y * z)⁻¹)⁻¹ z z y,
  rw [mul_right_inv, mul_right_inv] at this,
  simpa [l92] using this,
end

lemma l201 : x * y⁻¹⁻¹ = x * y := by simpa [l126 x y] using l126 (x * y) y⁻¹
@[simp] lemma one_mul : 1 * z = z := by simpa [l201] using l126 z z⁻¹
@[simp] lemma inv_inv : y⁻¹⁻¹ = y := by simpa using l201 1 y
@[simp] lemma mul_left_inv : x⁻¹ * x = 1 := by simpa using mul_right_inv x⁻¹
lemma l229 : (z * x)⁻¹ = x⁻¹ * z⁻¹ := by simpa [l126] using (l25 x⁻¹ (z * x)).symm
lemma thingy : x * (x⁻¹ * z) = z := by simpa [l229] using l5 x z⁻¹ x z
lemma l239 : x * (x⁻¹ * u * y) = u * y := by simpa [l229, l126] using l5 x y⁻¹ x (u * y)

lemma mul_assoc : x * y * z = x * (y * z) :=
begin
  have := thingy x (x⁻¹⁻¹ * y * z),
  simp only [l239] at this,
  simp [this],
end

/-- Every McCune group is a group. -/
instance : group α :=
{ mul_assoc := mul_assoc,
  one_mul := by simp,
  mul_one := by simp,
  mul_left_inv := λ x, mul_left_inv _,
  ..(by apply_instance : has_one α),
  ..(by apply_instance : has_mul α),
  ..(by apply_instance : has_inv α) }

end mccune_group

/-- Every group is a McCune group. -/
def mccune_group_of_group {α : Type*} [group α] : mccune_group α :=
{ mccune := λ x y z u, by simp [mul_assoc],
  default := 1 }

class mccune_comm_group (α : Type*) extends has_mul α, has_inv α, inhabited α :=
(mccune (x y z : α) : x * y * z * (x * z)⁻¹ = y)

namespace mccune_comm_group
variables {α : Type*} [mccune_comm_group α] (x y z u v w : α)

lemma l10 : x * y * (z * x * u * y)⁻¹ = (z * u)⁻¹ :=
by simpa [mccune] using mccune (z * x * u) (z * u)⁻¹ y

lemma l12 : x * (y * x * (y * z)⁻¹)⁻¹ = z := by simpa [mccune] using mccune (y * x) z (y * z)⁻¹
lemma l16 : x * (y * z)⁻¹ * x⁻¹ = (y * z)⁻¹ := by simpa [mccune] using l10 x (y * z)⁻¹ y z
lemma l18 : (y * (z * (y * z * x)⁻¹))⁻¹ = x :=
by simpa [l10] using l12 (z * (y * z * x)⁻¹) (y * z) x
lemma l23 : (x * y * (x * (y * z))⁻¹)⁻¹ = z := by simpa [l10] using l18 z (x * y) (y * z)
lemma l37 : x * y * x⁻¹ = y := by simpa [l23] using l16 x (x * x) (x * (x * y))⁻¹
lemma l39 : (z * y * (z * x)⁻¹)⁻¹ = x * y⁻¹ := by simpa [l12] using (l16 y (z * y) (z * x)⁻¹).symm
lemma l41 : x * (y * x * z)⁻¹ = (y * z)⁻¹ := by simpa [mccune] using l16 (y * x * z) y z
lemma l43 : x * (z * x⁻¹) = z := by simpa [l39] using l12 x x z
lemma l51 : (x * (x * z)⁻¹)⁻¹ = z := by simpa [l41] using l18 z x x
lemma l53 : x * (y * x)⁻¹ = y⁻¹ := by simpa [l37] using l37 (y * x) y⁻¹
lemma l55 : (y * z)⁻¹ = y⁻¹ * z⁻¹ := by simpa [l53, l37] using (l10 z (y * z)⁻¹ y z).symm
lemma l58 : x * y * z * x⁻¹ * y⁻¹ = z := by simpa [l37] using mccune (x * y) z x⁻¹
lemma l60 : x * (y⁻¹ * y⁻¹⁻¹) = x := by simpa [l37, l55] using mccune y x y⁻¹
lemma l64 : x⁻¹ * (x⁻¹⁻¹ * y⁻¹⁻¹) = y := by simpa [l55] using l51 x y
@[simp] lemma l85 : x⁻¹⁻¹ = x := by simpa [l43] using l64 x x
lemma l92 : x⁻¹ * (x * y) = y := by simpa using l64 x y
lemma l94 : x * (y⁻¹ * y) = x := by simpa using l60 x y
lemma l101 : x * (x⁻¹ * y) = y := by simpa using l92 x⁻¹ y
lemma l108 : x * y = y * x := by simpa [l92] using l37 y⁻¹ (y * x)
lemma l114 : x * (y * y⁻¹) = x := by simpa using l94 x y⁻¹
lemma l136 : x * x⁻¹ = y * y⁻¹ := by simpa [l114] using l101 x (y * y⁻¹)
lemma l172 : z * x * y * z⁻¹ = x * y := by simpa [l58] using (l43 x (z * x * y * z⁻¹)).symm
lemma l184 : x * y * z = z * x * y := by simpa [l92 z x] using l172 (z * x) y z⁻¹
lemma l244 : x * y * z = x * (y * z) := by simpa [l184 y] using (l108 x (y * z)).symm

/-- Every McCune comm group is a comm group. -/
instance : comm_group α :=
{ mul_assoc := l244,
  one := default α * (default α)⁻¹,
  mul_one := λ x, l114 x _,
  mul_comm := l108,
  mul_left_inv := λ x, (l108 _ x).trans (l136 x (default α)),
  one_mul := λ x, by rw [l108, l114],
  ..(by apply_instance : has_mul α),
  ..(by apply_instance : has_inv α) }

end mccune_comm_group

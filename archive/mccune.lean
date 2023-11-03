/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yury Kudryashov
-/

import algebra.group.basic

class mccune_group (G : Type*) extends has_mul G, has_inv G, inhabited G :=
(mccune (x y z u : G) : x * (y * (((z * z⁻¹) * (u * y)⁻¹) * x))⁻¹ = u)

namespace mccune_group
variables {G : Type*} [mccune_group G] (x y z u v w : G)

lemma l5 : x * (y * (z * z⁻¹ * (u * y)⁻¹ * x))⁻¹ = u := mccune _ _ _ _

lemma l7 : x * (y * y⁻¹ * (z * u)⁻¹ * (v * v⁻¹) * (z * x))⁻¹ = u :=
have v * v⁻¹ * (u * (y * y⁻¹ * (z * u)⁻¹ * (v * v⁻¹)))⁻¹ = z,
  from l5 (v * v⁻¹) u y z,
calc x * (y * y⁻¹ * (z * u)⁻¹ * (v * v⁻¹) * (z * x))⁻¹ =
  x * (y * y⁻¹ * (z * u)⁻¹ * (v * v⁻¹) *
    (v * v⁻¹ * (u * (y * y⁻¹ * (z * u)⁻¹ * (v * v⁻¹)))⁻¹ * x))⁻¹ :
  by rw this
... = u : l5 x (y * y⁻¹ * (z * u)⁻¹ * (v * v⁻¹)) v u

lemma l9 : x * (y * (z * z⁻¹) * (u * x))⁻¹ = v * v⁻¹ * (y * u)⁻¹ * (w * w⁻¹) :=
calc x * (y * (z * z⁻¹) * (u * x))⁻¹
   = x * (w * w⁻¹ * (u * (v * v⁻¹ * (y * u)⁻¹ * (w * w⁻¹)))⁻¹ * (z * z⁻¹) * (u * x))⁻¹ :
  by rw l5 (w * w⁻¹) u v y
... = v * v⁻¹ * (y * u)⁻¹ * (w * w⁻¹) :
  l7 x w u (v * v⁻¹ * (y * u)⁻¹ * (w * w⁻¹)) z

lemma l10 : y * y⁻¹ * (z * z⁻¹ * (u * x)⁻¹ * u)⁻¹ * (v * v⁻¹) = x :=
calc y * y⁻¹ * (z * z⁻¹ * (u * x)⁻¹ * u)⁻¹ * (v * v⁻¹)
    = x * (z * z⁻¹ * (u * x)⁻¹ * (x * x⁻¹) * (u * x))⁻¹ :
  (l9 x (z * z⁻¹ * (u * x)⁻¹) x u y v).symm
... = x : l7 x z u x x

lemma l12 : x * x⁻¹ * y⁻¹⁻¹ * (z * z⁻¹) = y :=
have x * x⁻¹ * (y * y⁻¹ * (y * y⁻¹)⁻¹ * y)⁻¹ * (y * y⁻¹ * (y * y⁻¹)⁻¹) = y⁻¹,
  from l10 y⁻¹ x y y (y * y⁻¹),
this ▸ l10 y x x (y * y⁻¹ * (y * y⁻¹)⁻¹) z

lemma l14 : x * x⁻¹ * (y * z)⁻¹ = u * u⁻¹ * (y * z)⁻¹ :=
have x * x⁻¹ * (u * u⁻¹ * (y * z)⁻¹ * y)⁻¹ * (x * x⁻¹) = z, from l10 z x u y x,
calc x * x⁻¹ * (y * z)⁻¹ = x * x⁻¹ * (y * (x * x⁻¹ * (u * u⁻¹ * (y * z)⁻¹ * y)⁻¹ * (x * x⁻¹)))⁻¹ :
  by rw this
... = u * u⁻¹ * (y * z)⁻¹ : l5 (x * x⁻¹) y x (u * u⁻¹ * (y * z)⁻¹)

lemma l15 : (x * x⁻¹) * y⁻¹ = (z * z⁻¹) * y⁻¹ :=
have A : x * x⁻¹ * y⁻¹⁻¹ * (z * z⁻¹) = y, from l12 x y z,
have B : x * x⁻¹ * (x * x⁻¹ * y⁻¹⁻¹ * (z * z⁻¹))⁻¹ = z * z⁻¹ * (x * x⁻¹ * y⁻¹⁻¹ * (z * z⁻¹))⁻¹,
  from l14 x ((x * x⁻¹) * y⁻¹⁻¹) (z * z⁻¹) z,
by rwa A at B

lemma l17 : u * u⁻¹ = v * v⁻¹ :=
have H : v * v⁻¹ * u⁻¹ = u * u⁻¹ * u⁻¹ := l15 v u u,
calc u * u⁻¹ = u * (u⁻¹ * (u * u⁻¹ * (u * u⁻¹ * u⁻¹)⁻¹ * u))⁻¹ : (l5 u u⁻¹ u (u * u⁻¹)).symm
... = u * (u⁻¹ * (u * u⁻¹ * (v * v⁻¹ * u⁻¹)⁻¹ * u))⁻¹          : by rw H
... = v * v⁻¹                                                  : l5 u u⁻¹ u (v * v⁻¹)

instance : has_one G := ⟨default * default⁻¹⟩

lemma mul_right_inv : u * u⁻¹ = 1 := l17 u default

lemma l20 : 1 * (1 * z)⁻¹ * 1 = z⁻¹ :=
calc 1 * (1 * z)⁻¹ * 1 = z * z⁻¹ * (z * z⁻¹ * (z * z⁻¹)⁻¹ * z)⁻¹ * (z * z⁻¹) :
  by rw [mul_right_inv, mul_right_inv]
... = z⁻¹ : l10 z⁻¹ z z z z

lemma l22 : x * (y⁻¹ * (1 * x))⁻¹ = y :=
calc x * (y⁻¹ * (1 * x))⁻¹ = x * (y⁻¹ * (x * x⁻¹ * (y * y⁻¹)⁻¹ * x))⁻¹ :
  by simp only [mul_right_inv]
... = y :  l5 x y⁻¹ x y

lemma l25 : x * (1⁻¹⁻¹ * (w * x))⁻¹ = w⁻¹ :=
calc x * (1⁻¹⁻¹ * (w * x))⁻¹ = x * ((1 * (1 * 1⁻¹)⁻¹ * 1) * (w * x))⁻¹ : by rw l20
... = x * (x * x⁻¹ * (w * w⁻¹)⁻¹ * (x * x⁻¹) * (w * x))⁻¹ :
  by simp only [mul_right_inv]
... = w⁻¹ : l7 x x w w⁻¹ x

lemma l32 : 1⁻¹ * (y⁻¹ * 1)⁻¹ = y :=
calc _ = 1⁻¹ * (y⁻¹ * (1 * 1⁻¹))⁻¹ : by simp only [mul_right_inv]
   ... = y                         : l22 1⁻¹ y

lemma l34 : x⁻¹ * (1⁻¹⁻¹ * 1)⁻¹ = x⁻¹ :=
calc x⁻¹ * (1⁻¹⁻¹ * 1)⁻¹ = x⁻¹ * (1⁻¹⁻¹ * (x * x⁻¹))⁻¹ : by rw mul_right_inv
                     ... = x⁻¹                         : l25 x⁻¹ x

lemma l36 : (1 * (x * 1⁻¹⁻¹)⁻¹)⁻¹ = x :=
calc (1 * (x * 1⁻¹⁻¹)⁻¹)⁻¹ = x * (1⁻¹⁻¹ * (1 * (x * 1⁻¹⁻¹)⁻¹ * x))⁻¹ :
  (l25 x (1 * (x * 1⁻¹⁻¹)⁻¹)).symm
... = x * (1⁻¹⁻¹ * (x * x⁻¹ * (x * 1⁻¹⁻¹)⁻¹ * x))⁻¹ :
  by rw mul_right_inv
... = x : l5 x 1⁻¹⁻¹ x x

lemma l44 : x * (1⁻¹⁻¹ * 1)⁻¹ = x :=
have A : (1 * (x * 1⁻¹⁻¹)⁻¹)⁻¹ * (1⁻¹⁻¹ * 1)⁻¹ = (1 * (x * 1⁻¹⁻¹)⁻¹)⁻¹ := l34 (1 * (x * 1⁻¹⁻¹)⁻¹),
have B : (1 * (x * 1⁻¹⁻¹)⁻¹)⁻¹ = x := l36 x,
B ▸ A

lemma l48 : (1 : G)⁻¹⁻¹ * 1 = 1 :=
calc (1 : G)⁻¹⁻¹ * 1 = (1 : G)⁻¹⁻¹ * 1 * (1⁻¹⁻¹ * 1)⁻¹ : (l44 ((1 : G)⁻¹⁻¹ * 1)).symm
                 ... = 1                               : mul_right_inv _

lemma l52 : x * 1⁻¹ = x :=
calc x * 1⁻¹ = x * (1⁻¹⁻¹ * 1)⁻¹ : by rw l48
         ... = x                 : l44 x

lemma l57 : (1⁻¹ * u)⁻¹⁻¹ = u :=
begin
  have A : u * u⁻¹ * (u * u⁻¹ * (1⁻¹ * u)⁻¹ * 1⁻¹)⁻¹ * (u * u⁻¹) = u := l10 u u u 1⁻¹ u,
  have B : 1 * (1⁻¹ * u)⁻¹ * 1⁻¹ = 1 * (1⁻¹ * u)⁻¹ := l52 (1 * (1⁻¹ * u)⁻¹),
  simp only [mul_right_inv, B] at A,
  calc (1⁻¹ * u)⁻¹⁻¹ = 1 * (1 * (1⁻¹ * u)⁻¹)⁻¹ * 1 : (l20 (1⁻¹ * u)⁻¹).symm
  ... = u : A
end

lemma l62 : (x⁻¹ * 1)⁻¹ = x⁻¹⁻¹ :=
calc (x⁻¹ * 1)⁻¹ = (1⁻¹ * (x⁻¹ * 1)⁻¹)⁻¹⁻¹ : (l57 (x⁻¹ * 1)⁻¹).symm
             ... = x⁻¹⁻¹                   : by rw [l32 x]

lemma l76 : (x * 1)⁻¹ = x⁻¹ :=
have A : (1⁻¹ * x)⁻¹⁻¹ = x, from l57 x,
have B : ((1⁻¹ * x)⁻¹⁻¹ * 1)⁻¹ = (1⁻¹ * x)⁻¹⁻¹⁻¹, from l62 (1⁻¹ * x)⁻¹,
by rwa A at B

lemma l88 : 1⁻¹ * x⁻¹⁻¹ = x :=
calc 1⁻¹ * x⁻¹⁻¹ = 1⁻¹ * (x⁻¹ * 1)⁻¹ : congr_arg2 (*) rfl (l76 x⁻¹).symm
             ... = x                 : l32 x

lemma mul_one : y * 1 = y :=
calc y * 1 = 1⁻¹ * (y * 1)⁻¹⁻¹ : (l88 (y * 1)).symm
       ... = 1⁻¹ * y⁻¹⁻¹       : by rw l76
       ... = y                 : l88 y

lemma one_inv_inv : (1 : G)⁻¹⁻¹ = 1 :=
calc (1 : G)⁻¹⁻¹ = 1⁻¹⁻¹ * 1 : (mul_one _).symm
             ... = 1         : l48

lemma one_inv : (1 : G)⁻¹ = 1 :=
calc (1 : G)⁻¹ = 1⁻¹ * 1⁻¹⁻¹ : by rw [one_inv_inv, mul_one]
           ... = 1           : l88 1

lemma l92 : (1 * x⁻¹)⁻¹ = x := 
calc _ = (1 * (x * 1⁻¹⁻¹)⁻¹)⁻¹ : by rw [one_inv_inv, mul_one]
... = x : l36 x

lemma mul_inv_cancel_right : y * z * z⁻¹ = y :=
calc y * z * z⁻¹ = (1 * (y * z)⁻¹)⁻¹ * (z * (z * z⁻¹ * (y * z)⁻¹ * (1 * (y * z)⁻¹)⁻¹))⁻¹ :
  by simp_rw [mul_right_inv, l92, mul_one]
... = y : l5 ((1 : G) * (y * z)⁻¹)⁻¹ z z y

lemma mul_inv_inv : x * y⁻¹⁻¹ = x * y :=
calc x * y⁻¹⁻¹ =  x * y * y⁻¹ * y⁻¹⁻¹ : congr_arg2 (*) (mul_inv_cancel_right x y).symm rfl
           ... = x * y                : mul_inv_cancel_right (x * y) y⁻¹

lemma one_mul : 1 * z = z :=
calc 1 * z = z * z⁻¹ * z⁻¹⁻¹ : by rw [mul_inv_inv, mul_right_inv]
       ... = z               : mul_inv_cancel_right z z⁻¹


lemma inv_inv : y⁻¹⁻¹ = y :=
calc y⁻¹⁻¹ = 1 * y⁻¹⁻¹ : (one_mul _).symm
       ... = 1 * y     : mul_inv_inv _ _
       ... = y         : one_mul y

lemma mul_left_inv : x⁻¹ * x = 1 :=
calc x⁻¹ * x = x⁻¹ * x⁻¹⁻¹ : (mul_inv_inv _ _).symm
         ... = 1           : mul_right_inv _

lemma mul_inv_rev : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
calc (x * y)⁻¹ = y⁻¹ * (1⁻¹⁻¹ * (x * y * y⁻¹))⁻¹ : (l25 y⁻¹ (x * y)).symm
           ... = y⁻¹ * x⁻¹                       : by rw [mul_inv_cancel_right, inv_inv, one_mul]

lemma mul_inv_cancel_left : x * (x⁻¹ * y) = y :=
calc x * (x⁻¹ * y) = x * (y⁻¹ * (x * x⁻¹ * (y * y⁻¹)⁻¹ * x))⁻¹ :
  by simp only [mul_right_inv, one_mul, mul_inv_rev, one_inv, inv_inv]
... = y : l5 x y⁻¹ x y


lemma l239 : x * (x⁻¹ * u * y) = u * y :=
calc x * (x⁻¹ * u * y) = x * (y⁻¹ * (x * x⁻¹ * (u * y * y⁻¹)⁻¹ * x))⁻¹ :
  by simp only [mul_inv_cancel_right, mul_right_inv, one_mul, mul_inv_rev, inv_inv]
... = u * y : l5 x y⁻¹ x (u * y)

lemma mul_assoc : x * y * z = x * (y * z) :=
calc x * y * z = x * (x⁻¹ * (x⁻¹⁻¹ * y * z)) : by rw [mul_inv_cancel_left, inv_inv]
           ... = x * (y * z)                 : by rw l239

/-- Every McCune group is a group. -/
instance : group G :=
{ mul_assoc := mul_assoc,
  one_mul := one_mul,
  mul_one := mul_one,
  mul_left_inv := mul_left_inv,
  .. mccune_group.has_one,
  .. ‹mccune_group G› }

end mccune_group

/-- Every group is a McCune group. -/
def mccune_group_of_group {G : Type*} [group G] : mccune_group G :=
{ mccune := λ x y z u, by simp [mul_assoc],
  default := 1 }

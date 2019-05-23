/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

Given a monoid `M` and an element `g ∈ M` satisfying `gⁿ = 1`, we
can interpret `gⁱ` for elements `i ∈ ℤ/n`.  We give several
different Lean versions of this idea.  Some of them involve
the type `zmod n`, which is Lean's implementation of `ℤ/n`.
Others involve the relation `a ≡ b [MOD n]` on `ℕ`, or the
relation `a ≡ b [ZMOD n]` on `ℤ`.
-/

import data.fintype algebra.group_power data.zmod.basic

variable n : ℕ+
section pow_mod

variables {M : Type*} [monoid M] (g : M)

def pow_mod : (zmod n) → M := λ i, g ^ i.val

@[simp] lemma one_pow_mod (i : zmod n) : pow_mod n 1 i = 1 :=
one_pow i.val

@[simp] lemma pow_mod_zero : pow_mod n g 0 = 1 := rfl

section with_exponent

variables {n} {g} (hg : g ^ (n : ℕ) = 1)
include hg

lemma pow_exponent (m : ℕ)  : (g ^ m) ^ (n : ℕ) = 1 :=
by {rw [← pow_mul, mul_comm, pow_mul, hg, one_pow]}

lemma pow_nat_mod (i : ℕ) : g ^ i = g ^ (i % n) :=
calc
  g ^ i = g ^ (i % (n : ℕ) + (n : ℕ) * (i / (n : ℕ))) :
   by {rw [nat.mod_add_div i (n : ℕ)],}
  ... = g ^ (i % (n : ℕ)) : by rw [pow_add, pow_mul, hg, one_pow, mul_one]

lemma pow_nat_congr {i j : ℕ} (e : i ≡ j [MOD n]) : g ^ i = g ^ j :=
begin
  change i % n = j % n at e,
  rw [pow_nat_mod hg i,pow_nat_mod hg j, e]
end

lemma pow_mod_exponent (m : zmod n) : (pow_mod n g m) ^ (n : ℕ) = 1 :=
pow_exponent hg m.val

@[simp] lemma pow_mod_coe_nat (i : ℕ) : pow_mod n g i = g ^ i :=
by {dsimp [pow_mod], rw [zmod.val_cast_nat, ← pow_nat_mod], exact hg}

@[simp] lemma pow_mod_one : pow_mod n g 1 = g :=
begin
  have := @pow_mod_coe_nat n _ _ g hg 1,
  rw [pow_one, nat.cast_one] at this,
  exact this
end

lemma pow_mod_add (i j : zmod n) :
 pow_mod n g (i + j) = (pow_mod n g i) * (pow_mod n g j) :=
begin
 dsimp [pow_mod],
 rw [← pow_add, zmod.add_val, ← pow_nat_mod hg],
end

lemma pow_mod_mul (i j : zmod n) :
 pow_mod n g (i * j) = pow_mod n (pow_mod n g i) j :=
begin
  dsimp [pow_mod],
  rw [← pow_mul, zmod.mul_val, ← pow_nat_mod hg],
end

end with_exponent
end pow_mod

section gpow_mod

variable {n}
variables {G : Type*} [group G] {g : G} (hg : g ^ (n : ℕ) = 1)
include hg

lemma gpow_exponent (m : ℤ) : (g ^ m) ^ (n : ℕ) = 1 :=
by {rw [← gpow_coe_nat, ← gpow_mul, mul_comm,
         gpow_mul, gpow_coe_nat, hg, one_gpow]}

lemma inv_exponent : (g⁻¹) ^ (n : ℕ) = 1 := by {rw [inv_pow,hg,one_inv]}

lemma gpow_nat_congr {i j : ℕ} (e : i ≡ j [MOD n]) : g ^ i = g ^ j :=
begin
  change i % n = j % n at e,
  rw [pow_nat_mod hg i, pow_nat_mod hg j, e]
end

lemma gpow_int_mod (i : ℤ) : g ^ i = g ^ (i % n).nat_abs :=
begin
  let n_Z := (n : ℤ),
  have : n_Z = ((n : ℕ) : ℤ) := rfl,
  have hg_Z : g ^ n_Z = 1 := by {rw [this, gpow_coe_nat], exact hg,},
  have n_nz : n_Z ≠ 0 := ne_of_gt (int.coe_nat_pos.mpr n.property),
  rw [← gpow_coe_nat, int.nat_abs_of_nonneg (int.mod_nonneg i n_nz)],
  exact calc
   g ^ i = g ^ (i % n_Z + n_Z * (i / n_Z)) :
    by rw [int.mod_add_div i n_Z]
   ... = g^(i % n_Z) :
    by {rw [gpow_add, gpow_mul, hg_Z, one_gpow, mul_one]}
end

lemma gpow_int_congr {i j : ℤ} (e : i ≡ j [ZMOD n]) : g ^ i = g ^ j :=
begin
  change i % n = j % n at e,
  rw [gpow_int_mod hg i, gpow_int_mod hg j,e]
end

@[simp] lemma gpow_mod_coe_int (i : ℤ) : pow_mod n g i = g ^ i :=
begin
  dsimp [pow_mod],
  have : ((n : ℕ) : ℤ) = (n : ℤ) := by simp,
  rw [zmod.val_cast_int, this, ← gpow_int_mod],
  exact hg,
end

@[simp] lemma gpow_mod_neg (i : zmod n) :
 pow_mod n g (- i) = (pow_mod n g i)⁻¹ :=
by {apply eq_inv_of_mul_eq_one,
    rw [← pow_mod_add hg, neg_add_self, pow_mod_zero]}

lemma gpow_mod_inv (i : zmod n) :
 pow_mod n g⁻¹ i = pow_mod n g (- i) :=
begin
 rw [gpow_mod_neg hg],
 apply eq_inv_of_mul_eq_one,
 dsimp [pow_mod],
 rw [inv_pow, mul_left_inv]
end

end gpow_mod

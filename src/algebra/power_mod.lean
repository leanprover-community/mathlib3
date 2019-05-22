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

variables {M : Type*} [monoid M] {g : M} (hg : g ^ n.val = 1)
include hg

lemma pow_exponent (m : ℕ) : (g ^ m) ^ n.val = 1 :=
by {rw[← pow_mul, mul_comm, pow_mul, hg, one_pow]}

lemma pow_nat_mod (i : ℕ) : g ^ i = g ^ (i % n) :=
calc
  g ^ i = g ^ (i % n.val + n.val * (i / n.val)) :
   congr_arg (has_pow.pow g) (nat.mod_add_div i n.val).symm
  ... = g ^ (i % n.val) : by rw[pow_add, pow_mul, hg, one_pow, mul_one]

lemma pow_nat_congr {i j : ℕ} (e : i ≡ j [MOD n]) : g ^ i = g ^ j :=
begin
  change i % n = j % n at e,
  rw[@pow_nat_mod n _ _ _ hg i,@pow_nat_mod n _ _ _ hg j, e]
end

def pow_mod : (zmod n) → M := λ i, g ^ i.val

lemma pow_mod_exponent (m : zmod n) : (pow_mod n hg m) ^ n.val = 1 :=
pow_exponent n hg m.val

@[simp] lemma pow_mod_coe_nat (i : ℕ) : pow_mod n hg i = g ^ i :=
by {dsimp[pow_mod], rw[zmod.val_cast_nat, ← pow_nat_mod], exact hg}

@[simp] lemma pow_mod_zero : pow_mod n hg 0 = 1 := rfl

@[simp] lemma pow_mod_one : pow_mod n hg 1 = g :=
begin
  have := @pow_mod_coe_nat n _ _ g hg 1,
  rw[pow_one, nat.cast_one] at this,
  exact this
end

@[simp] lemma one_pow_mod :
 ∀ {h : (1 : M) ^ (n : ℕ) = 1}, pow_mod n h 1 = 1
| h := by {dsimp[pow_mod], rw[one_pow]}

lemma pow_mod_add (i j : zmod n) :
 pow_mod n hg (i + j) = (pow_mod n hg i) * (pow_mod n hg j) :=
begin
 dsimp[pow_mod],
 rw[← pow_add, zmod.add_val],
 exact (pow_nat_mod n hg (i.val + j.val)).symm
end

lemma pow_mod_mul (i j : zmod n) :
 pow_mod n hg (i * j) = pow_mod n (pow_mod_exponent n hg i) j :=
begin
  dsimp[pow_mod],
  rw[← pow_mul, zmod.mul_val],
  exact (pow_nat_mod n hg (i.val * j.val)).symm,
end

end pow_mod

section gpow_mod

variables {G : Type*} [group G] {g : G} (hg : g ^ n.val = 1)
include hg

lemma gpow_exponent (m : ℤ) : (g ^ m) ^ n.val = 1 :=
by {rw[← gpow_coe_nat, ← gpow_mul, mul_comm,
         gpow_mul, gpow_coe_nat, hg, one_gpow]}

lemma inv_exponent : (g⁻¹) ^ n.val = 1 := by {rw[inv_pow,hg,one_inv]}

lemma gpow_nat_congr {i j : ℕ} (e : i ≡ j [MOD n]) : g ^ i = g ^ j :=
begin
  change i % n = j % n at e,
  rw[@pow_nat_mod n _ _ _ hg i, @pow_nat_mod n _ _ _ hg j,e]
end

lemma gpow_int_mod (i : ℤ) : g ^ i = g ^ (i % n).nat_abs :=
begin
  let n_Z := (n : ℤ),
  have : n_Z = ((n : ℕ) : ℤ) := rfl,
  have hg_Z : g ^ n_Z = 1 := by {rw[this, gpow_coe_nat], exact hg,},
  have n_nz : n_Z ≠ 0 := ne_of_gt (int.coe_nat_pos.mpr n.property),
  rw[← gpow_coe_nat, int.nat_abs_of_nonneg (int.mod_nonneg i n_nz)],
  exact calc
   g ^ i = g ^ (i % n_Z + n_Z * (i / n_Z)) :
    congr_arg (has_pow.pow g) (int.mod_add_div i n_Z).symm
   ... = g^(i % n_Z) :
    by {rw[gpow_add, gpow_mul, hg_Z, one_gpow, mul_one]}
end

lemma gpow_int_congr {i j : ℤ} (e : i ≡ j [ZMOD n]) : g ^ i = g ^ j :=
begin
  change i % n = j % n at e,
  rw[@gpow_int_mod n _ _ _ hg i,  @gpow_int_mod n _ _ _ hg j,e]
end

@[simp] lemma gpow_mod_coe_int (i : ℤ) : pow_mod n hg i = g ^ i :=
begin
  dsimp[pow_mod],
  have : ((n : ℕ) : ℤ) = (n : ℤ) := by simp,
  rw[zmod.val_cast_int, this, ← gpow_int_mod],
  exact hg,
end

@[simp] lemma gpow_mod_neg (i : zmod n) :
 pow_mod n hg (- i) = (pow_mod n hg i)⁻¹ :=
by {apply eq_inv_of_mul_eq_one,
    rw[← pow_mod_add, neg_add_self, pow_mod_zero]}

lemma gpow_mod_inv (i : zmod n) :
 pow_mod n (inv_exponent n hg) i = pow_mod n hg (- i) :=
begin
 rw[gpow_mod_neg],
 apply eq_inv_of_mul_eq_one,
 dsimp[pow_mod],
 rw[inv_pow,mul_left_inv]
end

end gpow_mod

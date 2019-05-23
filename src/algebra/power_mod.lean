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

import data.fintype algebra.group_power data.zmod.basic data.nat.modeq

section pow_congr_monoid

variables {n : ℕ} {M : Type*} [monoid M] {g : M} (hg : g ^ n = 1)
include hg

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

end pow_congr_monoid

section pow_congr_group

variables {n : ℕ} {G : Type*} [group G] {g : G} (hg : g ^ (n : ℕ) = 1)
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

lemma gpow_int_mod (i : ℤ) : g ^ i = g ^ (i % n) :=
by rw[← congr_arg ((^) g) (int.mod_add_div i n), gpow_add, gpow_mul,
      gpow_coe_nat, hg, one_gpow, mul_one]

lemma gpow_int_mod' (h : n > 0) (i : ℤ) : g ^ i = g ^ (i % n).nat_abs :=
begin
 have := int.mod_nonneg i (ne_of_gt (int.coe_nat_pos.mpr h)),
 have : ((i % n).nat_abs : ℤ) = i % n := int.of_nat_nat_abs_eq_of_nonneg this,
 rw[gpow_int_mod hg, ← gpow_coe_nat, this]
end

lemma gpow_int_congr {i j : ℤ} (e : i ≡ j [ZMOD n]) : g ^ i = g ^ j :=
begin
  change i % n = j % n at e,
  rw [gpow_int_mod hg i, gpow_int_mod hg j,e]
end

end pow_congr_group

variable n : ℕ+
section pow_mod

variables {M : Type*} [monoid M] (g : M)

instance : has_pow M (zmod n) := ⟨λ g i, g ^ (i : ℕ)⟩

theorem pow_mod_eq (i : zmod n) : g ^ i = g ^ (i : ℕ) := rfl

@[simp] lemma one_pow_mod (i : zmod n) : (1 : M) ^ i = 1 :=
one_pow i.val

@[simp] lemma pow_mod_zero : g ^ (0 : zmod n) = 1 := rfl

section with_exponent

variables {n} {g} (hg : g ^ (n : ℕ) = 1)
include hg

lemma pow_exponent (m : ℕ)  : (g ^ m) ^ (n : ℕ) = 1 :=
by {rw [← pow_mul, mul_comm, pow_mul, hg, one_pow]}

lemma pow_mod_exponent (m : zmod n) : (g ^ m) ^ (n : ℕ) = 1 :=
pow_exponent hg m.val

@[simp] lemma pow_mod_coe_nat (i : ℕ) : g ^ (i : zmod n) = g ^ i :=
by {rw [pow_mod_eq, zmod.coe_cast_nat, ← pow_nat_mod], exact hg}

@[simp] lemma pow_mod_one : g ^ (1 : zmod n) = g :=
begin
  have := pow_mod_coe_nat hg 1,
  rw [pow_one, nat.cast_one] at this,
  exact this
end

lemma pow_mod_add (i j : zmod n) : g ^ (i + j) = g ^ i * g ^ j :=
by rw [pow_mod_eq, pow_mod_eq, pow_mod_eq,
       ← pow_add, zmod.add_coe, ← pow_nat_mod hg]

lemma pow_mod_mul (i j : zmod n) : g ^ (i * j) = (g ^ i) ^ j :=
by rw [pow_mod_eq, pow_mod_eq, pow_mod_eq,
       ← pow_mul, zmod.mul_coe, ← pow_nat_mod hg]

end with_exponent
end pow_mod

section gpow_mod

variable {n}
variables {G : Type*} [group G] {g : G} (hg : g ^ (n : ℕ) = 1)
include hg

lemma gpow_mod_coe_int (i : ℤ) : g ^ (i : zmod n) = g ^ i :=
begin
  have : (((i : zmod n) : ℕ) : ℤ) = ((i : zmod n) : ℤ) := rfl,
  rw [pow_mod_eq, ← gpow_coe_nat, this],
  rw [@zmod.coe_cast_int' n i],
  have : ((n : ℕ) : ℤ) = (n : ℤ) := rfl,
  rw[← this, ← gpow_int_mod],
  exact hg
end

@[simp] lemma gpow_mod_neg (i : zmod n) : g ^ (- i) = (g ^ i)⁻¹ :=
by {apply eq_inv_of_mul_eq_one,
    rw [← pow_mod_add hg, neg_add_self, pow_mod_zero]}

lemma gpow_mod_inv (i : zmod n) : g⁻¹ ^ i = g ^ (- i) :=
begin
 rw [gpow_mod_neg hg],
 apply eq_inv_of_mul_eq_one,
 rw [pow_mod_eq, pow_mod_eq, inv_pow, mul_left_inv]
end

end gpow_mod

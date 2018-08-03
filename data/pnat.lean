/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import tactic.basic

/-- `ℕ+` is the type of positive natural numbers. It is defined as a subtype,
  and the VM representation of `ℕ+` is the same as `ℕ` because the proof
  is not stored. -/
def pnat := {n : ℕ // n > 0}
notation `ℕ+` := pnat

instance coe_pnat_nat : has_coe ℕ+ ℕ := ⟨subtype.val⟩

namespace nat

/-- Convert a natural number to a positive natural number. The
  positivity assumption is inferred by `dec_trivial`. -/
def to_pnat (n : ℕ) (h : n > 0 . tactic.exact_dec_trivial) : ℕ+ := ⟨n, h⟩

/-- Write a successor as an element of `ℕ+`. -/
def succ_pnat (n : ℕ) : ℕ+ := ⟨succ n, succ_pos n⟩

@[simp] theorem succ_pnat_coe (n : ℕ) : (succ_pnat n : ℕ) = succ n := rfl

/-- Convert a natural number to a pnat. `n+1` is mapped to itself,
  and `0` becomes `1`. -/
def to_pnat' (n : ℕ) : ℕ+ := succ_pnat (pred n)

end nat

namespace pnat

open nat
@[simp] theorem pos (n : ℕ+) : (n : ℕ) > 0 := n.2

theorem eq {m n : ℕ+} : (m : ℕ) = n → m = n := subtype.eq

@[simp] theorem mk_coe (n h) : ((⟨n, h⟩ : ℕ+) : ℕ) = n := rfl

instance : has_add ℕ+ := ⟨λ m n, ⟨m + n, add_pos m.2 n.2⟩⟩

@[simp] theorem add_coe (m n : ℕ+) : ((m + n : ℕ+) : ℕ) = m + n := rfl

@[simp] theorem ne_zero (n : ℕ+) : (n : ℕ) ≠ 0 := ne_of_gt n.2

@[simp] theorem to_pnat'_coe {n : ℕ} : n > 0 → (n.to_pnat' : ℕ) = n := succ_pred_eq_of_pos

@[simp] theorem coe_to_pnat' (n : ℕ+) : (n : ℕ).to_pnat' = n := eq (to_pnat'_coe n.pos)

instance : comm_monoid ℕ+ :=
{ mul       := λ m n, ⟨m.1 * n.1, mul_pos m.2 n.2⟩,
  mul_assoc := λ a b c, subtype.eq (mul_assoc _ _ _),
  one       := succ_pnat 0,
  one_mul   := λ a, subtype.eq (one_mul _),
  mul_one   := λ a, subtype.eq (mul_one _),
  mul_comm  := λ a b, subtype.eq (mul_comm _ _) }

@[simp] theorem one_coe : ((1 : ℕ+) : ℕ) = 1 := rfl

@[simp] theorem mul_coe (m n : ℕ+) : ((m * n : ℕ+) : ℕ) = m * n := rfl

/-- The power of a pnat and a nat is a pnat. -/
def pow (m : ℕ+) (n : ℕ) : ℕ+ :=
⟨m ^ n, nat.pos_pow_of_pos _ m.pos⟩

instance : has_pow ℕ+ ℕ := ⟨pow⟩

@[simp] theorem pow_coe (m : ℕ+) (n : ℕ) : (↑(m ^ n) : ℕ) = m ^ n := rfl

instance : has_repr ℕ+ := ⟨λ n, repr n.1⟩

end pnat

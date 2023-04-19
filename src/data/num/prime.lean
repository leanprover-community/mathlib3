/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.num.lemmas
import data.nat.prime
import tactic.ring

/-!
# Primality for binary natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines versions of `nat.min_fac` and `nat.prime` for `num` and `pos_num`. As with other
`num` definitions, they are not intended for general use (`nat` should be used instead of `num` in
most cases) but they can be used in contexts where kernel computation is required, such as proofs
by `rfl` and `dec_trivial`, as well as in `#reduce`.

The default decidable instance for `nat.prime` is optimized for VM evaluation, so it should be
preferred within `#eval` or in tactic execution, while for proofs the `norm_num` tactic can be used
to construct primality and non-primality proofs more efficiently than kernel computation.

Nevertheless, sometimes proof by computational reflection requires natural number computations, and
`num` implements algorithms directly on binary natural numbers for this purpose.
-/

namespace pos_num

/-- Auxiliary function for computing the smallest prime factor of a `pos_num`. Unlike
`nat.min_fac_aux`, we use a natural number `fuel` variable that is set to an upper bound on the
number of iterations. It is initialized to the number `n` we are determining primality for. Even
though this is exponential in the input (since it is a `nat`, not a `num`), it will get lazily
evaluated during kernel reduction, so we will only require about `sqrt n` unfoldings, for the
`sqrt n` iterations of the loop. -/
def min_fac_aux (n : pos_num) : ℕ → pos_num → pos_num
| 0 _ := n
| (fuel+1) k :=
  if h : n < k.bit1 * k.bit1 then n else
  if k.bit1 ∣ n then k.bit1 else
  min_fac_aux fuel k.succ

theorem min_fac_aux_to_nat {fuel:ℕ} {n k : pos_num} (h : nat.sqrt n < fuel + k.bit1) :
  (min_fac_aux n fuel k : ℕ) = nat.min_fac_aux n k.bit1 :=
begin
  induction fuel with fuel ih generalizing k; rw [min_fac_aux, nat.min_fac_aux],
  { rw if_pos, rwa [zero_add, nat.sqrt_lt] at h },
  rw [← mul_to_nat], simp only [cast_lt, dvd_to_nat, ite_cast],
  congr' 2,
  rw ih; [congr, convert nat.lt_succ_of_lt h using 1];
  simp only [_root_.bit1, _root_.bit0, cast_bit1, cast_succ,
    nat.succ_eq_add_one, add_assoc, add_left_comm]
end

/-- Returns the smallest prime factor of `n ≠ 1`. -/
def min_fac : pos_num → pos_num
| 1 := 1
| (bit0 n) := 2
| (bit1 n) := min_fac_aux (bit1 n) n 1

@[simp] theorem min_fac_to_nat (n : pos_num) : (min_fac n : ℕ) = nat.min_fac n :=
begin
  cases n, {refl},
  { rw [min_fac, nat.min_fac_eq, if_neg], swap, {simp},
    rw [min_fac_aux_to_nat], {refl},
    simp only [cast_one, cast_bit1],
    rw [nat.sqrt_lt],
    convert lt_add_of_pos_right _ (dec_trivial : (0:ℕ) < (n+4)*n + 8),
    unfold _root_.bit1 _root_.bit0, ring },
  { rw [min_fac, nat.min_fac_eq, if_pos], {refl},
    simp },
end

/-- Primality predicate for a `pos_num`. -/
@[simp] def prime (n : pos_num) : Prop := nat.prime n

instance decidable_prime : decidable_pred pos_num.prime
| 1 := decidable.is_false nat.not_prime_one
| (bit0 n) := decidable_of_iff' (n = 1) begin
    refine nat.prime_def_min_fac.trans ((and_iff_right _).trans $ eq_comm.trans _),
    { exact bit0_le_bit0.2 (to_nat_pos _) },
    rw [← min_fac_to_nat, to_nat_inj],
    exact ⟨bit0.inj, congr_arg _⟩,
  end
| (bit1 n) := decidable_of_iff' (min_fac_aux (bit1 n) n 1 = bit1 n) begin
    refine nat.prime_def_min_fac.trans ((and_iff_right _).trans _),
    { exact nat.bit0_le_bit1_iff.2 (to_nat_pos _) },
    rw [← min_fac_to_nat, to_nat_inj], refl,
  end

end pos_num

namespace num

/-- Returns the smallest prime factor of `n ≠ 1`. -/
def min_fac : num → pos_num
| 0 := 2
| (pos n) := n.min_fac

@[simp] theorem min_fac_to_nat : ∀ (n : num), (min_fac n : ℕ) = nat.min_fac n
| 0 := rfl
| (pos n) := pos_num.min_fac_to_nat _

/-- Primality predicate for a `num`. -/
@[simp] def prime (n : num) : Prop := nat.prime n

instance decidable_prime : decidable_pred num.prime
| 0 := decidable.is_false nat.not_prime_zero
| (pos n) := pos_num.decidable_prime n

end num

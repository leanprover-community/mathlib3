/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import data.int.basic
import data.nat.pow
import data.nat.size

/-!
# Bitwise operations on integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.


## Recursors
* `int.bit_cases_on`: Parity disjunction. Something is true/defined on `ℤ` if it's true/defined for
  even and for odd values.

-/

namespace int

/-! ### bitwise ops -/

@[simp] lemma bodd_zero : bodd 0 = ff := rfl
@[simp] lemma bodd_one : bodd 1 = tt := rfl
lemma bodd_two : bodd 2 = ff := rfl

@[simp, norm_cast] lemma bodd_coe (n : ℕ) : int.bodd n = nat.bodd n := rfl

@[simp] lemma bodd_sub_nat_nat (m n : ℕ) : bodd (sub_nat_nat m n) = bxor m.bodd n.bodd :=
by apply sub_nat_nat_elim m n (λ m n i, bodd i = bxor m.bodd n.bodd); intros;
  simp; cases i.bodd; simp

@[simp] lemma bodd_neg_of_nat (n : ℕ) : bodd (neg_of_nat n) = n.bodd :=
by cases n; simp; refl

@[simp] lemma bodd_neg (n : ℤ) : bodd (-n) = bodd n :=
by cases n; simp [has_neg.neg, int.coe_nat_eq, int.neg, bodd, -of_nat_eq_coe]

@[simp] lemma bodd_add (m n : ℤ) : bodd (m + n) = bxor (bodd m) (bodd n) :=
by cases m with m m; cases n with n n; unfold has_add.add;
  simp [int.add, -of_nat_eq_coe, bool.bxor_comm]

@[simp] lemma bodd_mul (m n : ℤ) : bodd (m * n) = bodd m && bodd n :=
by cases m with m m; cases n with n n;
  simp [← int.mul_def, int.mul, -of_nat_eq_coe, bool.bxor_comm]

theorem bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
| (n : ℕ) :=
  by rw [show (cond (bodd n) 1 0 : ℤ) = (cond (bodd n) 1 0 : ℕ),
         by cases bodd n; refl]; exact congr_arg of_nat n.bodd_add_div2
| -[1+ n] := begin
    refine eq.trans _ (congr_arg neg_succ_of_nat n.bodd_add_div2),
    dsimp [bodd], cases nat.bodd n; dsimp [cond, bnot, div2, int.mul],
    { change -[1+ 2 * nat.div2 n] = _, rw zero_add },
    { rw [zero_add, add_comm], refl }
  end

theorem div2_val : ∀ n, div2 n = n / 2
| (n : ℕ) := congr_arg of_nat n.div2_val
| -[1+ n] := congr_arg neg_succ_of_nat n.div2_val

lemma bit0_val (n : ℤ) : bit0 n = 2 * n := (two_mul _).symm

lemma bit1_val (n : ℤ) : bit1 n = 2 * n + 1 := congr_arg (+(1:ℤ)) (bit0_val _)

lemma bit_val (b n) : bit b n = 2 * n + cond b 1 0 :=
by { cases b, apply (bit0_val n).trans (add_zero _).symm, apply bit1_val }

lemma bit_decomp (n : ℤ) : bit (bodd n) (div2 n) = n :=
(bit_val _ _).trans $ (add_comm _ _).trans $ bodd_add_div2 _

/-- Defines a function from `ℤ` conditionally, if it is defined for odd and even integers separately
  using `bit`. -/
def {u} bit_cases_on {C : ℤ → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n :=
by rw [← bit_decomp n]; apply h

@[simp] lemma bit_zero : bit ff 0 = 0 := rfl

@[simp] lemma bit_coe_nat (b) (n : ℕ) : bit b n = nat.bit b n :=
by rw [bit_val, nat.bit_val]; cases b; refl

@[simp] lemma bit_neg_succ (b) (n : ℕ) : bit b -[1+ n] = -[1+ nat.bit (bnot b) n] :=
by rw [bit_val, nat.bit_val]; cases b; refl

@[simp] lemma bodd_bit (b n) : bodd (bit b n) = b :=
by rw bit_val; simp; cases b; cases bodd n; refl

@[simp] lemma bodd_bit0 (n : ℤ) : bodd (bit0 n) = ff := bodd_bit ff n

@[simp] lemma bodd_bit1 (n : ℤ) : bodd (bit1 n) = tt := bodd_bit tt n

lemma bit0_ne_bit1 (m n : ℤ) : bit0 m ≠ bit1 n :=
mt (congr_arg bodd) $ by simp

lemma bit1_ne_bit0 (m n : ℤ) : bit1 m ≠ bit0 n :=
(bit0_ne_bit1 _ _).symm

lemma bit1_ne_zero (m : ℤ) : bit1 m ≠ 0 :=
by simpa only [bit0_zero] using bit1_ne_bit0 m 0

@[simp] lemma test_bit_zero (b) : ∀ n, test_bit (bit b n) 0 = b
| (n : ℕ) := by rw [bit_coe_nat]; apply nat.test_bit_zero
| -[1+ n] := by rw [bit_neg_succ]; dsimp [test_bit]; rw [nat.test_bit_zero];
                clear test_bit_zero; cases b; refl

@[simp] lemma test_bit_succ (m b) : ∀ n, test_bit (bit b n) (nat.succ m) = test_bit n m
| (n : ℕ) := by rw [bit_coe_nat]; apply nat.test_bit_succ
| -[1+ n] := by rw [bit_neg_succ]; dsimp [test_bit]; rw [nat.test_bit_succ]

private meta def bitwise_tac : tactic unit := `[
  funext m,
  funext n,
  cases m with m m; cases n with n n; try {refl},
  all_goals
  { apply congr_arg of_nat <|> apply congr_arg neg_succ_of_nat,
    try {dsimp [nat.land, nat.ldiff, nat.lor]},
    try {rw [
      show nat.bitwise (λ a b, a && bnot b) n m =
           nat.bitwise (λ a b, b && bnot a) m n, from
      congr_fun (congr_fun (@nat.bitwise_swap (λ a b, b && bnot a) rfl) n) m]},
    apply congr_arg (λ f, nat.bitwise f m n),
    funext a,
    funext b,
    cases a; cases b; refl },
  all_goals {unfold nat.land nat.ldiff nat.lor}
]

theorem bitwise_or   : bitwise bor                  = lor   := by bitwise_tac
theorem bitwise_and  : bitwise band                 = land  := by bitwise_tac
theorem bitwise_diff : bitwise (λ a b, a && bnot b) = ldiff := by bitwise_tac
theorem bitwise_xor  : bitwise bxor                 = lxor  := by bitwise_tac

@[simp] lemma bitwise_bit (f : bool → bool → bool) (a m b n) :
  bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) :=
begin
  cases m with m m; cases n with n n;
  repeat { rw [← int.coe_nat_eq] <|> rw bit_coe_nat <|> rw bit_neg_succ };
  unfold bitwise nat_bitwise bnot;
  [ induction h : f ff ff,
    induction h : f ff tt,
    induction h : f tt ff,
    induction h : f tt tt ],
  all_goals
  { unfold cond, rw nat.bitwise_bit,
    repeat { rw bit_coe_nat <|> rw bit_neg_succ <|> rw bnot_bnot } },
  all_goals { unfold bnot {fail_if_unchanged := ff}; rw h; refl }
end

@[simp] lemma lor_bit (a m b n) : lor (bit a m) (bit b n) = bit (a || b) (lor m n) :=
by rw [← bitwise_or, bitwise_bit]

@[simp] lemma land_bit (a m b n) : land (bit a m) (bit b n) = bit (a && b) (land m n) :=
by rw [← bitwise_and, bitwise_bit]

@[simp] lemma ldiff_bit (a m b n) : ldiff (bit a m) (bit b n) = bit (a && bnot b) (ldiff m n) :=
by rw [← bitwise_diff, bitwise_bit]

@[simp] lemma lxor_bit (a m b n) : lxor (bit a m) (bit b n) = bit (bxor a b) (lxor m n) :=
by rw [← bitwise_xor, bitwise_bit]

@[simp] lemma lnot_bit (b) : ∀ n, lnot (bit b n) = bit (bnot b) (lnot n)
| (n : ℕ) := by simp [lnot]
| -[1+ n] := by simp [lnot]

@[simp] lemma test_bit_bitwise (f : bool → bool → bool) (m n k) :
  test_bit (bitwise f m n) k = f (test_bit m k) (test_bit n k) :=
begin
  induction k with k IH generalizing m n;
  apply bit_cases_on m; intros a m';
  apply bit_cases_on n; intros b n';
  rw bitwise_bit,
  { simp [test_bit_zero] },
  { simp [test_bit_succ, IH] }
end

@[simp] lemma test_bit_lor (m n k) : test_bit (lor m n) k = test_bit m k || test_bit n k :=
by rw [← bitwise_or, test_bit_bitwise]

@[simp] lemma test_bit_land (m n k) : test_bit (land m n) k = test_bit m k && test_bit n k :=
by rw [← bitwise_and, test_bit_bitwise]

@[simp]
lemma test_bit_ldiff (m n k) : test_bit (ldiff m n) k = test_bit m k && bnot (test_bit n k) :=
by rw [← bitwise_diff, test_bit_bitwise]

@[simp] lemma test_bit_lxor (m n k) : test_bit (lxor m n) k = bxor (test_bit m k) (test_bit n k) :=
by rw [← bitwise_xor, test_bit_bitwise]

@[simp] lemma test_bit_lnot : ∀ n k, test_bit (lnot n) k = bnot (test_bit n k)
| (n : ℕ) k := by simp [lnot, test_bit]
| -[1+ n] k := by simp [lnot, test_bit]

@[simp] lemma shiftl_neg (m n : ℤ) : shiftl m (-n) = shiftr m n := rfl
@[simp] lemma shiftr_neg (m n : ℤ) : shiftr m (-n) = shiftl m n := by rw [← shiftl_neg, neg_neg]

@[simp] lemma shiftl_coe_nat (m n : ℕ) : shiftl m n = nat.shiftl m n := rfl
@[simp] lemma shiftr_coe_nat (m n : ℕ) : shiftr m n = nat.shiftr m n := by cases n; refl

@[simp] lemma shiftl_neg_succ (m n : ℕ) : shiftl -[1+ m] n = -[1+ nat.shiftl' tt m n] := rfl
@[simp]
lemma shiftr_neg_succ (m n : ℕ) : shiftr -[1+ m] n = -[1+ nat.shiftr m n] := by cases n; refl

lemma shiftr_add : ∀ (m : ℤ) (n k : ℕ), shiftr m (n + k) = shiftr (shiftr m n) k
| (m : ℕ) n k := by rw [shiftr_coe_nat, shiftr_coe_nat,
                        ← int.coe_nat_add, shiftr_coe_nat, nat.shiftr_add]
| -[1+ m] n k := by rw [shiftr_neg_succ, shiftr_neg_succ,
                        ← int.coe_nat_add, shiftr_neg_succ, nat.shiftr_add]

/-! ### bitwise ops -/

local attribute [simp] int.zero_div

lemma shiftl_add : ∀ (m : ℤ) (n : ℕ) (k : ℤ), shiftl m (n + k) = shiftl (shiftl m n) k
| (m : ℕ) n (k:ℕ) := congr_arg of_nat (nat.shiftl_add _ _ _)
| -[1+ m] n (k:ℕ) := congr_arg neg_succ_of_nat (nat.shiftl'_add _ _ _ _)
| (m : ℕ) n -[1+k] := sub_nat_nat_elim n k.succ
    (λ n k i, shiftl ↑m i = nat.shiftr (nat.shiftl m n) k)
    (λ i n, congr_arg coe $
      by rw [← nat.shiftl_sub, add_tsub_cancel_left]; apply nat.le_add_right)
    (λ i n, congr_arg coe $
      by rw [add_assoc, nat.shiftr_add, ← nat.shiftl_sub, tsub_self]; refl)
| -[1+ m] n -[1+k] := sub_nat_nat_elim n k.succ
    (λ n k i, shiftl -[1+ m] i = -[1+ nat.shiftr (nat.shiftl' tt m n) k])
    (λ i n, congr_arg neg_succ_of_nat $
      by rw [← nat.shiftl'_sub, add_tsub_cancel_left]; apply nat.le_add_right)
    (λ i n, congr_arg neg_succ_of_nat $
      by rw [add_assoc, nat.shiftr_add, ← nat.shiftl'_sub, tsub_self]; refl)

lemma shiftl_sub (m : ℤ) (n : ℕ) (k : ℤ) : shiftl m (n - k) = shiftr (shiftl m n) k :=
shiftl_add _ _ _

lemma shiftl_eq_mul_pow : ∀ (m : ℤ) (n : ℕ), shiftl m n = m * ↑(2 ^ n)
| (m : ℕ) n := congr_arg coe (nat.shiftl_eq_mul_pow _ _)
| -[1+ m] n := @congr_arg ℕ ℤ _ _ (λi, -i) (nat.shiftl'_tt_eq_mul_pow _ _)

lemma shiftr_eq_div_pow : ∀ (m : ℤ) (n : ℕ), shiftr m n = m / ↑(2 ^ n)
| (m : ℕ) n := by rw shiftr_coe_nat; exact congr_arg coe (nat.shiftr_eq_div_pow _ _)
| -[1+ m] n := begin
  rw [shiftr_neg_succ, neg_succ_of_nat_div, nat.shiftr_eq_div_pow], refl,
  exact coe_nat_lt_coe_nat_of_lt (pow_pos dec_trivial _)
end

lemma one_shiftl (n : ℕ) : shiftl 1 n = (2 ^ n : ℕ) :=
congr_arg coe (nat.one_shiftl _)

@[simp] lemma zero_shiftl : ∀ n : ℤ, shiftl 0 n = 0
| (n : ℕ) := congr_arg coe (nat.zero_shiftl _)
| -[1+ n] := congr_arg coe (nat.zero_shiftr _)

@[simp] lemma zero_shiftr (n) : shiftr 0 n = 0 := zero_shiftl _

end int

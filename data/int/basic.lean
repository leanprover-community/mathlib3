/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The integers, with addition, multiplication, and subtraction.
-/
import data.nat.sub
open nat

namespace int

theorem of_nat_add_neg_succ_of_nat_of_lt {m n : ℕ} (h : m < succ n) : of_nat m + -[1+n] = -[1+ n - m] := 
begin
 change sub_nat_nat _ _ = _, 
 have h' : succ n - m = succ (n - m), 
 apply succ_sub,
 apply le_of_lt_succ h,
 simp [*, sub_nat_nat]
end

theorem of_nat_add_neg_succ_of_nat_of_ge {m n : ℕ} (h : m ≥ succ n) : of_nat m + -[1+n] = of_nat (m - succ n) := 
begin
 change sub_nat_nat _ _ = _,
 have h' : succ n - m = 0,
 apply sub_eq_zero_of_le h,
 simp [*, sub_nat_nat]
end

@[simp] lemma neg_add_neg (m n : ℕ) : -[1+m] + -[1+n] = -[1+nat.succ(m+n)] := rfl

end int

-- TODO: where to put these?
meta def simp_coe_attr : user_attribute :=
{ name     := `simp.coe,
  descr    := "rules for pushing coercions inwards"}

run_cmd attribute.register ``simp_coe_attr

meta def simp_coe_out_attr : user_attribute :=
{ name     := `simp.coe_out,
  descr    := "rules for pushing coercions outwards"}

run_cmd attribute.register ``simp_coe_out_attr

instance : inhabited ℤ := ⟨0⟩
meta instance : has_to_format ℤ := ⟨λ z, int.rec_on z (λ k, ↑k) (λ k, "-("++↑k++"+1)")⟩

/-

/- nat abs -/

theorem nat_abs_add_le (a b : ℤ) : nat_abs (a + b) ≤ nat_abs a + nat_abs b := sorry

theorem nat_abs_neg_of_nat (n : nat) : nat_abs (neg_of_nat n) = n :=
begin cases n, reflexivity, reflexivity end

section
local attribute nat_abs [reducible]
theorem nat_abs_mul : Π (a b : ℤ), nat_abs (a * b) = (nat_abs a) * (nat_abs b)
| (of_nat m) (of_nat n) := rfl
| (of_nat m) -[1+ n]    := by rewrite [mul_of_nat_neg_succ_of_nat, nat_abs_neg_of_nat]
| -[1+ m]    (of_nat n) := by rewrite [mul_neg_succ_of_nat_of_nat, nat_abs_neg_of_nat]
| -[1+ m]    -[1+ n]    := rfl
end

/- additional properties -/
theorem of_nat_sub {m n : ℕ} (H : m ≥ n) : of_nat (m - n) = of_nat m - of_nat n :=
have m - n + n = m,     from nat.sub_add_cancel H,
begin
  symmetry,
  apply sub_eq_of_eq_add,
  rewrite [←of_nat_add, this]
end

theorem neg_succ_of_nat_eq' (m : ℕ) : -[1+ m] = -m - 1 :=
by rewrite [neg_succ_of_nat_eq, neg_add]

def succ (a : ℤ) := a + (succ zero)
def pred (a : ℤ) := a - (succ zero)
def nat_succ_eq_int_succ (n : ℕ) : nat.succ n = int.succ n := rfl
theorem pred_succ (a : ℤ) : pred (succ a) = a := !sub_add_cancel
theorem succ_pred (a : ℤ) : succ (pred a) = a := !add_sub_cancel

theorem neg_succ (a : ℤ) : -succ a = pred (-a) :=
by rewrite [↑succ,neg_add]

theorem succ_neg_succ (a : ℤ) : succ (-succ a) = -a :=
by rewrite [neg_succ,succ_pred]

theorem neg_pred (a : ℤ) : -pred a = succ (-a) :=
by rewrite [↑pred,neg_sub,sub_eq_add_neg,add.comm]

theorem pred_neg_pred (a : ℤ) : pred (-pred a) = -a :=
by rewrite [neg_pred,pred_succ]

theorem pred_nat_succ (n : ℕ) : pred (nat.succ n) = n := pred_succ n
theorem neg_nat_succ (n : ℕ) : -nat.succ n = pred (-n) := !neg_succ
theorem succ_neg_nat_succ (n : ℕ) : succ (-nat.succ n) = -n := !succ_neg_succ

attribute [unfold 2]
def rec_nat_on {P : ℤ → Type} (z : ℤ) (H0 : P 0)
  (Hsucc : Π⦃n : ℕ⦄, P n → P (succ n)) (Hpred : Π⦃n : ℕ⦄, P (-n) → P (-nat.succ n)) : P z :=
int.rec (nat.rec H0 Hsucc) (λn, nat.rec H0 Hpred (nat.succ n)) z

--the only computation rule of rec_nat_on which is not defintional
theorem rec_nat_on_neg {P : ℤ → Type} (n : nat) (H0 : P zero)
  (Hsucc : Π⦃n : nat⦄, P n → P (succ n)) (Hpred : Π⦃n : nat⦄, P (-n) → P (-nat.succ n))
  : rec_nat_on (-nat.succ n) H0 Hsucc Hpred = Hpred (rec_nat_on (-n) H0 Hsucc Hpred) :=
nat.rec rfl (λn H, rfl) n

end int

-/

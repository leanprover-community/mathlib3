/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chris Hughes
-/
import data.int.modeq data.int.basic data.nat.modeq data.fintype data.nat.prime data.nat.gcd

class pos_nat (n : ℕ) := (pos : 0 < n)

attribute [class] nat.prime

instance pos_nat_of_prime (p : ℕ) [hp : nat.prime p] : pos_nat p := ⟨hp.pos⟩

open nat nat.modeq int

def Zmod := fin

namespace Zmod

instance {n : ℕ} : has_neg (Zmod n) :=
⟨λ a, ⟨nat_mod (-(a.1 : ℤ)) n, 
begin
  cases n with n,
  { exact (nat.not_lt_zero _ a.2).elim },
  { have h : (nat.succ n : ℤ) ≠ 0 := dec_trivial,
    rw [← int.coe_nat_lt, nat_mod, to_nat_of_nonneg (int.mod_nonneg _ h)],
    exact int.mod_lt _ h }
end⟩⟩

instance (n : ℕ) : add_comm_semigroup (Zmod n) :=
{ add := @has_add.add (fin n) fin.has_add,
  add_assoc := λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, fin.eq_of_veq 
    (show ((a + b) % n + c) ≡ (a + (b + c) % n) [MOD n], 
    from calc ((a + b) % n + c) ≡ a + b + c [MOD n] : modeq_add (nat.mod_mod _ _) rfl
      ... ≡ a + (b + c) [MOD n] : by rw add_assoc
      ... ≡ (a + (b + c) % n) [MOD n] : modeq_add rfl (nat.mod_mod _ _).symm),
  add_comm := λ ⟨a, _⟩ ⟨b, _⟩, fin.eq_of_veq (show (a + b) % n = (b + a) % n, by rw add_comm) }

instance (n : ℕ) : comm_semigroup (Zmod n) :=
{ mul := @has_mul.mul (fin n) fin.has_mul,
  mul_assoc := λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, fin.eq_of_veq
    (calc ((a * b) % n * c) ≡ a * b * c [MOD n] : modeq_mul (nat.mod_mod _ _) rfl
      ... ≡ a * (b * c) [MOD n] : by rw mul_assoc
      ... ≡ a * (b * c % n) [MOD n] : modeq_mul rfl (nat.mod_mod _ _).symm),
  mul_comm := λ ⟨a, _⟩ ⟨b, _⟩, fin.eq_of_veq (show (a * b) % n = (b * a) % n, by rw mul_comm) }

instance (n : ℕ) [h0 : pos_nat n] : has_one (Zmod n) := ⟨⟨1 % n, nat.mod_lt _ h0.pos⟩⟩

instance (n : ℕ) [h0 : pos_nat n] : has_zero (Zmod n) := ⟨⟨0, h0.pos⟩⟩

private lemma one_mul_aux (n : ℕ) [h0 : pos_nat n] : ∀ a : Zmod n, (1 : Zmod n) * a = a := 
λ ⟨a, ha⟩, fin.eq_of_veq (show (1 % n * a) % n = a, 
begin
  resetI,
  clear _fun_match,
  cases n with n,
  { simp },
  { cases n with n,
    { rw [nat.mod_self, zero_mul];
      exact (nat.eq_zero_of_le_zero (le_of_lt_succ ha)).symm },
    { have h : 1 < n + 2 := dec_trivial,
      have ha : a < succ (succ n) := ha,
      rw [nat.mod_eq_of_lt h, one_mul, nat.mod_eq_of_lt ha] } }
end)

private lemma left_distrib_aux (n : ℕ) : ∀ a b c : Zmod n, a * (b + c) = a * b + a * c :=
λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, fin.eq_of_veq
(calc a * ((b + c) % n) ≡ a * (b + c) [MOD n] : modeq_mul rfl (nat.mod_mod _ _)
  ... ≡ a * b + a * c [MOD n] : by rw mul_add
  ... ≡ (a * b) % n + (a * c) % n [MOD n] : modeq_add (nat.mod_mod _ _).symm (nat.mod_mod _ _).symm)

instance (n : ℕ) : distrib (Zmod n) :=
{ left_distrib := left_distrib_aux n,
  right_distrib := λ a b c, by rw [mul_comm, left_distrib_aux, mul_comm _ b, mul_comm]; refl,
  ..Zmod.add_comm_semigroup n,
  ..Zmod.comm_semigroup n }

instance (n : ℕ) [h0 : pos_nat n] : comm_ring (Zmod n) :=
{ zero_add := λ ⟨a, ha⟩, fin.eq_of_veq (show (0 + a) % n = a, by rw zero_add; exact nat.mod_eq_of_lt ha),
  add_zero := λ ⟨a, ha⟩, fin.eq_of_veq (nat.mod_eq_of_lt ha),
  add_left_neg := 
    λ ⟨a, ha⟩, fin.eq_of_veq (show (((-a : ℤ) % n).to_nat + a) % n = 0,
      from int.coe_nat_inj
      begin
        have hn : (n : ℤ) ≠ 0 := (ne_of_lt (int.coe_nat_lt.2 h0.pos)).symm,
        rw [int.coe_nat_mod, int.coe_nat_add, to_nat_of_nonneg (int.mod_nonneg _ hn), add_comm],
        simp,
      end),
  one_mul := one_mul_aux n,
  mul_one := λ a, by rw mul_comm; exact one_mul_aux n a,
  ..Zmod.has_zero n,
  ..Zmod.has_one n,
  ..Zmod.has_neg,
  ..Zmod.distrib n,
  ..Zmod.add_comm_semigroup n,
  ..Zmod.comm_semigroup n }

@[simp] lemma val_zero (n : ℕ) [pos_nat n] : (0 : Zmod n).val = 0 := rfl

lemma add_val {n : ℕ} : ∀ a b : Zmod n, (a + b).val = (a.val + b.val) % n
| ⟨_, _⟩ ⟨_, _⟩ := rfl

lemma mul_val {n : ℕ} :  ∀ a b : Zmod n, (a + b).val = (a.val + b.val) % n
| ⟨_, _⟩ ⟨_, _⟩ := rfl

lemma cast_val_nat {n : ℕ} [pos_nat n] (a : ℕ) : (a : Zmod n).val = a % n :=
begin
  induction a with a ih,
  { rw [nat.zero_mod]; refl },
  { rw [succ_eq_add_one, nat.cast_add, add_val, ih],
    show (a % n + ((0 + (1 % n)) % n)) % n = (a + 1) % n,
    rw [zero_add, nat.mod_mod],
    exact nat.modeq.modeq_add (nat.mod_mod a n) (nat.mod_mod 1 n) }
end

lemma mk_eq_cast {a n : ℕ} (h : a < n) [pos_nat n] : (⟨a, h⟩ : Zmod n) = (a : Zmod n) :=
fin.eq_of_veq (by rw [cast_val_nat, nat.mod_eq_of_lt h])

@[simp] lemma cast_self_eq_zero (n : ℕ) [pos_nat n] : (n : Zmod n) = 0 :=
fin.eq_of_veq (show (n : Zmod n).val = 0, by simp [cast_val_nat])

lemma cast_val_of_lt {a n : ℕ} (h : a < n) [pos_nat n] : (a : Zmod n).val = a :=
by rw [cast_val_nat, nat.mod_eq_of_lt h]

@[simp] lemma cast_nat_mod (n : ℕ) [pos_nat n] (a : ℕ) : ((a % n : ℕ) : Zmod n) = a :=
by conv {to_rhs, rw ← nat.mod_add_div a n}; simp
 
@[simp] lemma cast_int_mod (n : ℕ) [pos_nat n] (a : ℤ) : ((a % n : ℤ) : Zmod n) = a :=
by conv {to_rhs, rw ← int.mod_add_div a n}; simp

lemma cast_val_int (n : ℕ) [h0 : pos_nat n] (a : ℤ) : (a : Zmod n).val = (a % n).nat_abs :=
have h : nat_abs (a % n) < n := int.coe_nat_lt.1 begin 
  rw [nat_abs_of_nonneg (mod_nonneg _ (int.coe_nat_ne_zero_iff_pos.2 h0.pos))],
  conv {to_rhs, rw ← abs_of_nonneg (int.coe_nat_nonneg n)},
  exact int.mod_lt _ (int.coe_nat_ne_zero_iff_pos.2 h0.pos)
end,
int.coe_nat_inj $ 
 by conv {to_lhs, rw [← cast_int_mod n a, 
    ← nat_abs_of_nonneg (mod_nonneg _ (int.coe_nat_ne_zero_iff_pos.2 h0.pos)),
    int.cast_coe_nat, cast_val_of_lt h] }

instance Zmod_one.subsingleton : subsingleton (Zmod 1) := 
⟨λ a b, fin.eq_of_veq (by rw [eq_zero_of_le_zero (le_of_lt_succ a.2), 
  eq_zero_of_le_zero (le_of_lt_succ b.2)])⟩

instance Zmod_zero.subsingleton : subsingleton (Zmod 0) :=
⟨λ a, (nat.not_lt_zero _ a.2).elim⟩

lemma eq_iff_modeq_nat {n : ℕ} [pos_nat n] {a b : ℕ} : (a : Zmod n) = b ↔ a ≡ b [MOD n] :=
⟨λ h, by have := fin.veq_of_eq h;
  rwa [cast_val_nat, cast_val_nat] at this,
λ h, fin.eq_of_veq $ by rwa [cast_val_nat, cast_val_nat]⟩

lemma eq_iff_modeq_int {n : ℕ} [h0 : pos_nat n] {a b : ℤ} : (a : Zmod n) = b ↔ a ≡ b [ZMOD n] :=
⟨λ h, by have := fin.veq_of_eq h;
  rwa [cast_val_int, cast_val_int, ← int.coe_nat_eq_coe_nat_iff,
    nat_abs_of_nonneg (int.mod_nonneg _ (int.coe_nat_ne_zero_iff_pos.2 h0.pos)),
    nat_abs_of_nonneg (int.mod_nonneg _ (int.coe_nat_ne_zero_iff_pos.2 h0.pos))] at this,
λ h : a % n = b % n, 
  by rw [← cast_int_mod n a, ← cast_int_mod n b, h]⟩ 

instance (n : ℕ) : fintype (Zmod n) := fin.fintype _

lemma card_Zmod : ∀ n, fintype.card (Zmod n) = n := fintype.card_fin

instance (n : ℕ) [pos_nat n] : has_inv (Zmod n) := 
⟨λ a, gcd_a a.1 n⟩

lemma gcd_a_modeq (a b : ℕ) : (a : ℤ) * gcd_a a b ≡ nat.gcd a b [ZMOD b] :=
by rw [← add_zero ((a : ℤ) * _), gcd_eq_gcd_ab];
  exact int.modeq.modeq_add rfl (int.modeq.modeq_zero_iff.2 (dvd_mul_right _ _)).symm

lemma mul_inv_eq_gcd (n a : ℕ) [pos_nat n]: (a : Zmod n) * a⁻¹ = nat.gcd a n :=
by rw [← int.cast_coe_nat (nat.gcd _ _), nat.gcd_comm, nat.gcd_rec, ← eq_iff_modeq_int.2 (gcd_a_modeq _ _)];
  simp [has_inv.inv, cast_val_nat]

private lemma mul_inv_cancel_aux {p : ℕ} [hp : prime p] : ∀ a : Zmod p, a ≠ 0 → a * a⁻¹ = 1 :=
λ ⟨a, hap⟩ ha0, begin
  rw [mk_eq_cast, ne.def, ← nat.cast_zero, eq_iff_modeq_nat, modeq_zero_iff] at ha0,
  have : nat.gcd p a = 1 := (prime.coprime_iff_not_dvd hp).2 ha0,
  rw [mk_eq_cast hap, mul_inv_eq_gcd, gcd_comm, this, nat.cast_one],
end

instance {p : ℕ} [hp : prime p] : discrete_field (Zmod p) :=
{ zero_ne_one := fin.ne_of_vne $ show 0 ≠ 1 % p, 
    by rw nat.mod_eq_of_lt hp.gt_one; exact zero_ne_one,
  mul_inv_cancel := mul_inv_cancel_aux,
  inv_mul_cancel := λ a, by rw mul_comm; exact mul_inv_cancel_aux _,
  has_decidable_eq := by apply_instance,
  inv_zero := show (gcd_a 0 p : Zmod p) = 0,
    by unfold gcd_a xgcd xgcd_aux; refl,
  ..Zmod.comm_ring p,
  ..Zmod.has_inv p }

end Zmod
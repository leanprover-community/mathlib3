/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chris Hughes
-/
import data.int.modeq data.int.gcd data.fintype data.pnat

open nat nat.modeq int

def zmod (n : ℕ+) := fin n

namespace zmod

instance (n : ℕ+) : has_neg (zmod n) :=
⟨λ a, ⟨nat_mod (-(a.1 : ℤ)) n,
  have h : (n : ℤ) ≠ 0 := int.coe_nat_ne_zero_iff_pos.2 n.pos,
  have h₁ : ((n : ℕ) : ℤ) = abs n := (abs_of_nonneg (int.coe_nat_nonneg n)).symm,
  by rw [← int.coe_nat_lt, nat_mod, to_nat_of_nonneg (int.mod_nonneg _ h), h₁];
    exact int.mod_lt _ h⟩⟩

instance (n : ℕ+) : add_comm_semigroup (zmod n) :=
{ add_assoc := λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, fin.eq_of_veq
    (show ((a + b) % n + c) ≡ (a + (b + c) % n) [MOD n],
    from calc ((a + b) % n + c) ≡ a + b + c [MOD n] : modeq_add (nat.mod_mod _ _) rfl
      ... ≡ a + (b + c) [MOD n] : by rw add_assoc
      ... ≡ (a + (b + c) % n) [MOD n] : modeq_add rfl (nat.mod_mod _ _).symm),
  add_comm := λ ⟨a, _⟩ ⟨b, _⟩, fin.eq_of_veq (show (a + b) % n = (b + a) % n, by rw add_comm),
  ..fin.has_add }

instance (n : ℕ+) : comm_semigroup (zmod n) :=
{ mul_assoc := λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, fin.eq_of_veq
    (calc ((a * b) % n * c) ≡ a * b * c [MOD n] : modeq_mul (nat.mod_mod _ _) rfl
      ... ≡ a * (b * c) [MOD n] : by rw mul_assoc
      ... ≡ a * (b * c % n) [MOD n] : modeq_mul rfl (nat.mod_mod _ _).symm),
  mul_comm := λ ⟨a, _⟩ ⟨b, _⟩, fin.eq_of_veq (show (a * b) % n = (b * a) % n, by rw mul_comm),
  ..fin.has_mul }

instance (n : ℕ+) : has_one (zmod n) := ⟨⟨(1 % n), nat.mod_lt _ n.pos⟩⟩

instance (n : ℕ+) : has_zero (zmod n) := ⟨⟨0, n.pos⟩⟩

instance zmod_one.subsingleton : subsingleton (zmod 1) :=
⟨λ a b, fin.eq_of_veq (by rw [eq_zero_of_le_zero (le_of_lt_succ a.2),
  eq_zero_of_le_zero (le_of_lt_succ b.2)])⟩

lemma add_val {n : ℕ+} : ∀ a b : zmod n, (a + b).val = (a.val + b.val) % n
| ⟨_, _⟩ ⟨_, _⟩ := rfl

lemma mul_val {n : ℕ+} :  ∀ a b : zmod n, (a * b).val = (a.val * b.val) % n
| ⟨_, _⟩ ⟨_, _⟩ := rfl

lemma one_val {n : ℕ+} : (1 : zmod n).val = 1 % n := rfl

@[simp] lemma zero_val (n : ℕ+) : (0 : zmod n).val = 0 := rfl

private lemma one_mul_aux (n : ℕ+) (a : zmod n) : (1 : zmod n) * a = a :=
begin
  cases n with n hn,
  cases n with n,
  { exact (lt_irrefl _ hn).elim },
  { cases n with n,
    { exact @subsingleton.elim (zmod 1) _ _ _ },
    { have h₁ : a.1 % n.succ.succ = a.1 := nat.mod_eq_of_lt a.2,
      have h₂ : 1 % n.succ.succ = 1 := nat.mod_eq_of_lt dec_trivial,
      refine fin.eq_of_veq _,
      simp [mul_val, one_val, h₁, h₂] } }
end

private lemma left_distrib_aux (n : ℕ+) : ∀ a b c : zmod n, a * (b + c) = a * b + a * c :=
λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, fin.eq_of_veq
(calc a * ((b + c) % n) ≡ a * (b + c) [MOD n] : modeq_mul rfl (nat.mod_mod _ _)
  ... ≡ a * b + a * c [MOD n] : by rw mul_add
  ... ≡ (a * b) % n + (a * c) % n [MOD n] : modeq_add (nat.mod_mod _ _).symm (nat.mod_mod _ _).symm)

instance (n : ℕ+) : comm_ring (zmod n) :=
{ zero_add := λ ⟨a, ha⟩, fin.eq_of_veq (show (0 + a) % n = a, by rw zero_add; exact nat.mod_eq_of_lt ha),
  add_zero := λ ⟨a, ha⟩, fin.eq_of_veq (nat.mod_eq_of_lt ha),
  add_left_neg :=
    λ ⟨a, ha⟩, fin.eq_of_veq (show (((-a : ℤ) % n).to_nat + a) % n = 0,
      from int.coe_nat_inj
      begin
        have hn : (n : ℤ) ≠ 0 := (ne_of_lt (int.coe_nat_lt.2 n.pos)).symm,
        rw [int.coe_nat_mod, int.coe_nat_add, to_nat_of_nonneg (int.mod_nonneg _ hn), add_comm],
        simp,
      end),
  one_mul := one_mul_aux n,
  mul_one := λ a, by rw mul_comm; exact one_mul_aux n a,
  left_distrib := left_distrib_aux n,
  right_distrib := λ a b c, by rw [mul_comm, left_distrib_aux, mul_comm _ b, mul_comm]; refl,
  ..zmod.has_zero n,
  ..zmod.has_one n,
  ..zmod.has_neg n,
  ..zmod.add_comm_semigroup n,
  ..zmod.comm_semigroup n }

lemma val_cast_nat {n : ℕ+} (a : ℕ) : (a : zmod n).val = a % n :=
begin
  induction a with a ih,
  { rw [nat.zero_mod]; refl },
  { rw [succ_eq_add_one, nat.cast_add, add_val, ih],
    show (a % n + ((0 + (1 % n)) % n)) % n = (a + 1) % n,
    rw [zero_add, nat.mod_mod],
    exact nat.modeq.modeq_add (nat.mod_mod a n) (nat.mod_mod 1 n) }
end

lemma mk_eq_cast {n : ℕ+} {a : ℕ} (h : a < n) : (⟨a, h⟩ : zmod n) = (a : zmod n) :=
fin.eq_of_veq (by rw [val_cast_nat, nat.mod_eq_of_lt h])

@[simp] lemma cast_self_eq_zero {n : ℕ+} : ((n : ℕ) : zmod n) = 0 :=
fin.eq_of_veq (show (n : zmod n).val = 0, by simp [val_cast_nat])

lemma val_cast_of_lt {n : ℕ+} {a : ℕ} (h : a < n) : (a : zmod n).val = a :=
by rw [val_cast_nat, nat.mod_eq_of_lt h]

@[simp] lemma cast_mod_nat (n : ℕ+) (a : ℕ) : ((a % n : ℕ) : zmod n) = a :=
by conv {to_rhs, rw ← nat.mod_add_div a n}; simp

@[simp] lemma cast_val {n : ℕ+} (a : zmod n) : (a.val : zmod n) = a :=
by cases a; simp [mk_eq_cast]

@[simp] lemma cast_mod_int (n : ℕ+) (a : ℤ) : ((a % (n : ℕ) : ℤ) : zmod n) = a :=
by conv {to_rhs, rw ← int.mod_add_div a n}; simp

lemma val_cast_int {n : ℕ+} (a : ℤ) : (a : zmod n).val = (a % (n : ℕ)).nat_abs :=
have h : nat_abs (a % (n : ℕ)) < n := int.coe_nat_lt.1 begin
  rw [nat_abs_of_nonneg (mod_nonneg _ (int.coe_nat_ne_zero_iff_pos.2 n.pos))],
  conv {to_rhs, rw ← abs_of_nonneg (int.coe_nat_nonneg n)},
  exact int.mod_lt _ (int.coe_nat_ne_zero_iff_pos.2 n.pos)
end,
int.coe_nat_inj $
  by conv {to_lhs, rw [← cast_mod_int n a,
    ← nat_abs_of_nonneg (mod_nonneg _ (int.coe_nat_ne_zero_iff_pos.2 n.pos)),
    int.cast_coe_nat, val_cast_of_lt h] }

lemma eq_iff_modeq_nat {n : ℕ+} {a b : ℕ} : (a : zmod n) = b ↔ a ≡ b [MOD n] :=
⟨λ h, by have := fin.veq_of_eq h;
  rwa [val_cast_nat, val_cast_nat] at this,
λ h, fin.eq_of_veq $ by rwa [val_cast_nat, val_cast_nat]⟩

lemma eq_iff_modeq_int {n : ℕ+} {a b : ℤ} : (a : zmod n) = b ↔ a ≡ b [ZMOD (n : ℕ)] :=
⟨λ h, by have := fin.veq_of_eq h;
  rwa [val_cast_int, val_cast_int, ← int.coe_nat_eq_coe_nat_iff,
    nat_abs_of_nonneg (int.mod_nonneg _ (int.coe_nat_ne_zero_iff_pos.2 n.pos)),
    nat_abs_of_nonneg (int.mod_nonneg _ (int.coe_nat_ne_zero_iff_pos.2 n.pos))] at this,
λ h : a % (n : ℕ) = b % (n : ℕ),
  by rw [← cast_mod_int n a, ← cast_mod_int n b, h]⟩

instance (n : ℕ+) : fintype (zmod n) := fin.fintype _

lemma card_zmod (n : ℕ+) : fintype.card (zmod n) = n := fintype.card_fin n

end zmod

def zmodp (p : ℕ) (hp : prime p) : Type := zmod ⟨p, hp.pos⟩

namespace zmodp

variables {p : ℕ} (hp : prime p)

instance : comm_ring (zmodp p hp) := zmod.comm_ring ⟨p, hp.pos⟩

instance {p : ℕ} (hp : prime p) : has_inv (zmodp p hp) :=
⟨λ a, gcd_a a.1 p⟩

lemma add_val : ∀ a b : zmodp p hp, (a + b).val = (a.val + b.val) % p
| ⟨_, _⟩ ⟨_, _⟩ := rfl

lemma mul_val : ∀ a b : zmodp p hp, (a * b).val = (a.val * b.val) % p
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp] lemma one_val : (1 : zmodp p hp).val = 1 :=
nat.mod_eq_of_lt hp.gt_one

@[simp] lemma zero_val : (0 : zmodp p hp).val = 0 := rfl

lemma val_cast_nat (a : ℕ) : (a : zmodp p hp).val = a % p :=
@zmod.val_cast_nat ⟨p, hp.pos⟩ _

lemma mk_eq_cast {a : ℕ} (h : a < p) : (⟨a, h⟩ : zmodp p hp) = (a : zmodp p hp) :=
@zmod.mk_eq_cast ⟨p, hp.pos⟩ _ _

@[simp] lemma cast_self_eq_zero: (p : zmodp p hp) = 0 :=
fin.eq_of_veq (by simpa [val_cast_nat])

lemma val_cast_of_lt {a : ℕ} (h : a < p) : (a : zmodp p hp).val = a :=
@zmod.val_cast_of_lt ⟨p, hp.pos⟩ _ h

@[simp] lemma cast_mod_nat (a : ℕ) : ((a % p : ℕ) : zmodp p hp) = a :=
@zmod.cast_mod_nat ⟨p, hp.pos⟩ _

@[simp] lemma cast_val (a : zmodp p hp) : (a.val : zmodp p hp) = a :=
@zmod.cast_val ⟨p, hp.pos⟩ _

@[simp] lemma cast_mod_int (a : ℤ) : ((a % p : ℤ) : zmodp p hp) = a :=
@zmod.cast_mod_int ⟨p, hp.pos⟩ _

lemma val_cast_int (a : ℤ) : (a : zmodp p hp).val = (a % p).nat_abs :=
@zmod.val_cast_int ⟨p, hp.pos⟩ _

lemma eq_iff_modeq_nat {a b : ℕ} : (a : zmodp p hp) = b ↔ a ≡ b [MOD p] :=
@zmod.eq_iff_modeq_nat ⟨p, hp.pos⟩ _ _

lemma eq_iff_modeq_int {a b : ℤ} : (a : zmodp p hp) = b ↔ a ≡ b [ZMOD p] :=
@zmod.eq_iff_modeq_int ⟨p, hp.pos⟩ _ _

lemma gcd_a_modeq (a b : ℕ) : (a : ℤ) * gcd_a a b ≡ nat.gcd a b [ZMOD b] :=
by rw [← add_zero ((a : ℤ) * _), gcd_eq_gcd_ab];
  exact int.modeq.modeq_add rfl (int.modeq.modeq_zero_iff.2 (dvd_mul_right _ _)).symm

lemma mul_inv_eq_gcd (a : ℕ) : (a : zmodp p hp) * a⁻¹ = nat.gcd a p :=
by rw [← int.cast_coe_nat (nat.gcd _ _), nat.gcd_comm, nat.gcd_rec, ← (eq_iff_modeq_int _).2 (gcd_a_modeq _ _)];
  simp [has_inv.inv, val_cast_nat]

private lemma mul_inv_cancel_aux : ∀ a : zmodp p hp, a ≠ 0 → a * a⁻¹ = 1 :=
λ ⟨a, hap⟩ ha0, begin
  rw [mk_eq_cast, ne.def, ← @nat.cast_zero (zmodp p hp), eq_iff_modeq_nat, modeq_zero_iff] at ha0,
  have : nat.gcd p a = 1 := (prime.coprime_iff_not_dvd hp).2 ha0,
  rw [mk_eq_cast _ hap, mul_inv_eq_gcd, nat.gcd_comm],
  simpa [nat.gcd_comm, this]
end

instance : discrete_field (zmodp p hp) :=
{ zero_ne_one := fin.ne_of_vne $ show 0 ≠ 1 % p,
    by rw nat.mod_eq_of_lt hp.gt_one;
      exact zero_ne_one,
  mul_inv_cancel := mul_inv_cancel_aux hp,
  inv_mul_cancel := λ a, by rw mul_comm; exact mul_inv_cancel_aux hp _,
  has_decidable_eq := by apply_instance,
  inv_zero := show (gcd_a 0 p : zmodp p hp) = 0,
    by unfold gcd_a xgcd xgcd_aux; refl,
  ..zmodp.comm_ring hp,
  ..zmodp.has_inv hp }

end zmodp
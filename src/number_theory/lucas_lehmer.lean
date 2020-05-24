/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Reid Barton, Bhavik Mehta, Scott Morrison, Ainsley Pahljina
-/
import data.nat.prime
import data.zmod.basic
import algebra.pi_instances
import group_theory.order_of_element
import ring_theory.fintype

open nat (prime)

/- Additions to Mathlib -/

namespace nat

lemma one_le_pow (n m : ℕ) (h : 0 < m) : 1 ≤ m^n :=
begin
  induction n with n ih,
  { exact le_refl _, },
  { calc 1 ≤ m^n : ih
       ... ≤ m^n * m : (@le_mul_iff_one_le_right ℕ _ m (m^n) ih).mpr h },
end
lemma one_le_pow' (n m : ℕ) : 1 ≤ (m+1)^n := one_le_pow n (m+1) (succ_pos m)
lemma one_le_two_pow (n : ℕ) : 1 ≤ 2^n := one_le_pow n 2 dec_trivial

lemma one_lt_pow (n m : ℕ) (h₀ : 0 < n) (h₁ : 1 < m) : 1 < m^n :=
begin
  induction n with n ih,
  { cases h₀, },
  { calc 1 ≤ m^n : one_le_pow n m (lt_of_succ_lt h₁)
       ... < m^n * m : (lt_mul_iff_one_lt_right (by exact one_le_pow n m (lt_of_succ_lt h₁))).mpr h₁ }
end
lemma one_lt_pow' (n m : ℕ) : 1 < (m+2)^(n+1) :=
  one_lt_pow (n+1) (m+2) (succ_pos n) (nat.lt_of_sub_eq_succ rfl)
lemma one_lt_two_pow (n : ℕ) (h₀ : 0 < n) : 1 < 2^n := one_lt_pow n 2 h₀ dec_trivial
lemma one_lt_two_pow' (n : ℕ) : 1 < 2^(n+1) := one_lt_pow (n+1) 2 (succ_pos n) dec_trivial

lemma lt_two_pow (n : ℕ) : n < 2^n :=
lt_pow_self dec_trivial n

lemma two_not_dvd_odd (a : ℕ) : ¬(2 ∣ 2 * a + 1) :=
begin
  intro h,
  cases h with b h,
  replace h := congr_arg (λ n, n % 2) h,
  simp only [add_mod, mod_mod, mul_mod_right, zero_add] at h,
  cases h,
end
lemma two_not_dvd_odd' (a : ℕ) (w : 0 < a) : ¬(2 ∣ 2 * a - 1) :=
begin
  cases a,
  { cases w, },
  { exact two_not_dvd_odd a, }
end

end nat

lemma char_p.int_coe_eq_int_coe_iff (R : Type*) [ring R] (p : ℕ) [char_p R p] (a b : ℤ) :
  (a : R) = b ↔ a ≡ b [ZMOD p] :=
begin
  rw eq_comm,
  rw ←sub_eq_zero,
  rw ←int.cast_sub,
  rw char_p.int_cast_eq_zero_iff R p,
  rw int.modeq.modeq_iff_dvd,
end

lemma zmod.int_coe_eq_int_coe_iff (a b : ℤ) (c : ℕ) :
  (a : zmod c) = (b : zmod c) ↔ a ≡ b [ZMOD c] :=
char_p.int_coe_eq_int_coe_iff (zmod c) c a b

lemma zmod.nat_coe_eq_nat_coe_iff (a b c : ℕ) :
  (a : zmod c) = (b : zmod c) ↔ a ≡ b [MOD c] :=
begin
  convert zmod.int_coe_eq_int_coe_iff a b c,
  simp [nat.modeq.modeq_iff_dvd, int.modeq.modeq_iff_dvd],
end

@[simp]
lemma int_coe_zmod_eq_zero_iff_dvd (a : ℤ) (b : ℕ) : (a : zmod b) = 0 ↔ (b : ℤ) ∣ a :=
begin
  change (a : zmod b) = ((0 : ℤ) : zmod b) ↔ (b : ℤ) ∣ a,
  rw zmod.int_coe_eq_int_coe_iff,
  rw int.modeq.modeq_zero_iff,
end

@[simp]
lemma nat_coe_zmod_eq_zero_iff_dvd (a b : ℕ) : (a : zmod b) = 0 ↔ b ∣ a :=
begin
  change (a : zmod b) = ((0 : ℕ) : zmod b) ↔ b ∣ a,
  rw zmod.nat_coe_eq_nat_coe_iff,
  rw nat.modeq.modeq_zero_iff,
end

@[push_cast]
lemma mod_coe_zmod (a : ℤ) (b : ℕ) : ((a % b : ℤ) : zmod b) = (a : zmod b) :=
begin
  rw zmod.int_coe_eq_int_coe_iff,
  apply int.modeq.mod_modeq,
end


section Mersenne
open nat

/- Defining the Mersenne Numbers -/

def M (p : ℕ) : ℕ := 2^p - 1

lemma M_pos {p : ℕ} (h : 0 < p) : 0 < M p :=
begin
  dsimp [M],
  calc 0 < 2^1 - 1 : by norm_num
     ... ≤ 2^p - 1 : nat.pred_le_pred (pow_le_pow_of_le_right (succ_pos 1) h)
end

end Mersenne

def s : ℕ → ℤ
| 0 := 4
| (i+1) := (s i)^2 - 2

def s_zmod (p : ℕ) : ℕ → zmod (2^p - 1)
| 0 := 4
| (i+1) := (s_zmod i)^2 - 2

def s_mod (p : ℕ) : ℕ → ℤ
| 0 := 4 % (2^p - 1)
| (i+1) := ((s_mod i)^2 - 2) % (2^p - 1)

lemma Mersenne_int_ne_zero (p : ℕ) (w : 0 < p) : (2^p - 1 : ℤ) ≠ 0 :=
begin
  apply ne_of_gt, simp only [gt_iff_lt, sub_pos],
  exact_mod_cast nat.one_lt_two_pow p w,
end

lemma s_mod_nonneg (p : ℕ) (w : 0 < p) (i : ℕ) : 0 ≤ s_mod p i :=
begin
  cases i; dsimp [s_mod],
  { trivial, },
  { apply int.mod_nonneg, exact Mersenne_int_ne_zero p w },
end

lemma s_mod_mod (p i : ℕ) : s_mod p i % (2^p - 1) = s_mod p i :=
by cases i; { dsimp [s_mod], simp, }

lemma s_mod_lt (p : ℕ) (w : 0 < p) (i : ℕ) : s_mod p i < 2^p - 1 :=
begin
  rw ←s_mod_mod,
  convert int.mod_lt _ _,
  { refine (abs_of_nonneg _).symm,
    simp only [sub_nonneg, ge_iff_le],
    exact_mod_cast nat.one_le_two_pow p, },
  { exact Mersenne_int_ne_zero p w, },
end

lemma s_zmod_eq_s (p' : ℕ) (i : ℕ) : s_zmod (p'+2) i = (s i : zmod (2^(p'+2) - 1)):=
begin
  induction i with i ih,
  { dsimp [s, s_zmod], norm_num, },
  { dsimp [s, s_zmod],
    push_cast,
    rw ih, },
end


/- Lucas Lehmer Residue -/

def Lucas_Lehmer_residue (p : ℕ) : zmod (2^p - 1) := s_zmod p (p-2)

-- These next two don't make good `norm_cast` lemmas.
lemma int.coe_nat_pow_pred (b p : ℕ) (w : 0 < b) : ((b^p - 1 : ℕ) : ℤ) = (b^p - 1 : ℤ) :=
begin
  have : 1 ≤ b^p := nat.one_le_pow p b w,
  simp only [this] with push_cast, -- `push_cast` should allow extra lemmas
end
lemma int.coe_nat_two_pow_pred (p : ℕ) : ((2^p - 1 : ℕ) : ℤ) = (2^p - 1 : ℤ) :=
int.coe_nat_pow_pred 2 p dec_trivial

lemma s_zmod_eq_s_mod (p : ℕ) (w : 1 < p) (i : ℕ) : s_zmod p i = (s_mod p i : zmod (2^p - 1)) :=
begin
  induction i with i ih;
  -- { dsimp [s_mod, s_zmod], norm_num, },
  { dsimp [s_mod, s_zmod],
    -- unfortunately this is too complicated for `push_cast` to handle on its own...
    rw ←int.coe_nat_two_pow_pred p,
    push_cast;
    rw ih, },
end

lemma int.nat_abs_lt_nat_abs_of_nonneg_of_lt {a b : ℤ} (w₁ : 0 ≤ a) (w₂ : a < b) :
  a.nat_abs < b.nat_abs :=
begin
  lift b to ℕ using le_of_lt (lt_of_le_of_lt w₁ w₂),
  lift a to ℕ using w₁,
  simpa using w₂,
end

lemma int.eq_zero_of_dvd_of_lt {a b : ℤ} (w₁ : 0 ≤ a) (w₂ : a < b) (h : b ∣ a) : a = 0 :=
begin
  apply int.eq_zero_of_dvd_of_nat_abs_lt_nat_abs h,
  exact int.nat_abs_lt_nat_abs_of_nonneg_of_lt w₁ w₂,
end

lemma residue_eq_zero_iff_s_mod_eq_zero (p : ℕ) (w : 1 < p) :
  Lucas_Lehmer_residue p = 0 ↔ s_mod p (p-2) = 0 :=
begin
  dsimp [Lucas_Lehmer_residue],
  -- We want to use that fact that `s_mod p (p-2) < 2^p - 1`
  -- to show that the coercion into `zmod (2^p - 1)` is injective,
  -- and then use the previous lemma.
  rw s_zmod_eq_s_mod p w,
  split,
  { intro h,
    simp at h,
    apply int.eq_zero_of_dvd_of_lt _ _ h; clear h,
    apply s_mod_nonneg _ (nat.lt_of_succ_lt w),
    convert s_mod_lt _ (nat.lt_of_succ_lt w) (p-2),
    simp only [nat.one_le_two_pow p] with push_cast,
    refl, },
  { intro h, rw h, simp, },
end

@[derive decidable_pred]
def Lucas_Lehmer_test (p : ℕ) := Lucas_Lehmer_residue p = 0

-- q is defined as the minimum factor of (M p)
def q (p : ℕ) : ℕ+ := ⟨nat.min_fac (M p), by exact nat.min_fac_pos (M p)⟩

/- X q : the group of tuples (a,b) taken modulo q, of the form a + 3^(1/2) b -/

@[derive [add_comm_group, decidable_eq]]
def X (q : ℕ+) := (zmod q) × (zmod q)

namespace X
variable {q : ℕ+}

@[ext]
lemma ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y :=
begin
  cases x, cases y,
  congr; assumption
end

@[simp] lemma add_fst (x y : X q) : (x + y).1 = x.1 + y.1 := rfl
@[simp] lemma add_snd (x y : X q) : (x + y).2 = x.2 + y.2 := rfl

@[simp] lemma neg_fst (x : X q) : (-x).1 = -x.1 := rfl
@[simp] lemma neg_snd (x : X q) : (-x).2 = -x.2 := rfl

instance : has_mul (X q) :=
{ mul := λ x y, (x.1*y.1 + 3*x.2*y.2, x.1*y.2 + x.2*y.1) }

@[simp] lemma mul_fst (x y : X q) : (x * y).1 = x.1 * y.1 + 3 * x.2 * y.2 := rfl
@[simp] lemma mul_snd (x y : X q) : (x * y).2 = x.1 * y.2 + x.2 * y.1 := rfl

instance : has_one (X q) :=
{ one := ⟨1,0⟩ }

@[simp] lemma one_fst : (1 : X q).1 = 1 := rfl
@[simp] lemma one_snd : (1 : X q).2 = 0 := rfl

@[simp] lemma bit0_fst (x : X q) : (bit0 x).1 = bit0 x.1 := rfl
@[simp] lemma bit0_snd (x : X q) : (bit0 x).2 = bit0 x.2 := rfl
@[simp] lemma bit1_fst (x : X q) : (bit1 x).1 = bit1 x.1 := rfl
@[simp] lemma bit1_snd (x : X q) : (bit1 x).2 = bit0 x.2 := by { dsimp [bit1], simp, }

instance : monoid (X q) :=
{ mul_assoc := λ x y z, by { ext; { dsimp, ring }, },
  one := ⟨1,0⟩,
  one_mul := λ x, by { ext; simp, },
  mul_one := λ x, by { ext; simp, },
  ..(infer_instance : has_mul (X q)) }

lemma left_distrib (x y z : X q) : x * (y + z) = x * y + x * z :=
by { ext; { dsimp, ring }, }

lemma right_distrib (x y z : X q) : (x + y) * z = x * z + y * z :=
by { ext; { dsimp, ring }, }

instance : ring (X q) :=
{ left_distrib := left_distrib,
  right_distrib := right_distrib,
  ..(infer_instance : add_comm_group (X q)),
  ..(infer_instance : monoid (X q)) }

instance : comm_ring (X q) :=
{ mul_comm := λ x y, by { ext; { dsimp, ring }, },
  ..(infer_instance : ring (X q))}

instance [fact (1 < (q : ℕ))] : nonzero_comm_ring (X q) :=
{ zero_ne_one := λ h, begin injection h, exact @zero_ne_one (zmod q) _ h_1, end,
  ..(infer_instance : comm_ring (X q)) }

instance fintype_zmod_pnat : fintype (zmod q) :=
begin
  rcases q with ⟨q,p⟩, cases q,
  { exfalso, cases p, },
  { dsimp [zmod],
    apply_instance, },
end

instance fintype_X : fintype (X q) :=
begin
  dsimp [X],
  apply_instance,
end

instance fact_pnat_pos : fact ((0 : ℕ) < q) :=
q.2

/-- The cardinality of the group `zmod q` is q. -/
lemma fin_zmod : fintype.card (zmod q) = q :=
by convert zmod.card q

/-- The cardinality of X is q^2. -/
lemma X_card : fintype.card (X q) = q^2 :=
begin
  dsimp [X],
  simp only [fintype.card_prod, fin_zmod],
  ring,
end


-- For the purpose of this we do not need to produce the list of units so leave as non-computable
noncomputable instance fintype_units : fintype (units (X q)) :=
fintype.of_injective (coe : units (X q) → (X q)) units.ext

/- The cardinality of the units is less than q^2.
Mathematically the cardinality of the units will be
less than or equal to the cardinality of X q. However 0 in X q,
is a known element without an inverse, thus the inequality holds.
-/
lemma units_card (w : 1 < q) : fintype.card (units (X q)) < q^2 :=
begin
  haveI : fact (1 < (q : ℕ)) := w,
  convert card_units_lt (X q),
  rw X_card,
end

@[simp]
lemma nat_coe_fst (n : ℕ) : (n : X q).fst = (n : zmod q) :=
begin
  induction n,
  { refl, },
  { dsimp, simp only [add_left_inj], exact n_ih, }
end
@[simp]
lemma nat_coe_snd (n : ℕ) : (n : X q).snd = (0 : zmod q) :=
begin
  induction n,
  { refl, },
  { dsimp, simp only [add_zero], exact n_ih, }
end

@[simp]
lemma int_coe_fst (n : ℤ) : (n : X q).fst = (n : zmod q) :=
by { induction n; simp, }
@[simp]
lemma int_coe_snd (n : ℤ) : (n : X q).snd = (0 : zmod q) :=
by { induction n; simp, }

@[norm_cast]
lemma coe_mul (n m : ℤ) : ((n * m : ℤ) : X q) = (n : X q) * (m : X q) :=
by { ext; simp; ring }

@[norm_cast]
lemma coe_nat (n : ℕ) : ((n : ℤ) : X q) = (n : X q) :=
by { ext; simp, }

def ω : X q := (2, 1)
def ωb : X q := (2, -1)

lemma ω_mul_ωb (q : ℕ+): (ω : X q) * ωb = 1 :=
begin
  dsimp [ω, ωb],
  ext; simp; ring,
end

lemma ωb_mul_ω (q : ℕ+): (ωb : X q) * ω = 1 :=
begin
  dsimp [ω, ωb],
  ext; simp; ring,
end

/- Closed form solution for the recurrence relation -/

lemma closed_form (i : ℕ) : (s i : X q) = (ω : X q)^(2^i) + (ωb : X q)^(2^i) :=
begin
  induction i with i ih,
  { dsimp [s, ω, ωb],
    ext; { simp; refl, }, },
  { calc (s (i + 1) : X q) = ((s i)^2 - 2 : ℤ) : rfl
    ... = ((s i : X q)^2 - 2) : by push_cast
    ... = (ω^(2^i) + ωb^(2^i))^2 - 2 : by rw ih
    ... = (ω^(2^i))^2 + (ωb^(2^i))^2 + 2*(ωb^(2^i)*ω^(2^i)) - 2 : by ring
    ... = (ω^(2^i))^2 + (ωb^(2^i))^2 :
            by rw [←mul_pow ωb ω, ωb_mul_ω, one_pow, mul_one, add_sub_cancel]
    ... = ω^(2^(i+1)) + ωb^(2^(i+1)) : by rw [←pow_mul, ←pow_mul, nat.pow_succ] }
end


end X

open X
section residue_zero



/-- If 1 < p, then `q p`, the smallest prime factor of `M p`, is more than 2. -/
lemma two_lt_q (p' : ℕ) : 2 < q (p'+2) := begin
  by_contradiction,
  simp at a,
  interval_cases q (p'+2); clear a,
  { -- If q = 1, we get a contradiction from 2^p = 2
    dsimp [q] at h, injection h with h', clear h,
    simp [M] at h',
    exact lt_irrefl 2
    (calc 2 ≤ p'+2    : nat.le_add_left _ _
      ...  < 2^(p'+2) : nat.lt_two_pow _
      ...  = 2        : nat.pred_inj (nat.one_le_two_pow _) dec_trivial h'), },
  { -- If q = 2, we get a contradiction from 2 ∣ 2^p - 1
    dsimp [q] at h, injection h with h', clear h,
    rw [M, pnat.one_coe, nat.min_fac_eq_two_iff, nat.pow_succ, nat.mul_comm] at h',
    exact nat.two_not_dvd_odd' (2^(p'+1)) (nat.one_le_two_pow _) h', }
end

theorem ω_pow_formula (p' : ℕ) (h : Lucas_Lehmer_residue (p'+2) = 0) :
  ∃ (k : ℤ), (ω : X (q (p'+2)))^(2^(p'+1)) = k * (M (p'+2)) * ((ω : X (q (p'+2)))^(2^p')) - 1 :=
begin
  dsimp [Lucas_Lehmer_residue] at h,
  rw s_zmod_eq_s p' at h,
  simp at h,
  cases h with k h,
  use k,
  replace h := congr_arg (λ (n : ℤ), (n : X (q (p'+2)))) h, -- coercion from ℤ to X q
  dsimp at h,
  rw closed_form at h,
  replace h := congr_arg (λ x, ω^2^p' * x) h,
  dsimp at h,
  have t : 2^p' + 2^p' = 2^(p'+1) := by ring_exp,
  rw [mul_add, ←pow_add ω, t, ←mul_pow ω ωb (2^p'), ω_mul_ωb, one_pow] at h,
  rw [mul_comm, coe_mul] at h,
  rw [mul_comm _ (k : X (q (p'+2)))] at h,
  replace h := eq_sub_of_add_eq h,
  exact_mod_cast h,
end

/-- `q` is the minimum factor of M p, so `M p = 0` in `X q`. -/
theorem Mersenne_coe_X (p : ℕ) : (M p : X (q p)) = 0 :=
begin
  ext; simp [M, q],
  apply nat.min_fac_dvd,
end

theorem ω_pow_eq_neg_one (p' : ℕ) (h : Lucas_Lehmer_residue (p'+2) = 0) :
  (ω : X (q (p'+2)))^(2^(p'+1)) = -1 :=
begin
  cases ω_pow_formula p' h with k w,
  rw [Mersenne_coe_X] at w,
  simpa using w,
end

lemma nat.succ_pred (n : ℕ) (w : 0 < n) : (n - 1) + 1 = n := nat.pred_inj (nat.succ_pos _) w rfl

theorem ω_pow_eq_one (p' : ℕ) (h : Lucas_Lehmer_residue (p'+2) = 0) :
  (ω : X (q (p'+2)))^(2^(p'+2)) = 1 :=
calc (ω : X (q (p'+2)))^2^(p'+2) = (ω^(2^(p'+1)))^2 : by rw [←pow_mul, ←nat.pow_succ, nat.succ_eq_add_one]
         ... = (-1)^2 : by rw ω_pow_eq_neg_one p' h
         ... = 1      : by simp

def ω_unit (p : ℕ) : units (X (q p)) :=
{ val := ω,
  inv := ωb,
  val_inv := by simp [ω_mul_ωb],
  inv_val := by simp [ωb_mul_ω], }

@[simp] lemma ω_unit_coe (p : ℕ) : (ω_unit p : X (q p)) = ω := rfl

/-- The order of ω in the unit group is exactly 2^p. -/
theorem order_ω (p' : ℕ) (h : Lucas_Lehmer_residue (p'+2) = 0) :
  order_of (ω_unit (p'+2)) = 2^(p'+2) :=
begin
  apply nat.eq_prime_pow_of_dvd_least_prime_pow, -- the order of ω divides 2^p
  { norm_num, },
  { intro o,
    have ω_pow := order_of_dvd_iff_pow_eq_one.1 o,
    replace ω_pow := congr_arg (units.coe_hom (X (q (p'+2))) : units (X (q (p'+2))) → X (q (p'+2))) ω_pow,
    simp at ω_pow,
    have h : (1 : zmod (q (p'+2))) = -1 :=
      congr_arg (prod.fst) ((ω_pow.symm).trans (ω_pow_eq_neg_one p' h)),
    haveI : fact (2 < (q (p'+2) : ℕ)) := two_lt_q _,
    apply zmod.neg_one_ne_one h.symm, },
  { apply order_of_dvd_iff_pow_eq_one.2,
    apply units.ext,
    push_cast,
    exact ω_pow_eq_one p' h, }
end

lemma order_ineq (p' : ℕ) (h : Lucas_Lehmer_residue (p'+2) = 0) : 2^(p'+2) < (q (p'+2) : ℕ)^2 :=
calc 2^(p'+2) = order_of (ω_unit (p'+2)) : (order_ω p' h).symm
     ... ≤ fintype.card (units (X _))    : order_of_le_card_univ
     ... < (q (p'+2) : ℕ)^2              : units_card (nat.lt_of_succ_lt (two_lt_q _))

end residue_zero

theorem Lucas_Lehmer_sufficiency (p : ℕ) (w : 1 < p) : Lucas_Lehmer_test p → prime (M p) :=
begin
  let p' := p - 2,
  have z : p = p' + 2 := (nat.sub_eq_iff_eq_add w).mp rfl,
  have w : 1 < p' + 2 := (nat.lt_of_sub_eq_succ rfl),
  contrapose,
  intros a t,
  rw z at a,
  rw z at t,
  have h₁ := order_ineq p' t,
  have h₂ := nat.min_fac_sq_le_self (M (p'+2)) (M_pos (nat.lt_of_succ_lt w)) a,
  have h := lt_of_lt_of_le h₁ h₂,
  exact not_lt_of_ge (nat.sub_le _ _) h,
end

-- Here we calculate the residue, very inefficiently, using `dec_trivial`. We can do much better.
example : prime (M 5) := Lucas_Lehmer_sufficiency 5 (by norm_num) dec_trivial

-- Next we switch to trying to use `norm_num` to calculate each `s p i`.

open tactic

meta instance nat_pexpr : has_to_pexpr ℕ := ⟨pexpr.of_expr ∘ λ n, reflect n⟩
meta instance int_pexpr : has_to_pexpr ℤ := ⟨pexpr.of_expr ∘ λ n, reflect n⟩

lemma s_mod_succ {p a i b c}
  (h1 : (2^p - 1 : ℤ) = a)
  (h2 : s_mod p i = b)
  (h3 : (b * b - 2) % a = c) :
  s_mod p (i+1) = c :=
by { dsimp [s_mod, M], rw [h1, h2, pow_two, h3] }

meta def run_Lucas_Lehmer_test : tactic unit :=
do `(Lucas_Lehmer_test %%p) ← target,
   `[dsimp [Lucas_Lehmer_test]],
   `[rw residue_eq_zero_iff_s_mod_eq_zero, swap, norm_num],
   p ← eval_expr ℕ p,
   -- Calculate the candidate Mersenne prime
   M ← to_expr ``(2^%%p - 1 : ℤ) >>= eval_expr ℤ,
   t ← to_expr ``(2^%%p - 1 = %%M),
   v ← to_expr ``(by norm_num : 2^%%p - 1 = %%M),
   w ← assertv `w t v,
   -- Unfortunately this creates something like `w : 2^5 - 1 = int.of_nat 31`.
   -- We could make a better `has_to_pexpr ℤ` instance, or just:
   `[simp only [int.coe_nat_zero, int.coe_nat_succ, int.of_nat_eq_coe, zero_add, int.coe_nat_bit1] at w],
   -- base case
   t ← to_expr ``(s_mod %%p 0 = 4),
   v ← to_expr ``(rfl),
   h ← assertv `h t v,
   -- step case, repeated p-2 times
   iterate_exactly (p-2) `[replace h := s_mod_succ w h (by { norm_num, refl })],
   -- now close the goal
   h ← get_local `h,
   exact h

example : prime (M 5) := Lucas_Lehmer_sufficiency _ (by norm_num) (by run_Lucas_Lehmer_test).

-- Unfortunately this doesn't actually work yet, as we get:
-- deep recursion was detected at 'replace' (potential solution: increase stack space in your system)Lean
lemma Lucas_Lehmer_test_7 : Lucas_Lehmer_test 7 := by run_Lucas_Lehmer_test
-- example : prime (M 7) := Lucas_Lehmer_sufficiency _ (by norm_num) (by run_Lucas_Lehmer_test).

-- If we get that sorted out, there's still a much faster method of doing these calculations,
-- based on the formula
--   n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]
-- and the fact that `% 2^p` and `/ 2^p` are very efficient on the binary representation.
-- Someone should do this, too!

-- It's hard to know what the limiting factor for large Mersenne primes would be.
-- In the purely computational world, it's the squaring operation in `s`.

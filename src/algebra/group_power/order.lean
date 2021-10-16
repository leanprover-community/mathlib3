/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import algebra.order.ring
import algebra.group_power.basic

/-!
# Lemmas about the interaction of power operations with order

Note that some lemmas are in `algebra/group_power/lemmas.lean` as they import files which
depend on this file.
-/

variables {A G M R : Type*}

section preorder

variables [monoid M] [preorder M] [covariant_class M M (*) (≤)]

@[mono, to_additive nsmul_le_nsmul_of_le_right]
lemma pow_le_pow_of_le_left' [covariant_class M M (function.swap (*)) (≤)]
  {a b : M} (hab : a ≤ b) : ∀ i : ℕ, a ^ i ≤ b ^ i
| 0     := by simp
| (k+1) := by { rw [pow_succ, pow_succ],
    exact mul_le_mul' hab (pow_le_pow_of_le_left' k) }

@[to_additive nsmul_nonneg]
theorem one_le_pow_of_one_le' {a : M} (H : 1 ≤ a) : ∀ n : ℕ, 1 ≤ a ^ n
| 0       := by simp
| (k + 1) := by { rw pow_succ, exact one_le_mul H (one_le_pow_of_one_le' k) }

@[to_additive nsmul_nonpos]
theorem pow_le_one' {a : M} (H : a ≤ 1) (n : ℕ) : a ^ n ≤ 1 :=
@one_le_pow_of_one_le' (order_dual M) _ _ _ _ H n

@[to_additive nsmul_le_nsmul]
theorem pow_le_pow' {a : M} {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
let ⟨k, hk⟩ := nat.le.dest h in
calc a ^ n ≤ a ^ n * a ^ k : le_mul_of_one_le_right' (one_le_pow_of_one_le' ha _)
       ... = a ^ m         : by rw [← hk, pow_add]

@[to_additive nsmul_le_nsmul_of_nonpos]
theorem pow_le_pow_of_le_one' {a : M} {n m : ℕ} (ha : a ≤ 1) (h : n ≤ m) : a ^ m ≤ a ^ n :=
@pow_le_pow' (order_dual M) _ _ _ _ _ _  ha h

@[to_additive nsmul_pos]
theorem one_lt_pow' {a : M} (ha : 1 < a) {k : ℕ} (hk : k ≠ 0) : 1 < a ^ k :=
begin
  rcases nat.exists_eq_succ_of_ne_zero hk with ⟨l, rfl⟩,
  clear hk,
  induction l with l IH,
  { simpa using ha },
  { rw pow_succ,
    exact one_lt_mul' ha IH }
end

@[to_additive nsmul_neg]
theorem pow_lt_one' {a : M} (ha : a < 1) {k : ℕ} (hk : k ≠ 0) : a ^ k < 1 :=
@one_lt_pow' (order_dual M) _ _ _ _ ha k hk

@[to_additive nsmul_lt_nsmul]
theorem pow_lt_pow'' [covariant_class M M (*) (<)] {a : M} {n m : ℕ} (ha : 1 < a) (h : n < m) :
  a ^ n < a ^ m :=
begin
  rcases nat.le.dest h with ⟨k, rfl⟩, clear h,
  rw [pow_add, pow_succ', mul_assoc, ← pow_succ],
  exact lt_mul_of_one_lt_right' _ (one_lt_pow' ha k.succ_ne_zero)
end

end preorder

section linear_order

variables [monoid M] [linear_order M] [covariant_class M M (*) (≤)]

@[to_additive nsmul_nonneg_iff]
lemma one_le_pow_iff {x : M} {n : ℕ} (hn : n ≠ 0) : 1 ≤ x ^ n ↔ 1 ≤ x :=
⟨le_imp_le_of_lt_imp_lt $ λ h, pow_lt_one' h hn, λ h, one_le_pow_of_one_le' h n⟩

@[to_additive nsmul_nonpos_iff]
lemma pow_le_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n ≤ 1 ↔ x ≤ 1 :=
@one_le_pow_iff (order_dual M) _ _ _ _ _ hn

@[to_additive nsmul_pos_iff]
lemma one_lt_pow_iff {x : M} {n : ℕ} (hn : n ≠ 0) : 1 < x ^ n ↔ 1 < x :=
lt_iff_lt_of_le_iff_le (pow_le_one_iff hn)

@[to_additive nsmul_neg_iff]
lemma pow_lt_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n < 1 ↔ x < 1 :=
lt_iff_lt_of_le_iff_le (one_le_pow_iff hn)

@[to_additive nsmul_eq_zero_iff]
lemma pow_eq_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 :=
by simp only [le_antisymm_iff, pow_le_one_iff hn, one_le_pow_iff hn]

end linear_order

section group

variables [group G] [preorder G] [covariant_class G G (*) (≤)]

@[to_additive gsmul_nonneg]
theorem one_le_gpow {x : G} (H : 1 ≤ x) {n : ℤ} (hn : 0 ≤ n) :
  1 ≤ x ^ n :=
begin
  lift n to ℕ using hn,
  rw gpow_coe_nat,
  apply one_le_pow_of_one_le' H,
end

end group

namespace canonically_ordered_comm_semiring

variables [canonically_ordered_comm_semiring R]

theorem pow_pos {a : R} (H : 0 < a) (n : ℕ) : 0 < a ^ n :=
pos_iff_ne_zero.2 $ pow_ne_zero _ H.ne'

end canonically_ordered_comm_semiring

section ordered_semiring
variable [ordered_semiring R]

@[simp] theorem pow_pos {a : R} (H : 0 < a) : ∀ (n : ℕ), 0 < a ^ n
| 0     := by { nontriviality, rw pow_zero, exact zero_lt_one }
| (n+1) := by { rw pow_succ, exact mul_pos H (pow_pos _) }

@[simp] theorem pow_nonneg {a : R} (H : 0 ≤ a) : ∀ (n : ℕ), 0 ≤ a ^ n
| 0     := by { rw pow_zero, exact zero_le_one}
| (n+1) := by { rw pow_succ, exact mul_nonneg H (pow_nonneg _) }

theorem pow_add_pow_le {x y : R} {n : ℕ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hn : n ≠ 0) :
  x ^ n + y ^ n ≤ (x + y) ^ n :=
begin
  rcases nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩,
  induction k with k ih, { simp only [pow_one] },
  let n := k.succ,
  have h1 := add_nonneg (mul_nonneg hx (pow_nonneg hy n)) (mul_nonneg hy (pow_nonneg hx n)),
  have h2 := add_nonneg hx hy,
  calc x^n.succ + y^n.succ
    ≤ x*x^n + y*y^n + (x*y^n + y*x^n) :
      by { rw [pow_succ _ n, pow_succ _ n], exact le_add_of_nonneg_right h1 }
    ... = (x+y) * (x^n + y^n) :
      by rw [add_mul, mul_add, mul_add, add_comm (y*x^n), ← add_assoc,
        ← add_assoc, add_assoc (x*x^n) (x*y^n), add_comm (x*y^n) (y*y^n), ← add_assoc]
    ... ≤ (x+y)^n.succ :
      by { rw [pow_succ _ n], exact mul_le_mul_of_nonneg_left (ih (nat.succ_ne_zero k)) h2 }
end

theorem pow_lt_pow_of_lt_left {x y : R} {n : ℕ} (Hxy : x < y) (Hxpos : 0 ≤ x) (Hnpos : 0 < n) :
  x ^ n < y ^ n :=
begin
  cases lt_or_eq_of_le Hxpos,
  { rw ←nat.sub_add_cancel Hnpos,
    induction (n - 1), { simpa only [pow_one] },
    rw [pow_add, pow_add, nat.succ_eq_add_one, pow_one, pow_one],
    apply mul_lt_mul ih (le_of_lt Hxy) h (le_of_lt (pow_pos (lt_trans h Hxy) _)) },
  { rw [←h, zero_pow Hnpos], apply pow_pos (by rwa ←h at Hxy : 0 < y),}
end

lemma pow_lt_one {a : R} (h₀ : 0 ≤ a) (h₁ : a < 1) {n : ℕ} (hn : n ≠ 0) : a ^ n < 1 :=
(one_pow n).subst (pow_lt_pow_of_lt_left h₁ h₀ (nat.pos_of_ne_zero hn))

theorem strict_mono_on_pow {n : ℕ} (hn : 0 < n) :
  strict_mono_on (λ x : R, x ^ n) (set.Ici 0) :=
λ x hx y hy h, pow_lt_pow_of_lt_left h hx hn

theorem one_le_pow_of_one_le {a : R} (H : 1 ≤ a) : ∀ (n : ℕ), 1 ≤ a ^ n
| 0     := by rw [pow_zero]
| (n+1) := by { rw pow_succ, simpa only [mul_one] using mul_le_mul H (one_le_pow_of_one_le n)
    zero_le_one (le_trans zero_le_one H) }

lemma pow_mono {a : R} (h : 1 ≤ a) : monotone (λ n : ℕ, a ^ n) :=
monotone_nat_of_le_succ $ λ n,
  by { rw pow_succ, exact le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans h) _) h }

theorem pow_le_pow {a : R} {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
pow_mono ha h

lemma strict_mono_pow {a : R} (h : 1 < a) : strict_mono (λ n : ℕ, a ^ n) :=
have 0 < a := zero_le_one.trans_lt h,
strict_mono_nat_of_lt_succ $ λ n, by simpa only [one_mul, pow_succ]
  using mul_lt_mul h (le_refl (a ^ n)) (pow_pos this _) this.le

lemma pow_lt_pow {a : R} {n m : ℕ} (h : 1 < a) (h2 : n < m) : a ^ n < a ^ m :=
strict_mono_pow h h2

lemma pow_lt_pow_iff {a : R} {n m : ℕ} (h : 1 < a) : a ^ n < a ^ m ↔ n < m :=
(strict_mono_pow h).lt_iff_lt

@[mono] lemma pow_le_pow_of_le_left {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ i : ℕ, a^i ≤ b^i
| 0     := by simp
| (k+1) := by { rw [pow_succ, pow_succ],
    exact mul_le_mul hab (pow_le_pow_of_le_left _) (pow_nonneg ha _) (le_trans ha hab) }

lemma one_lt_pow {a : R} (ha : 1 < a) : ∀ {n : ℕ}, n ≠ 0 → 1 < a ^ n
| 0       h := (h rfl).elim
| 1       h := (pow_one a).symm.subst ha
| (n + 2) h :=
  begin
    nontriviality R,
    rw [←one_mul (1 : R), pow_succ],
    exact mul_lt_mul ha (one_lt_pow (nat.succ_ne_zero _)).le zero_lt_one (zero_lt_one.trans ha).le,
  end

lemma pow_le_one {a : R} : ∀ (n : ℕ) (h₀ : 0 ≤ a) (h₁ : a ≤ 1), a ^ n ≤ 1
| 0       h₀ h₁ := (pow_zero a).le
| (n + 1) h₀ h₁ := (pow_succ' a n).le.trans (mul_le_one (pow_le_one n h₀ h₁) h₀ h₁)

end ordered_semiring

section linear_ordered_semiring
variable [linear_ordered_semiring R]

lemma pow_le_one_iff_of_nonneg {a : R} (ha : 0 ≤ a) {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ 1 ↔ a ≤ 1 :=
begin
  refine ⟨_, pow_le_one n ha⟩,
  rw [←not_lt, ←not_lt],
  exact mt (λ h, one_lt_pow h hn),
end

lemma one_le_pow_iff_of_nonneg {a : R} (ha : 0 ≤ a) {n : ℕ} (hn : n ≠ 0) : 1 ≤ a ^ n ↔ 1 ≤ a :=
begin
  refine ⟨_, λ h, one_le_pow_of_one_le h n⟩,
  rw [←not_lt, ←not_lt],
  exact mt (λ h, pow_lt_one ha h hn),
end

lemma one_lt_pow_iff_of_nonneg {a : R} (ha : 0 ≤ a) {n : ℕ} (hn : n ≠ 0) : 1 < a ^ n ↔ 1 < a :=
lt_iff_lt_of_le_iff_le (pow_le_one_iff_of_nonneg ha hn)

lemma pow_lt_one_iff_of_nonneg {a : R} (ha : 0 ≤ a) {n : ℕ} (hn : n ≠ 0) : a ^ n < 1 ↔ a < 1 :=
lt_iff_lt_of_le_iff_le (one_le_pow_iff_of_nonneg ha hn)

lemma sq_le_one_iff {a : R} (ha : 0 ≤ a) : a^2 ≤ 1 ↔ a ≤ 1 :=
pow_le_one_iff_of_nonneg ha (nat.succ_ne_zero _)

lemma sq_lt_one_iff {a : R} (ha : 0 ≤ a) : a^2 < 1 ↔ a < 1 :=
pow_lt_one_iff_of_nonneg ha (nat.succ_ne_zero _)

lemma one_le_sq_iff {a : R} (ha : 0 ≤ a) : 1 ≤ a^2 ↔ 1 ≤ a :=
one_le_pow_iff_of_nonneg ha (nat.succ_ne_zero _)

lemma one_lt_sq_iff {a : R} (ha : 0 ≤ a) : 1 < a^2 ↔ 1 < a :=
one_lt_pow_iff_of_nonneg ha (nat.succ_ne_zero _)

@[simp] theorem pow_left_inj {x y : R} {n : ℕ} (Hxpos : 0 ≤ x) (Hypos : 0 ≤ y) (Hnpos : 0 < n) :
  x ^ n = y ^ n ↔ x = y :=
(@strict_mono_on_pow R _ _ Hnpos).inj_on.eq_iff Hxpos Hypos

lemma lt_of_pow_lt_pow {a b : R} (n : ℕ) (hb : 0 ≤ b) (h : a ^ n < b ^ n) : a < b :=
lt_of_not_ge $ λ hn, not_lt_of_ge (pow_le_pow_of_le_left hb hn _) h

lemma le_of_pow_le_pow {a b : R} (n : ℕ) (hb : 0 ≤ b) (hn : 0 < n) (h : a ^ n ≤ b ^ n) : a ≤ b :=
le_of_not_lt $ λ h1, not_le_of_lt (pow_lt_pow_of_lt_left h1 hb hn) h

@[simp] lemma sq_eq_sq {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 = b ^ 2 ↔ a = b :=
pow_left_inj ha hb dec_trivial

end linear_ordered_semiring

section linear_ordered_ring

variable [linear_ordered_ring R]

lemma pow_abs (a : R) (n : ℕ) : |a| ^ n = |a ^ n| :=
((abs_hom.to_monoid_hom : R →* R).map_pow a n).symm

lemma abs_neg_one_pow (n : ℕ) : |(-1 : R) ^ n| = 1 :=
by rw [←pow_abs, abs_neg, abs_one, one_pow]

theorem pow_bit0_nonneg (a : R) (n : ℕ) : 0 ≤ a ^ bit0 n :=
by { rw pow_bit0, exact mul_self_nonneg _ }

theorem sq_nonneg (a : R) : 0 ≤ a ^ 2 :=
pow_bit0_nonneg a 1

alias sq_nonneg ← pow_two_nonneg

theorem pow_bit0_pos {a : R} (h : a ≠ 0) (n : ℕ) : 0 < a ^ bit0 n :=
(pow_bit0_nonneg a n).lt_of_ne (pow_ne_zero _ h).symm

theorem sq_pos_of_ne_zero (a : R) (h : a ≠ 0) : 0 < a ^ 2 :=
pow_bit0_pos h 1

alias sq_pos_of_ne_zero ← pow_two_pos_of_ne_zero

variables {x y : R}

theorem sq_abs (x : R) : |x| ^ 2 = x ^ 2 :=
by simpa only [sq] using abs_mul_abs_self x

theorem abs_sq (x : R) : |x ^ 2| = x ^ 2 :=
by simpa only [sq] using abs_mul_self x

theorem sq_lt_sq (h : |x| < y) : x ^ 2 < y ^ 2 :=
by simpa only [sq_abs] using pow_lt_pow_of_lt_left h (abs_nonneg x) (1:ℕ).succ_pos

theorem sq_lt_sq' (h1 : -y < x) (h2 : x < y) : x ^ 2 < y ^ 2 :=
sq_lt_sq (abs_lt.mpr ⟨h1, h2⟩)

theorem sq_le_sq (h : |x| ≤ |y|) : x ^ 2 ≤ y ^ 2 :=
by simpa only [sq_abs] using pow_le_pow_of_le_left (abs_nonneg x) h 2

theorem sq_le_sq' (h1 : -y ≤ x) (h2 : x ≤ y) : x ^ 2 ≤ y ^ 2 :=
sq_le_sq (le_trans (abs_le.mpr ⟨h1, h2⟩) (le_abs_self _))

theorem abs_lt_abs_of_sq_lt_sq (h : x^2 < y^2) : |x| < |y| :=
lt_of_pow_lt_pow 2 (abs_nonneg y) $ by rwa [← sq_abs x, ← sq_abs y] at h

theorem abs_lt_of_sq_lt_sq (h : x^2 < y^2) (hy : 0 ≤ y) : |x| < y :=
begin
  rw [← abs_of_nonneg hy],
  exact abs_lt_abs_of_sq_lt_sq h,
end

theorem abs_lt_of_sq_lt_sq' (h : x^2 < y^2) (hy : 0 ≤ y) : -y < x ∧ x < y :=
abs_lt.mp $ abs_lt_of_sq_lt_sq h hy

theorem abs_le_abs_of_sq_le_sq (h : x^2 ≤ y^2) : |x| ≤ |y| :=
le_of_pow_le_pow 2 (abs_nonneg y) (1:ℕ).succ_pos $ by rwa [← sq_abs x, ← sq_abs y] at h

theorem abs_le_of_sq_le_sq (h : x^2 ≤ y^2) (hy : 0 ≤ y) : |x| ≤ y :=
begin
  rw [← abs_of_nonneg hy],
  exact abs_le_abs_of_sq_le_sq h,
end

theorem abs_le_of_sq_le_sq' (h : x^2 ≤ y^2) (hy : 0 ≤ y) : -y ≤ x ∧ x ≤ y :=
abs_le.mp $ abs_le_of_sq_le_sq h hy

end linear_ordered_ring

section linear_ordered_comm_ring
variables [linear_ordered_comm_ring R]

/-- Arithmetic mean-geometric mean (AM-GM) inequality for linearly ordered commutative rings. -/
lemma two_mul_le_add_sq (a b : R) : 2 * a * b ≤ a ^ 2 + b ^ 2 :=
sub_nonneg.mp ((sub_add_eq_add_sub _ _ _).subst ((sub_sq a b).subst (sq_nonneg _)))

alias two_mul_le_add_sq ← two_mul_le_add_pow_two

end linear_ordered_comm_ring

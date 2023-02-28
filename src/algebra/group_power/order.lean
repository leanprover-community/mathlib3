/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import algebra.order.ring.abs
import algebra.order.with_zero
import algebra.group_power.ring
import data.set.intervals.basic

/-!
# Lemmas about the interaction of power operations with order

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Note that some lemmas are in `algebra/group_power/lemmas.lean` as they import files which
depend on this file.
-/

open function

variables {β A G M R : Type*}

section monoid
variable [monoid M]

section preorder
variable [preorder M]

section left
variables [covariant_class M M (*) (≤)] {x : M}

@[to_additive nsmul_le_nsmul_of_le_right, mono]
lemma pow_le_pow_of_le_left' [covariant_class M M (swap (*)) (≤)] {a b : M} (hab : a ≤ b) :
  ∀ i : ℕ, a ^ i ≤ b ^ i
| 0     := by simp
| (k+1) := by { rw [pow_succ, pow_succ],
    exact mul_le_mul' hab (pow_le_pow_of_le_left' k) }

attribute [mono] nsmul_le_nsmul_of_le_right

@[to_additive nsmul_nonneg]
theorem one_le_pow_of_one_le' {a : M} (H : 1 ≤ a) : ∀ n : ℕ, 1 ≤ a ^ n
| 0       := by simp
| (k + 1) := by { rw pow_succ, exact one_le_mul H (one_le_pow_of_one_le' k) }

@[to_additive nsmul_nonpos]
lemma pow_le_one' {a : M} (H : a ≤ 1) (n : ℕ) : a ^ n ≤ 1 := @one_le_pow_of_one_le' Mᵒᵈ _ _ _ _ H n

@[to_additive nsmul_le_nsmul]
theorem pow_le_pow' {a : M} {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
let ⟨k, hk⟩ := nat.le.dest h in
calc a ^ n ≤ a ^ n * a ^ k : le_mul_of_one_le_right' (one_le_pow_of_one_le' ha _)
       ... = a ^ m         : by rw [← hk, pow_add]

@[to_additive nsmul_le_nsmul_of_nonpos]
theorem pow_le_pow_of_le_one' {a : M} {n m : ℕ} (ha : a ≤ 1) (h : n ≤ m) : a ^ m ≤ a ^ n :=
@pow_le_pow' Mᵒᵈ _ _ _ _ _ _  ha h

@[to_additive nsmul_pos]
theorem one_lt_pow' {a : M} (ha : 1 < a) {k : ℕ} (hk : k ≠ 0) : 1 < a ^ k :=
begin
  rcases nat.exists_eq_succ_of_ne_zero hk with ⟨l, rfl⟩,
  clear hk,
  induction l with l IH,
  { simpa using ha },
  { rw pow_succ,
    exact one_lt_mul'' ha IH }
end

@[to_additive nsmul_neg]
lemma pow_lt_one' {a : M} (ha : a < 1) {k : ℕ} (hk : k ≠ 0) : a ^ k < 1 :=
@one_lt_pow' Mᵒᵈ _ _ _ _ ha k hk

@[to_additive nsmul_lt_nsmul]
theorem pow_lt_pow' [covariant_class M M (*) (<)] {a : M} {n m : ℕ} (ha : 1 < a) (h : n < m) :
  a ^ n < a ^ m :=
begin
  rcases nat.le.dest h with ⟨k, rfl⟩, clear h,
  rw [pow_add, pow_succ', mul_assoc, ← pow_succ],
  exact lt_mul_of_one_lt_right' _ (one_lt_pow' ha k.succ_ne_zero)
end

@[to_additive nsmul_strict_mono_right]
lemma pow_strict_mono_left [covariant_class M M (*) (<)] {a : M} (ha : 1 < a) :
  strict_mono ((^) a : ℕ → M) :=
λ m n, pow_lt_pow' ha

@[to_additive left.pow_nonneg]
lemma left.one_le_pow_of_le (hx : 1 ≤ x) : ∀ {n : ℕ}, 1 ≤ x^n
| 0       := (pow_zero x).ge
| (n + 1) := by { rw pow_succ, exact left.one_le_mul hx left.one_le_pow_of_le }

@[to_additive left.pow_nonpos]
lemma left.pow_le_one_of_le (hx : x ≤ 1) : ∀ {n : ℕ}, x^n ≤ 1
| 0       := (pow_zero _).le
| (n + 1) := by { rw pow_succ, exact left.mul_le_one hx left.pow_le_one_of_le }

end left

section right
variables [covariant_class M M (swap (*)) (≤)] {x : M}

@[to_additive right.pow_nonneg]
lemma right.one_le_pow_of_le (hx : 1 ≤ x) : ∀ {n : ℕ}, 1 ≤ x^n
| 0       := (pow_zero _).ge
| (n + 1) := by { rw pow_succ, exact right.one_le_mul hx right.one_le_pow_of_le }

@[to_additive right.pow_nonpos]
lemma right.pow_le_one_of_le (hx : x ≤ 1) : ∀ {n : ℕ}, x^n ≤ 1
| 0       := (pow_zero _).le
| (n + 1) := by { rw pow_succ, exact right.mul_le_one hx right.pow_le_one_of_le }

end right

section covariant_lt_swap
variables [preorder β] [covariant_class M M (*) (<)] [covariant_class M M (swap (*)) (<)]
  {f : β → M}

@[to_additive strict_mono.nsmul_left]
lemma strict_mono.pow_right' (hf : strict_mono f) : ∀ {n : ℕ}, n ≠ 0 → strict_mono (λ a, f a ^ n)
| 0 hn := (hn rfl).elim
| 1 hn := by simpa
| (nat.succ $ nat.succ n) hn :=
  by { simp_rw pow_succ _ (n + 1), exact hf.mul' (strict_mono.pow_right' n.succ_ne_zero) }

/-- See also `pow_strict_mono_right` -/
@[nolint to_additive_doc, to_additive nsmul_strict_mono_left]
lemma pow_strict_mono_right' {n : ℕ} (hn : n ≠ 0) : strict_mono (λ a : M, a ^ n) :=
strict_mono_id.pow_right' hn

end covariant_lt_swap

section covariant_le_swap
variables [preorder β] [covariant_class M M (*) (≤)] [covariant_class M M (swap (*)) (≤)]

@[to_additive monotone.nsmul_left]
lemma monotone.pow_right {f : β → M} (hf : monotone f) : ∀ n : ℕ, monotone (λ a, f a ^ n)
| 0 := by simpa using monotone_const
| (n + 1) := by { simp_rw pow_succ, exact hf.mul' (monotone.pow_right _) }

@[to_additive nsmul_mono_left]
lemma pow_mono_right (n : ℕ) : monotone (λ a : M, a ^ n) := monotone_id.pow_right _

end covariant_le_swap

@[to_additive left.pow_neg]
lemma left.pow_lt_one_of_lt [covariant_class M M (*) (<)] {n : ℕ} {x : M} (hn : 0 < n) (h : x < 1) :
  x^n < 1 :=
nat.le_induction ((pow_one _).trans_lt h) (λ n _ ih, by { rw pow_succ, exact mul_lt_one h ih }) _
  (nat.succ_le_iff.2 hn)

@[to_additive right.pow_neg]
lemma right.pow_lt_one_of_lt [covariant_class M M (swap (*)) (<)] {n : ℕ} {x : M}
  (hn : 0 < n) (h : x < 1) :
  x^n < 1 :=
nat.le_induction ((pow_one _).trans_lt h)
  (λ n _ ih, by { rw pow_succ, exact right.mul_lt_one h ih }) _ (nat.succ_le_iff.2 hn)

end preorder

section linear_order
variables [linear_order M]

section covariant_le
variables [covariant_class M M (*) (≤)]

@[to_additive nsmul_nonneg_iff]
lemma one_le_pow_iff {x : M} {n : ℕ} (hn : n ≠ 0) : 1 ≤ x ^ n ↔ 1 ≤ x :=
⟨le_imp_le_of_lt_imp_lt $ λ h, pow_lt_one' h hn, λ h, one_le_pow_of_one_le' h n⟩

@[to_additive]
lemma pow_le_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n ≤ 1 ↔ x ≤ 1 :=
@one_le_pow_iff Mᵒᵈ _ _ _ _ _ hn

@[to_additive nsmul_pos_iff]
lemma one_lt_pow_iff {x : M} {n : ℕ} (hn : n ≠ 0) : 1 < x ^ n ↔ 1 < x :=
lt_iff_lt_of_le_iff_le (pow_le_one_iff hn)

@[to_additive]
lemma pow_lt_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n < 1 ↔ x < 1 :=
lt_iff_lt_of_le_iff_le (one_le_pow_iff hn)

@[to_additive]
lemma pow_eq_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 :=
by simp only [le_antisymm_iff, pow_le_one_iff hn, one_le_pow_iff hn]

variables [covariant_class M M (*) (<)] {a : M} {m n : ℕ}

@[to_additive nsmul_le_nsmul_iff]
lemma pow_le_pow_iff' (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n := (pow_strict_mono_left ha).le_iff_le

@[to_additive nsmul_lt_nsmul_iff]
lemma pow_lt_pow_iff' (ha : 1 < a) : a ^ m < a ^ n ↔ m < n := (pow_strict_mono_left ha).lt_iff_lt

end covariant_le

section covariant_le_swap
variables [covariant_class M M (*) (≤)] [covariant_class M M (swap (*)) (≤)]

@[to_additive lt_of_nsmul_lt_nsmul]
lemma lt_of_pow_lt_pow'  {a b : M} (n : ℕ) : a ^ n < b ^ n → a < b := (pow_mono_right _).reflect_lt

@[to_additive]
lemma min_lt_max_of_mul_lt_mul {a b c d : M} (h : a * b < c * d) : min a b < max c d :=
lt_of_pow_lt_pow' 2 $ by { simp_rw pow_two, exact (mul_le_mul' inf_le_left
  inf_le_right).trans_lt (h.trans_le $ mul_le_mul' le_sup_left le_sup_right) }

@[to_additive min_lt_of_add_lt_two_nsmul]
lemma min_lt_of_mul_lt_sq {a b c : M} (h : a * b < c ^ 2) : min a b < c :=
by simpa using min_lt_max_of_mul_lt_mul (h.trans_eq $ pow_two _)

@[to_additive lt_max_of_two_nsmul_lt_add]
lemma lt_max_of_sq_lt_mul {a b c : M} (h : a ^ 2 < b * c) : a < max b c :=
by simpa using min_lt_max_of_mul_lt_mul ((pow_two _).symm.trans_lt h)

end covariant_le_swap

section covariant_lt_swap
variables [covariant_class M M (*) (<)] [covariant_class M M (swap (*)) (<)]

@[to_additive le_of_nsmul_le_nsmul]
lemma le_of_pow_le_pow' {a b : M} {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ b ^ n → a ≤ b :=
(pow_strict_mono_right' hn).le_iff_le.1

@[to_additive min_le_of_add_le_two_nsmul]
lemma min_le_of_mul_le_sq {a b c : M} (h : a * b ≤ c ^ 2) : min a b ≤ c :=
by simpa using min_le_max_of_mul_le_mul (h.trans_eq $ pow_two _)

@[to_additive le_max_of_two_nsmul_le_add]
lemma le_max_of_sq_le_mul {a b c : M} (h : a ^ 2 ≤ b * c) : a ≤ max b c :=
by simpa using min_le_max_of_mul_le_mul ((pow_two _).symm.trans_le h)

end covariant_lt_swap

@[to_additive left.nsmul_neg_iff]
lemma left.pow_lt_one_iff [covariant_class M M (*) (<)] {n : ℕ} {x : M} (hn : 0 < n) :
  x^n < 1 ↔ x < 1 :=
by { haveI := has_mul.to_covariant_class_left M, exact pow_lt_one_iff hn.ne' }

@[to_additive right.nsmul_neg_iff]
lemma right.pow_lt_one_iff [covariant_class M M (swap (*)) (<)] {n : ℕ} {x : M} (hn : 0 < n) :
  x^n < 1 ↔ x < 1 :=
⟨λ H, not_le.mp $ λ k, H.not_le $ by { haveI := has_mul.to_covariant_class_right M,
    exact right.one_le_pow_of_le k }, right.pow_lt_one_of_lt hn⟩

end linear_order
end monoid

section div_inv_monoid

variables [div_inv_monoid G] [preorder G] [covariant_class G G (*) (≤)]

@[to_additive zsmul_nonneg]
theorem one_le_zpow {x : G} (H : 1 ≤ x) {n : ℤ} (hn : 0 ≤ n) :
  1 ≤ x ^ n :=
begin
  lift n to ℕ using hn,
  rw zpow_coe_nat,
  apply one_le_pow_of_one_le' H,
end

end div_inv_monoid

namespace canonically_ordered_comm_semiring

variables [canonically_ordered_comm_semiring R]

theorem pow_pos {a : R} (H : 0 < a) (n : ℕ) : 0 < a ^ n :=
pos_iff_ne_zero.2 $ pow_ne_zero _ H.ne'

end canonically_ordered_comm_semiring

section ordered_semiring
variables [ordered_semiring R] {a x y : R} {n m : ℕ}

lemma zero_pow_le_one : ∀ n : ℕ, (0 : R) ^ n ≤ 1
| 0 := (pow_zero _).le
| (n + 1) := by { rw [zero_pow n.succ_pos], exact zero_le_one }

theorem pow_add_pow_le (hx : 0 ≤ x) (hy : 0 ≤ y) (hn : n ≠ 0) : x ^ n + y ^ n ≤ (x + y) ^ n :=
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

lemma pow_le_one : ∀ (n : ℕ) (h₀ : 0 ≤ a) (h₁ : a ≤ 1), a ^ n ≤ 1
| 0       h₀ h₁ := (pow_zero a).le
| (n + 1) h₀ h₁ := (pow_succ' a n).le.trans (mul_le_one (pow_le_one n h₀ h₁) h₀ h₁)

lemma pow_lt_one (h₀ : 0 ≤ a) (h₁ : a < 1) : ∀ {n : ℕ} (hn : n ≠ 0), a ^ n < 1
| 0 h := (h rfl).elim
| (n + 1) h :=
  by { rw pow_succ, exact mul_lt_one_of_nonneg_of_lt_one_left h₀ h₁ (pow_le_one _ h₀ h₁.le) }

theorem one_le_pow_of_one_le (H : 1 ≤ a) : ∀ (n : ℕ), 1 ≤ a ^ n
| 0     := by rw [pow_zero]
| (n+1) := by { rw pow_succ, simpa only [mul_one] using mul_le_mul H (one_le_pow_of_one_le n)
    zero_le_one (le_trans zero_le_one H) }

lemma pow_mono (h : 1 ≤ a) : monotone (λ n : ℕ, a ^ n) :=
monotone_nat_of_le_succ $ λ n,
  by { rw pow_succ, exact le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans h) _) h }

theorem pow_le_pow (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
pow_mono ha h

theorem le_self_pow (ha : 1 ≤ a) (h : m ≠ 0) : a ≤ a ^ m :=
(pow_one a).symm.trans_le (pow_le_pow ha $ pos_iff_ne_zero.mpr h)

@[mono] lemma pow_le_pow_of_le_left {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ i : ℕ, a^i ≤ b^i
| 0     := by simp
| (k+1) := by { rw [pow_succ, pow_succ],
    exact mul_le_mul hab (pow_le_pow_of_le_left _) (pow_nonneg ha _) (le_trans ha hab) }

lemma one_lt_pow (ha : 1 < a) : ∀ {n : ℕ} (hn : n ≠ 0), 1 < a ^ n
| 0 h := (h rfl).elim
| (n + 1) h :=
  by { rw pow_succ, exact one_lt_mul_of_lt_of_le ha (one_le_pow_of_one_le ha.le _) }

end ordered_semiring

section strict_ordered_semiring
variables [strict_ordered_semiring R] {a x y : R} {n m : ℕ}

lemma pow_lt_pow_of_lt_left (h : x < y) (hx : 0 ≤ x) : ∀ {n : ℕ}, 0 < n → x ^ n < y ^ n
| 0 hn := hn.false.elim
| (n + 1) _ := by simpa only [pow_succ'] using
    mul_lt_mul_of_le_of_le' (pow_le_pow_of_le_left hx h.le _) h (pow_pos (hx.trans_lt h) _) hx

lemma strict_mono_on_pow (hn : 0 < n) : strict_mono_on (λ x : R, x ^ n) (set.Ici 0) :=
λ x hx y hy h, pow_lt_pow_of_lt_left h hx hn

lemma pow_strict_mono_right (h : 1 < a) : strict_mono (λ n : ℕ, a ^ n) :=
have 0 < a := zero_le_one.trans_lt h,
strict_mono_nat_of_lt_succ $ λ n, by simpa only [one_mul, pow_succ]
  using mul_lt_mul h (le_refl (a ^ n)) (pow_pos this _) this.le

lemma pow_lt_pow (h : 1 < a) (h2 : n < m) : a ^ n < a ^ m :=
pow_strict_mono_right h h2

lemma pow_lt_pow_iff (h : 1 < a) : a ^ n < a ^ m ↔ n < m :=
(pow_strict_mono_right h).lt_iff_lt

lemma pow_le_pow_iff (h : 1 < a) : a ^ n ≤ a ^ m ↔ n ≤ m :=
(pow_strict_mono_right h).le_iff_le

lemma strict_anti_pow (h₀ : 0 < a) (h₁ : a < 1) : strict_anti (λ n : ℕ, a ^ n) :=
strict_anti_nat_of_succ_lt $ λ n,
  by simpa only [pow_succ, one_mul] using mul_lt_mul h₁ le_rfl (pow_pos h₀ n) zero_le_one

lemma pow_lt_pow_iff_of_lt_one (h₀ : 0 < a) (h₁ : a < 1) : a ^ m < a ^ n ↔ n < m :=
(strict_anti_pow h₀ h₁).lt_iff_lt

lemma pow_lt_pow_of_lt_one (h : 0 < a) (ha : a < 1) {i j : ℕ} (hij : i < j) : a ^ j < a ^ i :=
(pow_lt_pow_iff_of_lt_one h ha).2 hij

lemma pow_lt_self_of_lt_one (h₀ : 0 < a) (h₁ : a < 1) (hn : 1 < n) : a ^ n < a :=
calc a ^ n < a ^ 1 : pow_lt_pow_of_lt_one h₀ h₁ hn
... = a : pow_one _

lemma sq_pos_of_pos (ha : 0 < a) : 0 < a ^ 2 := by { rw sq, exact mul_pos ha ha }

end strict_ordered_semiring

section strict_ordered_ring
variables [strict_ordered_ring R] {a : R}

lemma pow_bit0_pos_of_neg (ha : a < 0) (n : ℕ) : 0 < a ^ bit0 n :=
begin
  rw pow_bit0',
  exact pow_pos (mul_pos_of_neg_of_neg ha ha) _,
end

lemma pow_bit1_neg (ha : a < 0) (n : ℕ) : a ^ bit1 n < 0 :=
begin
  rw [bit1, pow_succ],
  exact mul_neg_of_neg_of_pos ha (pow_bit0_pos_of_neg ha n),
end

lemma sq_pos_of_neg (ha : a < 0) : 0 < a ^ 2 := pow_bit0_pos_of_neg ha _

end strict_ordered_ring

section linear_ordered_semiring
variables [linear_ordered_semiring R] {a b : R}

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
(@strict_mono_on_pow R _ _ Hnpos).eq_iff_eq Hxpos Hypos

lemma lt_of_pow_lt_pow {a b : R} (n : ℕ) (hb : 0 ≤ b) (h : a ^ n < b ^ n) : a < b :=
lt_of_not_ge $ λ hn, not_lt_of_ge (pow_le_pow_of_le_left hb hn _) h

lemma le_of_pow_le_pow {a b : R} (n : ℕ) (hb : 0 ≤ b) (hn : 0 < n) (h : a ^ n ≤ b ^ n) : a ≤ b :=
le_of_not_lt $ λ h1, not_le_of_lt (pow_lt_pow_of_lt_left h1 hb hn) h

@[simp] lemma sq_eq_sq {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 = b ^ 2 ↔ a = b :=
pow_left_inj ha hb dec_trivial

lemma lt_of_mul_self_lt_mul_self (hb : 0 ≤ b) : a * a < b * b → a < b :=
by { simp_rw ←sq, exact lt_of_pow_lt_pow _ hb }

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

theorem pow_bit0_pos_iff (a : R) {n : ℕ} (hn : n ≠ 0) : 0 < a ^ bit0 n ↔ a ≠ 0 :=
begin
  refine ⟨λ h, _, λ h, pow_bit0_pos h n⟩,
  rintro rfl,
  rw zero_pow (nat.zero_lt_bit0 hn) at h,
  exact lt_irrefl _ h,
end

theorem sq_pos_iff (a : R) : 0 < a ^ 2 ↔ a ≠ 0 :=
pow_bit0_pos_iff a one_ne_zero

variables {x y : R}

theorem sq_abs (x : R) : |x| ^ 2 = x ^ 2 :=
by simpa only [sq] using abs_mul_abs_self x

theorem abs_sq (x : R) : |x ^ 2| = x ^ 2 :=
by simpa only [sq] using abs_mul_self x

theorem sq_lt_sq : x ^ 2 < y ^ 2 ↔ |x| < |y| :=
by simpa only [sq_abs]
  using (@strict_mono_on_pow R _ _ two_pos).lt_iff_lt (abs_nonneg x) (abs_nonneg y)

theorem sq_lt_sq' (h1 : -y < x) (h2 : x < y) : x ^ 2 < y ^ 2 :=
sq_lt_sq.2 (lt_of_lt_of_le (abs_lt.2 ⟨h1, h2⟩) (le_abs_self _))

theorem sq_le_sq : x ^ 2 ≤ y ^ 2 ↔ |x| ≤ |y| :=
by simpa only [sq_abs]
  using (@strict_mono_on_pow R _ _ two_pos).le_iff_le (abs_nonneg x) (abs_nonneg y)

theorem sq_le_sq' (h1 : -y ≤ x) (h2 : x ≤ y) : x ^ 2 ≤ y ^ 2 :=
sq_le_sq.2 (le_trans (abs_le.mpr ⟨h1, h2⟩) (le_abs_self _))

theorem abs_lt_of_sq_lt_sq (h : x^2 < y^2) (hy : 0 ≤ y) : |x| < y :=
by rwa [← abs_of_nonneg hy, ← sq_lt_sq]

theorem abs_lt_of_sq_lt_sq' (h : x^2 < y^2) (hy : 0 ≤ y) : -y < x ∧ x < y :=
abs_lt.mp $ abs_lt_of_sq_lt_sq h hy

theorem abs_le_of_sq_le_sq (h : x^2 ≤ y^2) (hy : 0 ≤ y) : |x| ≤ y :=
by rwa [← abs_of_nonneg hy, ← sq_le_sq]

theorem abs_le_of_sq_le_sq' (h : x^2 ≤ y^2) (hy : 0 ≤ y) : -y ≤ x ∧ x ≤ y :=
abs_le.mp $ abs_le_of_sq_le_sq h hy

lemma sq_eq_sq_iff_abs_eq_abs (x y : R) : x^2 = y^2 ↔ |x| = |y| :=
by simp only [le_antisymm_iff, sq_le_sq]

@[simp] lemma sq_le_one_iff_abs_le_one (x : R) : x^2 ≤ 1 ↔ |x| ≤ 1 :=
by simpa only [one_pow, abs_one] using @sq_le_sq _ _ x 1

@[simp] lemma sq_lt_one_iff_abs_lt_one (x : R) : x^2 < 1 ↔ |x| < 1 :=
by simpa only [one_pow, abs_one] using @sq_lt_sq _ _ x 1

@[simp] lemma one_le_sq_iff_one_le_abs (x : R) : 1 ≤ x^2 ↔ 1 ≤ |x| :=
by simpa only [one_pow, abs_one] using @sq_le_sq _ _ 1 x

@[simp] lemma one_lt_sq_iff_one_lt_abs (x : R) : 1 < x^2 ↔ 1 < |x| :=
by simpa only [one_pow, abs_one] using @sq_lt_sq _ _ 1 x

lemma pow_four_le_pow_two_of_pow_two_le {x y : R} (h : x^2 ≤ y) : x^4 ≤ y^2 :=
(pow_mul x 2 2).symm ▸ pow_le_pow_of_le_left (sq_nonneg x) h 2

end linear_ordered_ring

section linear_ordered_comm_ring
variables [linear_ordered_comm_ring R]

/-- Arithmetic mean-geometric mean (AM-GM) inequality for linearly ordered commutative rings. -/
lemma two_mul_le_add_sq (a b : R) : 2 * a * b ≤ a ^ 2 + b ^ 2 :=
sub_nonneg.mp ((sub_add_eq_add_sub _ _ _).subst ((sub_sq a b).subst (sq_nonneg _)))

alias two_mul_le_add_sq ← two_mul_le_add_pow_two

end linear_ordered_comm_ring

section linear_ordered_comm_monoid_with_zero
variables [linear_ordered_comm_monoid_with_zero M] [no_zero_divisors M] {a : M} {n : ℕ}

lemma pow_pos_iff (hn : 0 < n) : 0 < a ^ n ↔ 0 < a := by simp_rw [zero_lt_iff, pow_ne_zero_iff hn]

end linear_ordered_comm_monoid_with_zero

section linear_ordered_comm_group_with_zero
variables [linear_ordered_comm_group_with_zero M] {a : M} {m n : ℕ}

lemma pow_lt_pow_succ (ha : 1 < a) : a ^ n < a ^ n.succ :=
by { rw [←one_mul (a ^ n), pow_succ],
  exact mul_lt_right₀ _ ha (pow_ne_zero _ (zero_lt_one.trans ha).ne') }

lemma pow_lt_pow₀ (ha : 1 < a) (hmn : m < n) : a ^ m < a ^ n :=
by { induction hmn with n hmn ih, exacts [pow_lt_pow_succ ha, lt_trans ih (pow_lt_pow_succ ha)] }

end linear_ordered_comm_group_with_zero

namespace monoid_hom
variables [ring R] [monoid M] [linear_order M] [covariant_class M M (*) (≤)] (f : R →* M)

lemma map_neg_one : f (-1) = 1 :=
(pow_eq_one_iff (nat.succ_ne_zero 1)).1 $ by rw [←map_pow, neg_one_sq, map_one]

@[simp] lemma map_neg (x : R) : f (-x) = f x :=
by rw [←neg_one_mul, map_mul, map_neg_one, one_mul]

lemma map_sub_swap (x y : R) : f (x - y) = f (y - x) := by rw [←map_neg, neg_sub]

end monoid_hom

/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.rat.order
/-!
# Casts for Rational Numbers

## Summary

1. We define the canonical injection from ℚ into an arbitrary division ring and prove various
casting lemmas showing the well-behavedness of this injection.
2. We prove basic properties about the casts from ℤ and ℕ into ℚ (i.e. `(n : ℚ) = n / 1`) .

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, cast, coercion, casting
-/

namespace rat
variable {α : Type*}
local infix ` /. `:70 := rat.mk

section with_div_ring
variable [division_ring α]

/-- Construct the canonical injection from `ℚ` into an arbitrary
  division ring. If the field has positive characteristic `p`,
  we define `1 / p = 1 / 0 = 0` for consistency with our
  division by zero convention. -/
protected def cast : ℚ → α
| ⟨n, d, h, c⟩ := n / d

@[priority 0] instance cast_coe : has_coe ℚ α := ⟨rat.cast⟩

theorem coe_int_eq_mk : ∀ (z : ℤ), ↑z = z /. 1
| (n : ℕ) := show (n:ℚ) = n /. 1,
  by induction n with n IH n; simp [*, show (1:ℚ) = 1 /. 1, from rfl]
| -[1+ n] := show (-(n + 1) : ℚ) = -[1+ n] /. 1, begin
  induction n with n IH, {refl},
  show -(n + 1 + 1 : ℚ) = -[1+ n.succ] /. 1,
  rw [neg_add, IH],
  simpa [show -1 = (-1) /. 1, from rfl]
end

theorem mk_eq_div (n d : ℤ) : n /. d = ((n : ℚ) / d) :=
begin
  by_cases d0 : d = 0, {simp [d0, div_zero]},
  simp [division_def, coe_int_eq_mk, mul_def one_ne_zero d0]
end

theorem coe_int_eq_of_int (z : ℤ) : ↑z = of_int z :=
(coe_int_eq_mk z).trans (of_int_eq_mk z).symm

@[simp] theorem cast_of_int (n : ℤ) : (of_int n : α) = n :=
show (n / (1:ℕ) : α) = n, by rw [nat.cast_one, div_one]

@[simp, squash_cast] theorem cast_coe_int (n : ℤ) : ((n : ℚ) : α) = n :=
by rw [coe_int_eq_of_int, cast_of_int]

@[simp, elim_cast] theorem coe_int_num (n : ℤ) : (n : ℚ).num = n :=
by rw coe_int_eq_of_int; refl

@[simp, elim_cast] theorem coe_int_denom (n : ℤ) : (n : ℚ).denom = 1 :=
by rw coe_int_eq_of_int; refl

theorem coe_nat_eq_mk (n : ℕ) : ↑n = n /. 1 :=
by rw [← int.cast_coe_nat, coe_int_eq_mk]

@[simp, elim_cast] theorem coe_nat_num (n : ℕ) : (n : ℚ).num = n :=
by rw [← int.cast_coe_nat, coe_int_num]

@[simp, elim_cast] theorem coe_nat_denom (n : ℕ) : (n : ℚ).denom = 1 :=
by rw [← int.cast_coe_nat, coe_int_denom]

@[simp, squash_cast] theorem cast_coe_nat (n : ℕ) : ((n : ℚ) : α) = n := cast_coe_int n

@[simp, squash_cast] theorem cast_zero : ((0 : ℚ) : α) = 0 :=
(cast_of_int _).trans int.cast_zero

@[simp, squash_cast] theorem cast_one : ((1 : ℚ) : α) = 1 :=
(cast_of_int _).trans int.cast_one

theorem mul_cast_comm (a : α) :
  ∀ (n : ℚ), (n.denom : α) ≠ 0 → a * n = n * a
| ⟨n, d, h, c⟩ h₂ := show a * (n * d⁻¹) = n * d⁻¹ * a,
  by rw [← mul_assoc, int.mul_cast_comm, mul_assoc, mul_assoc,
         ← show (d:α)⁻¹ * a = a * d⁻¹, from
           division_ring.inv_comm_of_comm h₂ (int.mul_cast_comm a d).symm]

@[move_cast] theorem cast_mk_of_ne_zero (a b : ℤ)
  (b0 : (b:α) ≠ 0) : (a /. b : α) = a / b :=
begin
  have b0' : b ≠ 0, { refine mt _ b0, simp {contextual := tt} },
  cases e : a /. b with n d h c,
  have d0 : (d:α) ≠ 0,
  { intro d0,
    have dd := denom_dvd a b,
    cases (show (d:ℤ) ∣ b, by rwa e at dd) with k ke,
    have : (b:α) = (d:α) * (k:α), {rw [ke, int.cast_mul], refl},
    rw [d0, zero_mul] at this, contradiction },
  rw [num_denom'] at e,
  have := congr_arg (coe : ℤ → α) ((mk_eq b0' $ ne_of_gt $ int.coe_nat_pos.2 h).1 e),
  rw [int.cast_mul, int.cast_mul, int.cast_coe_nat] at this,
  symmetry, change (a * b⁻¹ : α) = n / d,
  rw [eq_div_iff_mul_eq _ _ d0, mul_assoc, nat.mul_cast_comm,
      ← mul_assoc, this, mul_assoc, mul_inv_cancel b0, mul_one]
end

@[move_cast] theorem cast_add_of_ne_zero : ∀ {m n : ℚ},
  (m.denom : α) ≠ 0 → (n.denom : α) ≠ 0 → ((m + n : ℚ) : α) = m + n
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := λ (d₁0 : (d₁:α) ≠ 0) (d₂0 : (d₂:α) ≠ 0), begin
  have d₁0' : (d₁:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d₁0; exact d₁0 rfl),
  have d₂0' : (d₂:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d₂0; exact d₂0 rfl),
  rw [num_denom', num_denom', add_def d₁0' d₂0'],
  suffices : (n₁ * (d₂ * (d₂⁻¹ * d₁⁻¹)) +
    n₂ * (d₁ * d₂⁻¹) * d₁⁻¹ : α) = n₁ * d₁⁻¹ + n₂ * d₂⁻¹,
  { rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero],
    { simpa [division_def, left_distrib, right_distrib, mul_inv_eq,
             d₁0, d₂0, division_ring.mul_ne_zero d₁0 d₂0, mul_assoc] },
    all_goals {simp [d₁0, d₂0, division_ring.mul_ne_zero d₁0 d₂0]} },
  rw [← mul_assoc (d₂:α), mul_inv_cancel d₂0, one_mul,
      ← nat.mul_cast_comm], simp [d₁0, mul_assoc]
end

@[simp, move_cast] theorem cast_neg : ∀ n, ((-n : ℚ) : α) = -n
| ⟨n, d, h, c⟩ := show (↑-n * d⁻¹ : α) = -(n * d⁻¹),
  by rw [int.cast_neg, neg_mul_eq_neg_mul]

@[move_cast] theorem cast_sub_of_ne_zero {m n : ℚ}
  (m0 : (m.denom : α) ≠ 0) (n0 : (n.denom : α) ≠ 0) : ((m - n : ℚ) : α) = m - n :=
have ((-n).denom : α) ≠ 0, by cases n; exact n0,
by simp [(cast_add_of_ne_zero m0 this)]

@[move_cast] theorem cast_mul_of_ne_zero : ∀ {m n : ℚ},
  (m.denom : α) ≠ 0 → (n.denom : α) ≠ 0 → ((m * n : ℚ) : α) = m * n
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := λ (d₁0 : (d₁:α) ≠ 0) (d₂0 : (d₂:α) ≠ 0), begin
  have d₁0' : (d₁:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d₁0; exact d₁0 rfl),
  have d₂0' : (d₂:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d₂0; exact d₂0 rfl),
  rw [num_denom', num_denom', mul_def d₁0' d₂0'],
  suffices : (n₁ * ((n₂ * d₂⁻¹) * d₁⁻¹) : α) = n₁ * (d₁⁻¹ * (n₂ * d₂⁻¹)),
  { rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero],
    { simpa [division_def, mul_inv_eq, d₁0, d₂0, division_ring.mul_ne_zero d₁0 d₂0, mul_assoc] },
    all_goals {simp [d₁0, d₂0, division_ring.mul_ne_zero d₁0 d₂0]} },
  rw [division_ring.inv_comm_of_comm d₁0 (nat.mul_cast_comm _ _).symm]
end

@[move_cast] theorem cast_inv_of_ne_zero : ∀ {n : ℚ},
  (n.num : α) ≠ 0 → (n.denom : α) ≠ 0 → ((n⁻¹ : ℚ) : α) = n⁻¹
| ⟨n, d, h, c⟩ := λ (n0 : (n:α) ≠ 0) (d0 : (d:α) ≠ 0), begin
  have n0' : (n:ℤ) ≠ 0 := λ e, by rw e at n0; exact n0 rfl,
  have d0' : (d:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d0; exact d0 rfl),
  rw [num_denom', inv_def],
  rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, inv_div];
  simp [n0, d0]
end

@[move_cast] theorem cast_div_of_ne_zero {m n : ℚ} (md : (m.denom : α) ≠ 0)
  (nn : (n.num : α) ≠ 0) (nd : (n.denom : α) ≠ 0) : ((m / n : ℚ) : α) = m / n :=
have (n⁻¹.denom : ℤ) ∣ n.num,
by conv in n⁻¹.denom { rw [num_denom n, inv_def] };
   apply denom_dvd,
have (n⁻¹.denom : α) = 0 → (n.num : α) = 0, from
λ h, let ⟨k, e⟩ := this in
  by have := congr_arg (coe : ℤ → α) e;
     rwa [int.cast_mul, int.cast_coe_nat, h, zero_mul] at this,
by rw [division_def, cast_mul_of_ne_zero md (mt this nn), cast_inv_of_ne_zero nn nd, division_def]

@[simp, elim_cast] theorem cast_inj [char_zero α] : ∀ {m n : ℚ}, (m : α) = n ↔ m = n
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := begin
  refine ⟨λ h, _, congr_arg _⟩,
  have d₁0 : d₁ ≠ 0 := ne_of_gt h₁,
  have d₂0 : d₂ ≠ 0 := ne_of_gt h₂,
  have d₁a : (d₁:α) ≠ 0 := nat.cast_ne_zero.2 d₁0,
  have d₂a : (d₂:α) ≠ 0 := nat.cast_ne_zero.2 d₂0,
  rw [num_denom', num_denom'] at h ⊢,
  rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero] at h; simp [d₁0, d₂0] at h ⊢,
  rwa [eq_div_iff_mul_eq _ _ d₂a, division_def, mul_assoc,
    division_ring.inv_comm_of_comm d₁a (nat.mul_cast_comm _ _),
    ← mul_assoc, ← division_def, eq_comm, eq_div_iff_mul_eq _ _ d₁a, eq_comm,
    ← int.cast_coe_nat, ← int.cast_mul, ← int.cast_coe_nat, ← int.cast_mul,
    int.cast_inj, ← mk_eq (int.coe_nat_ne_zero.2 d₁0) (int.coe_nat_ne_zero.2 d₂0)] at h
end

theorem cast_injective [char_zero α] : function.injective (coe : ℚ → α)
| m n := cast_inj.1

@[simp] theorem cast_eq_zero [char_zero α] {n : ℚ} : (n : α) = 0 ↔ n = 0 :=
by rw [← cast_zero, cast_inj]

@[simp] theorem cast_ne_zero [char_zero α] {n : ℚ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
not_congr cast_eq_zero

theorem eq_cast_of_ne_zero (f : ℚ → α) (H1 : f 1 = 1)
  (Hadd : ∀ x y, f (x + y) = f x + f y)
  (Hmul : ∀ x y, f (x * y) = f x * f y) :
  ∀ n : ℚ, (n.denom : α) ≠ 0 → f n = n
| ⟨n, d, h, c⟩ := λ (h₂ : ((d:ℤ):α) ≠ 0), show _ = (n / (d:ℤ) : α), begin
  rw [num_denom', mk_eq_div, eq_div_iff_mul_eq _ _ h₂],
  have : ∀ n : ℤ, f n = n, { apply int.eq_cast; simp [H1, Hadd] },
  rw [← this, ← this, ← Hmul, div_mul_cancel],
  exact int.cast_ne_zero.2 (int.coe_nat_ne_zero.2 $ ne_of_gt h),
end

theorem eq_cast [char_zero α] (f : ℚ → α) (H1 : f 1 = 1)
  (Hadd : ∀ x y, f (x + y) = f x + f y)
  (Hmul : ∀ x y, f (x * y) = f x * f y) (n : ℚ) : f n = n :=
eq_cast_of_ne_zero _ H1 Hadd Hmul _ $
  nat.cast_ne_zero.2 $ ne_of_gt n.pos

end with_div_ring

@[move_cast] theorem cast_mk [discrete_field α] [char_zero α] (a b : ℤ) : ((a /. b) : α) = a / b :=
if b0 : b = 0 then by simp [b0, div_zero]
else cast_mk_of_ne_zero a b (int.cast_ne_zero.2 b0)

@[simp, move_cast] theorem cast_add [division_ring α] [char_zero α] (m n) :
  ((m + n : ℚ) : α) = m + n :=
cast_add_of_ne_zero (nat.cast_ne_zero.2 $ ne_of_gt m.pos) (nat.cast_ne_zero.2 $ ne_of_gt n.pos)

@[simp, move_cast] theorem cast_sub [division_ring α] [char_zero α] (m n) :
  ((m - n : ℚ) : α) = m - n :=
cast_sub_of_ne_zero (nat.cast_ne_zero.2 $ ne_of_gt m.pos) (nat.cast_ne_zero.2 $ ne_of_gt n.pos)

@[simp, move_cast] theorem cast_mul [division_ring α] [char_zero α] (m n) :
  ((m * n : ℚ) : α) = m * n :=
cast_mul_of_ne_zero (nat.cast_ne_zero.2 $ ne_of_gt m.pos) (nat.cast_ne_zero.2 $ ne_of_gt n.pos)

@[simp, move_cast] theorem cast_inv [discrete_field α] [char_zero α] (n) : ((n⁻¹ : ℚ) : α) = n⁻¹ :=
if n0 : n.num = 0 then
  by simp [show n = 0, by rw [num_denom n, n0]; simp, inv_zero] else
cast_inv_of_ne_zero (int.cast_ne_zero.2 n0) (nat.cast_ne_zero.2 $ ne_of_gt n.pos)

@[simp, move_cast] theorem cast_div [discrete_field α] [char_zero α] (m n) :
  ((m / n : ℚ) : α) = m / n :=
by rw [division_def, cast_mul, cast_inv, division_def]

@[simp, move_cast] theorem cast_pow [discrete_field α] [char_zero α] (q) (k : ℕ) :
  ((q ^ k : ℚ) : α) = q ^ k :=
by induction k; simp only [*, cast_one, cast_mul, pow_zero, pow_succ]

@[simp, squash_cast, move_cast] theorem cast_bit0 [division_ring α] [char_zero α] (n : ℚ) :
  ((bit0 n : ℚ) : α) = bit0 n :=
cast_add _ _

@[simp, squash_cast, move_cast] theorem cast_bit1 [division_ring α] [char_zero α] (n : ℚ) :
  ((bit1 n : ℚ) : α) = bit1 n :=
by rw [bit1, cast_add, cast_one, cast_bit0]; refl

@[simp] theorem cast_nonneg [linear_ordered_field α] : ∀ {n : ℚ}, 0 ≤ (n : α) ↔ 0 ≤ n
| ⟨n, d, h, c⟩ := show 0 ≤ (n * d⁻¹ : α) ↔ 0 ≤ (⟨n, d, h, c⟩ : ℚ),
  by rw [num_denom', ← nonneg_iff_zero_le, mk_nonneg _ (int.coe_nat_pos.2 h),
    mul_nonneg_iff_right_nonneg_of_pos (@inv_pos α _ _ (nat.cast_pos.2 h)),
    int.cast_nonneg]

@[simp, elim_cast] theorem cast_le [linear_ordered_field α] {m n : ℚ} : (m : α) ≤ n ↔ m ≤ n :=
by rw [← sub_nonneg, ← cast_sub, cast_nonneg, sub_nonneg]

@[simp, elim_cast] theorem cast_lt [linear_ordered_field α] {m n : ℚ} : (m : α) < n ↔ m < n :=
by simpa [-cast_le] using not_congr (@cast_le α _ n m)

@[simp] theorem cast_nonpos [linear_ordered_field α] {n : ℚ} : (n : α) ≤ 0 ↔ n ≤ 0 :=
by rw [← cast_zero, cast_le]

@[simp] theorem cast_pos [linear_ordered_field α] {n : ℚ} : (0 : α) < n ↔ 0 < n :=
by rw [← cast_zero, cast_lt]

@[simp] theorem cast_lt_zero [linear_ordered_field α] {n : ℚ} : (n : α) < 0 ↔ n < 0 :=
by rw [← cast_zero, cast_lt]

@[simp, squash_cast] theorem cast_id : ∀ n : ℚ, ↑n = n
| ⟨n, d, h, c⟩ := show (n / (d : ℤ) : ℚ) = _, by rw [num_denom', mk_eq_div]

@[simp, move_cast] theorem cast_min [discrete_linear_ordered_field α] {a b : ℚ} :
  (↑(min a b) : α) = min a b :=
by by_cases a ≤ b; simp [h, min]

@[simp, move_cast] theorem cast_max [discrete_linear_ordered_field α] {a b : ℚ} :
  (↑(max a b) : α) = max a b :=
by by_cases a ≤ b; simp [h, max]

@[simp, move_cast] theorem cast_abs [discrete_linear_ordered_field α] {q : ℚ} :
  ((abs q : ℚ) : α) = abs q :=
by simp [abs]

end rat

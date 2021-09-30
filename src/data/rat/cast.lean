/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.rat.order
import data.int.char_zero

/-!
# Casts for Rational Numbers

## Summary

We define the canonical injection from ℚ into an arbitrary division ring and prove various
casting lemmas showing the well-behavedness of this injection.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, cast, coercion, casting
-/

namespace rat
variable {α : Type*}
open_locale rat

section with_div_ring
variable [division_ring α]

/-- Construct the canonical injection from `ℚ` into an arbitrary
  division ring. If the field has positive characteristic `p`,
  we define `1 / p = 1 / 0 = 0` for consistency with our
  division by zero convention. -/
-- see Note [coercion into rings]
@[priority 900] instance cast_coe : has_coe_t ℚ α := ⟨λ r, r.1 / r.2⟩

@[simp] theorem cast_of_int (n : ℤ) : (of_int n : α) = n :=
show (n / (1:ℕ) : α) = n, by rw [nat.cast_one, div_one]

@[simp, norm_cast] theorem cast_coe_int (n : ℤ) : ((n : ℚ) : α) = n :=
by rw [coe_int_eq_of_int, cast_of_int]

@[simp, norm_cast] theorem cast_coe_nat (n : ℕ) : ((n : ℚ) : α) = n := cast_coe_int n

@[simp, norm_cast] theorem cast_zero : ((0 : ℚ) : α) = 0 :=
(cast_of_int _).trans int.cast_zero

@[simp, norm_cast] theorem cast_one : ((1 : ℚ) : α) = 1 :=
(cast_of_int _).trans int.cast_one

theorem cast_commute (r : ℚ) (a : α) : commute ↑r a :=
(r.1.cast_commute a).div_left (r.2.cast_commute a)

theorem cast_comm (r : ℚ) (a : α) : (r : α) * a = a * r :=
(cast_commute r a).eq

theorem commute_cast (a : α) (r : ℚ) : commute a r :=
(r.cast_commute a).symm

@[norm_cast] theorem cast_mk_of_ne_zero (a b : ℤ)
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
  symmetry, change (a / b : α) = n / d,
  rw [div_eq_mul_inv, eq_div_iff_mul_eq d0, mul_assoc, (d.commute_cast _).eq,
      ← mul_assoc, this, mul_assoc, mul_inv_cancel b0, mul_one]
end

@[norm_cast] theorem cast_add_of_ne_zero : ∀ {m n : ℚ},
  (m.denom : α) ≠ 0 → (n.denom : α) ≠ 0 → ((m + n : ℚ) : α) = m + n
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := λ (d₁0 : (d₁:α) ≠ 0) (d₂0 : (d₂:α) ≠ 0), begin
  have d₁0' : (d₁:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d₁0; exact d₁0 rfl),
  have d₂0' : (d₂:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d₂0; exact d₂0 rfl),
  rw [num_denom', num_denom', add_def d₁0' d₂0'],
  suffices : (n₁ * (d₂ * (d₂⁻¹ * d₁⁻¹)) +
    n₂ * (d₁ * d₂⁻¹) * d₁⁻¹ : α) = n₁ * d₁⁻¹ + n₂ * d₂⁻¹,
  { rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero],
    { simpa [division_def, left_distrib, right_distrib, mul_inv_rev', d₁0, d₂0, mul_assoc] },
    all_goals {simp [d₁0, d₂0]} },
  rw [← mul_assoc (d₂:α), mul_inv_cancel d₂0, one_mul,
      (nat.cast_commute _ _).eq], simp [d₁0, mul_assoc]
end

@[simp, norm_cast] theorem cast_neg : ∀ n, ((-n : ℚ) : α) = -n
| ⟨n, d, h, c⟩ := show (↑-n / d : α) = -(n / d),
  by rw [div_eq_mul_inv, div_eq_mul_inv, int.cast_neg, neg_mul_eq_neg_mul]

@[norm_cast] theorem cast_sub_of_ne_zero {m n : ℚ}
  (m0 : (m.denom : α) ≠ 0) (n0 : (n.denom : α) ≠ 0) : ((m - n : ℚ) : α) = m - n :=
have ((-n).denom : α) ≠ 0, by cases n; exact n0,
by simp [sub_eq_add_neg, (cast_add_of_ne_zero m0 this)]

@[norm_cast] theorem cast_mul_of_ne_zero : ∀ {m n : ℚ},
  (m.denom : α) ≠ 0 → (n.denom : α) ≠ 0 → ((m * n : ℚ) : α) = m * n
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := λ (d₁0 : (d₁:α) ≠ 0) (d₂0 : (d₂:α) ≠ 0), begin
  have d₁0' : (d₁:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d₁0; exact d₁0 rfl),
  have d₂0' : (d₂:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d₂0; exact d₂0 rfl),
  rw [num_denom', num_denom', mul_def d₁0' d₂0'],
  suffices : (n₁ * ((n₂ * d₂⁻¹) * d₁⁻¹) : α) = n₁ * (d₁⁻¹ * (n₂ * d₂⁻¹)),
  { rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero],
    { simpa [division_def, mul_inv_rev', d₁0, d₂0, mul_assoc] },
    all_goals {simp [d₁0, d₂0]} },
  rw [(d₁.commute_cast (_:α)).inv_right'.eq]
end

@[norm_cast] theorem cast_inv_of_ne_zero : ∀ {n : ℚ},
  (n.num : α) ≠ 0 → (n.denom : α) ≠ 0 → ((n⁻¹ : ℚ) : α) = n⁻¹
| ⟨n, d, h, c⟩ := λ (n0 : (n:α) ≠ 0) (d0 : (d:α) ≠ 0), begin
  have n0' : (n:ℤ) ≠ 0 := λ e, by rw e at n0; exact n0 rfl,
  have d0' : (d:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d0; exact d0 rfl),
  rw [num_denom', inv_def],
  rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, inv_div];
  simp [n0, d0]
end

@[norm_cast] theorem cast_div_of_ne_zero {m n : ℚ} (md : (m.denom : α) ≠ 0)
  (nn : (n.num : α) ≠ 0) (nd : (n.denom : α) ≠ 0) : ((m / n : ℚ) : α) = m / n :=
have (n⁻¹.denom : ℤ) ∣ n.num,
by conv in n⁻¹.denom { rw [←(@num_denom n), inv_def] };
   apply denom_dvd,
have (n⁻¹.denom : α) = 0 → (n.num : α) = 0, from
λ h, let ⟨k, e⟩ := this in
  by have := congr_arg (coe : ℤ → α) e;
     rwa [int.cast_mul, int.cast_coe_nat, h, zero_mul] at this,
by rw [division_def, cast_mul_of_ne_zero md (mt this nn), cast_inv_of_ne_zero nn nd, division_def]

@[simp, norm_cast] theorem cast_inj [char_zero α] : ∀ {m n : ℚ}, (m : α) = n ↔ m = n
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := begin
  refine ⟨λ h, _, congr_arg _⟩,
  have d₁0 : d₁ ≠ 0 := ne_of_gt h₁,
  have d₂0 : d₂ ≠ 0 := ne_of_gt h₂,
  have d₁a : (d₁:α) ≠ 0 := nat.cast_ne_zero.2 d₁0,
  have d₂a : (d₂:α) ≠ 0 := nat.cast_ne_zero.2 d₂0,
  rw [num_denom', num_denom'] at h ⊢,
  rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero] at h; simp [d₁0, d₂0] at h ⊢,
  rwa [eq_div_iff_mul_eq d₂a, division_def, mul_assoc, (d₁.cast_commute (d₂:α)).inv_left'.eq,
    ← mul_assoc, ← division_def, eq_comm, eq_div_iff_mul_eq d₁a, eq_comm,
    ← int.cast_coe_nat, ← int.cast_mul, ← int.cast_coe_nat, ← int.cast_mul,
    int.cast_inj, ← mk_eq (int.coe_nat_ne_zero.2 d₁0) (int.coe_nat_ne_zero.2 d₂0)] at h
end

theorem cast_injective [char_zero α] : function.injective (coe : ℚ → α)
| m n := cast_inj.1

@[simp] theorem cast_eq_zero [char_zero α] {n : ℚ} : (n : α) = 0 ↔ n = 0 :=
by rw [← cast_zero, cast_inj]

theorem cast_ne_zero [char_zero α] {n : ℚ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
not_congr cast_eq_zero

@[simp, norm_cast] theorem cast_add [char_zero α] (m n) :
  ((m + n : ℚ) : α) = m + n :=
cast_add_of_ne_zero (nat.cast_ne_zero.2 $ ne_of_gt m.pos) (nat.cast_ne_zero.2 $ ne_of_gt n.pos)

@[simp, norm_cast] theorem cast_sub [char_zero α] (m n) :
  ((m - n : ℚ) : α) = m - n :=
cast_sub_of_ne_zero (nat.cast_ne_zero.2 $ ne_of_gt m.pos) (nat.cast_ne_zero.2 $ ne_of_gt n.pos)

@[simp, norm_cast] theorem cast_mul [char_zero α] (m n) :
  ((m * n : ℚ) : α) = m * n :=
cast_mul_of_ne_zero (nat.cast_ne_zero.2 $ ne_of_gt m.pos) (nat.cast_ne_zero.2 $ ne_of_gt n.pos)

@[simp, norm_cast] theorem cast_bit0 [char_zero α] (n : ℚ) :
  ((bit0 n : ℚ) : α) = bit0 n :=
cast_add _ _

@[simp, norm_cast] theorem cast_bit1 [char_zero α] (n : ℚ) :
  ((bit1 n : ℚ) : α) = bit1 n :=
by rw [bit1, cast_add, cast_one, cast_bit0]; refl

variable (α)

/-- Coercion `ℚ → α` as a `ring_hom`. -/
def cast_hom [char_zero α] : ℚ →+* α := ⟨coe, cast_one, cast_mul, cast_zero, cast_add⟩

variable {α}

@[simp] lemma coe_cast_hom [char_zero α] : ⇑(cast_hom α) = coe := rfl

@[simp, norm_cast] theorem cast_inv [char_zero α] (n) : ((n⁻¹ : ℚ) : α) = n⁻¹ :=
(cast_hom α).map_inv _

@[simp, norm_cast] theorem cast_div [char_zero α] (m n) :
  ((m / n : ℚ) : α) = m / n :=
(cast_hom α).map_div _ _

@[norm_cast] theorem cast_mk [char_zero α] (a b : ℤ) : ((a /. b) : α) = a / b :=
by simp only [mk_eq_div, cast_div, cast_coe_int]

@[simp, norm_cast] theorem cast_pow [char_zero α] (q) (k : ℕ) :
  ((q ^ k : ℚ) : α) = q ^ k :=
(cast_hom α).map_pow q k

end with_div_ring

@[simp, norm_cast] theorem cast_nonneg [linear_ordered_field α] : ∀ {n : ℚ}, 0 ≤ (n : α) ↔ 0 ≤ n
| ⟨n, d, h, c⟩ :=
  by { rw [num_denom', cast_mk, mk_eq_div, div_nonneg_iff, div_nonneg_iff], norm_cast }

@[simp, norm_cast] theorem cast_le [linear_ordered_field α] {m n : ℚ} : (m : α) ≤ n ↔ m ≤ n :=
by rw [← sub_nonneg, ← cast_sub, cast_nonneg, sub_nonneg]

@[simp, norm_cast] theorem cast_lt [linear_ordered_field α] {m n : ℚ} : (m : α) < n ↔ m < n :=
by simpa [-cast_le] using not_congr (@cast_le α _ n m)

@[simp] theorem cast_nonpos [linear_ordered_field α] {n : ℚ} : (n : α) ≤ 0 ↔ n ≤ 0 :=
by rw [← cast_zero, cast_le]

@[simp] theorem cast_pos [linear_ordered_field α] {n : ℚ} : (0 : α) < n ↔ 0 < n :=
by rw [← cast_zero, cast_lt]

@[simp] theorem cast_lt_zero [linear_ordered_field α] {n : ℚ} : (n : α) < 0 ↔ n < 0 :=
by rw [← cast_zero, cast_lt]

@[simp, norm_cast] theorem cast_id : ∀ n : ℚ, ↑n = n
| ⟨n, d, h, c⟩ := by rw [num_denom', cast_mk, mk_eq_div]

@[simp, norm_cast] theorem cast_min [linear_ordered_field α] {a b : ℚ} :
  (↑(min a b) : α) = min a b :=
by by_cases a ≤ b; simp [h, min_def]

@[simp, norm_cast] theorem cast_max [linear_ordered_field α] {a b : ℚ} :
  (↑(max a b) : α) = max a b :=
by by_cases b ≤ a; simp [h, max_def]

@[simp, norm_cast] theorem cast_abs [linear_ordered_field α] {q : ℚ} :
  ((abs q : ℚ) : α) = abs q :=
by simp [abs_eq_max_neg]

end rat

open rat ring_hom

lemma ring_hom.eq_rat_cast {k} [division_ring k] (f : ℚ →+* k) (r : ℚ) : f r = r :=
calc f r = f (r.1 / r.2) : by rw [← int.cast_coe_nat, ← mk_eq_div, num_denom]
     ... = f r.1 / f r.2 : f.map_div _ _
     ... = r.1 / r.2     : by rw [map_nat_cast, map_int_cast]

-- This seems to be true for a `[char_p k]` too because `k'` must have the same characteristic
-- but the proof would be much longer
lemma ring_hom.map_rat_cast {k k'} [division_ring k] [char_zero k] [division_ring k']
  (f : k →+* k') (r : ℚ) :
  f r = r :=
(f.comp (cast_hom k)).eq_rat_cast r

lemma ring_hom.ext_rat {R : Type*} [semiring R] (f g : ℚ →+* R) : f = g :=
begin
  ext r,
  refine rat.num_denom_cases_on' r _,
  intros a b b0,
  let φ : ℤ →+* R := f.comp (int.cast_ring_hom ℚ),
  let ψ : ℤ →+* R := g.comp (int.cast_ring_hom ℚ),
  rw [rat.mk_eq_div, int.cast_coe_nat],
  have b0' : (b:ℚ) ≠ 0 := nat.cast_ne_zero.2 b0,
  have : ∀ n : ℤ, f n = g n := λ n, show φ n = ψ n, by rw [φ.ext_int ψ],
  calc f (a * b⁻¹)
      = f a * f b⁻¹ * (g (b:ℤ) * g b⁻¹) :
        by rw [int.cast_coe_nat, ← g.map_mul, mul_inv_cancel b0', g.map_one, mul_one, f.map_mul]
  ... = g a * f b⁻¹ * (f (b:ℤ) * g b⁻¹) : by rw [this a, ← this b]
  ... = g (a * b⁻¹) :
        by rw [int.cast_coe_nat, mul_assoc, ← mul_assoc (f b⁻¹),
              ← f.map_mul, inv_mul_cancel b0', f.map_one, one_mul, g.map_mul]
end

instance rat.subsingleton_ring_hom {R : Type*} [semiring R] : subsingleton (ℚ →+* R) :=
⟨ring_hom.ext_rat⟩

namespace monoid_with_zero_hom

variables {M : Type*} [group_with_zero M]

/-- If `f` and `g` agree on the integers then they are equal `φ`.

See note [partially-applied ext lemmas] for why `comp` is used here. -/
@[ext]
theorem ext_rat {f g : monoid_with_zero_hom ℚ M}
  (same_on_int : f.comp (int.cast_ring_hom ℚ).to_monoid_with_zero_hom =
    g.comp (int.cast_ring_hom ℚ).to_monoid_with_zero_hom) : f = g :=
begin
  have same_on_int' : ∀ k : ℤ, f k = g k := congr_fun same_on_int,
  ext x,
  rw [← @rat.num_denom x, rat.mk_eq_div, f.map_div, g.map_div,
    same_on_int' x.num, same_on_int' x.denom],
end

/-- Positive integer values of a morphism `φ` and its value on `-1` completely determine `φ`. -/
theorem ext_rat_on_pnat {f g : monoid_with_zero_hom ℚ M}
  (same_on_neg_one : f (-1) = g (-1)) (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
ext_rat $ ext_int' (by simpa) ‹_›

end monoid_with_zero_hom

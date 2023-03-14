/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.rat.order
import data.rat.lemmas
import data.int.char_zero
import algebra.group_with_zero.power
import algebra.field.opposite
import algebra.order.field.basic

/-!
# Casts for Rational Numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We define the canonical injection from ℚ into an arbitrary division ring and prove various
casting lemmas showing the well-behavedness of this injection.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, cast, coercion, casting
-/

variables {F ι α β : Type*}

namespace rat
open_locale rat

section with_div_ring
variable [division_ring α]

@[simp, norm_cast] theorem cast_coe_int (n : ℤ) : ((n : ℚ) : α) = n :=
(cast_def _).trans $ show (n / (1:ℕ) : α) = n, by rw [nat.cast_one, div_one]

@[simp, norm_cast] theorem cast_coe_nat (n : ℕ) : ((n : ℚ) : α) = n :=
by rw [← int.cast_coe_nat, cast_coe_int, int.cast_coe_nat]

@[simp, norm_cast] lemma cast_zero : ((0 : ℚ) : α) = 0 := (cast_coe_int _).trans int.cast_zero
@[simp, norm_cast] lemma cast_one : ((1 : ℚ) : α) = 1 := (cast_coe_int _).trans int.cast_one

theorem cast_commute (r : ℚ) (a : α) : commute ↑r a :=
by simpa only [cast_def] using (r.1.cast_commute a).div_left (r.2.cast_commute a)

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
    have : (b:α) = (d:α) * (k:α), {rw [ke, int.cast_mul, int.cast_coe_nat]},
    rw [d0, zero_mul] at this, contradiction },
  rw [num_denom'] at e,
  have := congr_arg (coe : ℤ → α) ((mk_eq b0' $ ne_of_gt $ int.coe_nat_pos.2 h).1 e),
  rw [int.cast_mul, int.cast_mul, int.cast_coe_nat] at this,
  symmetry,
  rw [cast_def, div_eq_mul_inv, eq_div_iff_mul_eq d0, mul_assoc, (d.commute_cast _).eq,
      ← mul_assoc, this, mul_assoc, mul_inv_cancel b0, mul_one]
end

@[norm_cast] theorem cast_add_of_ne_zero : ∀ {m n : ℚ},
  (m.denom : α) ≠ 0 → (n.denom : α) ≠ 0 → ((m + n : ℚ) : α) = m + n
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := λ (d₁0 : (d₁:α) ≠ 0) (d₂0 : (d₂:α) ≠ 0), begin
  have d₁0' : (d₁:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d₁0; exact d₁0 nat.cast_zero),
  have d₂0' : (d₂:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d₂0; exact d₂0 nat.cast_zero),
  rw [num_denom', num_denom', add_def d₁0' d₂0'],
  suffices : (n₁ * (d₂ * (d₂⁻¹ * d₁⁻¹)) +
    n₂ * (d₁ * d₂⁻¹) * d₁⁻¹ : α) = n₁ * d₁⁻¹ + n₂ * d₂⁻¹,
  { rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero],
    { simpa [division_def, left_distrib, right_distrib, mul_inv_rev, d₁0, d₂0, mul_assoc] },
    all_goals {simp [d₁0, d₂0]} },
  rw [← mul_assoc (d₂:α), mul_inv_cancel d₂0, one_mul,
      (nat.cast_commute _ _).eq], simp [d₁0, mul_assoc]
end

@[simp, norm_cast] theorem cast_neg : ∀ n, ((-n : ℚ) : α) = -n
| ⟨n, d, h, c⟩ := by simpa only [cast_def] using show (↑-n / d : α) = -(n / d),
  by rw [div_eq_mul_inv, div_eq_mul_inv, int.cast_neg, neg_mul_eq_neg_mul]

@[norm_cast] theorem cast_sub_of_ne_zero {m n : ℚ}
  (m0 : (m.denom : α) ≠ 0) (n0 : (n.denom : α) ≠ 0) : ((m - n : ℚ) : α) = m - n :=
have ((-n).denom : α) ≠ 0, by cases n; exact n0,
by simp [sub_eq_add_neg, (cast_add_of_ne_zero m0 this)]

@[norm_cast] theorem cast_mul_of_ne_zero : ∀ {m n : ℚ},
  (m.denom : α) ≠ 0 → (n.denom : α) ≠ 0 → ((m * n : ℚ) : α) = m * n
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := λ (d₁0 : (d₁:α) ≠ 0) (d₂0 : (d₂:α) ≠ 0), begin
  have d₁0' : (d₁:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d₁0; exact d₁0 nat.cast_zero),
  have d₂0' : (d₂:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d₂0; exact d₂0 nat.cast_zero),
  rw [num_denom', num_denom', mul_def d₁0' d₂0'],
  suffices : (n₁ * ((n₂ * d₂⁻¹) * d₁⁻¹) : α) = n₁ * (d₁⁻¹ * (n₂ * d₂⁻¹)),
  { rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero],
    { simpa [division_def, mul_inv_rev, d₁0, d₂0, mul_assoc] },
    all_goals {simp [d₁0, d₂0]} },
  rw [(d₁.commute_cast (_:α)).inv_right₀.eq]
end

@[simp] theorem cast_inv_nat (n : ℕ) : ((n⁻¹ : ℚ) : α) = n⁻¹ :=
begin
  cases n, { simp },
  simp_rw [coe_nat_eq_mk, inv_def, mk, mk_nat, dif_neg n.succ_ne_zero, mk_pnat],
  simp [cast_def]
end

@[simp] theorem cast_inv_int (n : ℤ) : ((n⁻¹ : ℚ) : α) = n⁻¹ :=
begin
  cases n,
  { simp [cast_inv_nat] },
  { simp only [int.cast_neg_succ_of_nat, ← nat.cast_succ, cast_neg, inv_neg, cast_inv_nat] }
end

@[norm_cast] theorem cast_inv_of_ne_zero : ∀ {n : ℚ},
  (n.num : α) ≠ 0 → (n.denom : α) ≠ 0 → ((n⁻¹ : ℚ) : α) = n⁻¹
| ⟨n, d, h, c⟩ := λ (n0 : (n:α) ≠ 0) (d0 : (d:α) ≠ 0), begin
  have n0' : (n:ℤ) ≠ 0 := λ e, by rw e at n0; exact n0 int.cast_zero,
  have d0' : (d:ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ e, by rw e at d0; exact d0 nat.cast_zero),
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
  rwa [eq_div_iff_mul_eq d₂a, division_def, mul_assoc, (d₁.cast_commute (d₂:α)).inv_left₀.eq,
    ← mul_assoc, ← division_def, eq_comm, eq_div_iff_mul_eq d₁a, eq_comm,
    ← int.cast_coe_nat d₁, ← int.cast_mul, ← int.cast_coe_nat d₂, ← int.cast_mul,
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

variables (α) [char_zero α]

/-- Coercion `ℚ → α` as a `ring_hom`. -/
def cast_hom : ℚ →+* α := ⟨coe, cast_one, cast_mul, cast_zero, cast_add⟩

variable {α}

@[simp] lemma coe_cast_hom : ⇑(cast_hom α) = coe := rfl

@[simp, norm_cast] theorem cast_inv (n) : ((n⁻¹ : ℚ) : α) = n⁻¹ := map_inv₀ (cast_hom α) _
@[simp, norm_cast] theorem cast_div (m n) : ((m / n : ℚ) : α) = m / n := map_div₀ (cast_hom α) _ _
@[simp, norm_cast] theorem cast_zpow (q : ℚ) (n : ℤ) : ((q ^ n : ℚ) : α) = q ^ n :=
map_zpow₀ (cast_hom α) q n

@[norm_cast] theorem cast_mk (a b : ℤ) : ((a /. b) : α) = a / b :=
by simp only [mk_eq_div, cast_div, cast_coe_int]

@[simp, norm_cast] theorem cast_pow (q) (k : ℕ) : ((q ^ k : ℚ) : α) = q ^ k :=
(cast_hom α).map_pow q k

end with_div_ring

section linear_ordered_field

variables {K : Type*} [linear_ordered_field K]

lemma cast_pos_of_pos {r : ℚ} (hr : 0 < r) : (0 : K) < r :=
begin
  rw [rat.cast_def],
  exact div_pos (int.cast_pos.2 $ num_pos_iff_pos.2 hr) (nat.cast_pos.2 r.pos)
end

@[mono] lemma cast_strict_mono : strict_mono (coe : ℚ → K) :=
λ m n, by simpa only [sub_pos, cast_sub] using @cast_pos_of_pos K _ (n - m)

@[mono] lemma cast_mono : monotone (coe : ℚ → K) := cast_strict_mono.monotone

/-- Coercion from `ℚ` as an order embedding. -/
@[simps] def cast_order_embedding : ℚ ↪o K := order_embedding.of_strict_mono coe cast_strict_mono

@[simp, norm_cast] theorem cast_le {m n : ℚ} : (m : K) ≤ n ↔ m ≤ n := cast_order_embedding.le_iff_le
@[simp, norm_cast] theorem cast_lt {m n : ℚ} : (m : K) < n ↔ m < n := cast_strict_mono.lt_iff_lt

@[simp] theorem cast_nonneg {n : ℚ} : 0 ≤ (n : K) ↔ 0 ≤ n := by norm_cast
@[simp] theorem cast_nonpos {n : ℚ} : (n : K) ≤ 0 ↔ n ≤ 0 := by norm_cast
@[simp] theorem cast_pos {n : ℚ} : (0 : K) < n ↔ 0 < n := by norm_cast
@[simp] theorem cast_lt_zero {n : ℚ} : (n : K) < 0 ↔ n < 0 := by norm_cast

@[simp, norm_cast] theorem cast_min {a b : ℚ} : (↑(min a b) : K) = min a b :=
(@cast_mono K _).map_min

@[simp, norm_cast] theorem cast_max {a b : ℚ} : (↑(max a b) : K) = max a b :=
(@cast_mono K _).map_max

@[simp, norm_cast] theorem cast_abs {q : ℚ} : ((|q| : ℚ) : K) = |q| := by simp [abs_eq_max_neg]

open set

@[simp] lemma preimage_cast_Icc (a b : ℚ) : coe ⁻¹' (Icc (a : K) b) = Icc a b := by { ext x, simp }
@[simp] lemma preimage_cast_Ico (a b : ℚ) : coe ⁻¹' (Ico (a : K) b) = Ico a b := by { ext x, simp }
@[simp] lemma preimage_cast_Ioc (a b : ℚ) : coe ⁻¹' (Ioc (a : K) b) = Ioc a b := by { ext x, simp }
@[simp] lemma preimage_cast_Ioo (a b : ℚ) : coe ⁻¹' (Ioo (a : K) b) = Ioo a b := by { ext x, simp }
@[simp] lemma preimage_cast_Ici (a : ℚ) : coe ⁻¹' (Ici (a : K)) = Ici a := by { ext x, simp }
@[simp] lemma preimage_cast_Iic (a : ℚ) : coe ⁻¹' (Iic (a : K)) = Iic a := by { ext x, simp }
@[simp] lemma preimage_cast_Ioi (a : ℚ) : coe ⁻¹' (Ioi (a : K)) = Ioi a := by { ext x, simp }
@[simp] lemma preimage_cast_Iio (a : ℚ) : coe ⁻¹' (Iio (a : K)) = Iio a := by { ext x, simp }

end linear_ordered_field

@[norm_cast] theorem cast_id (n : ℚ) : (↑n : ℚ) = n := by rw [cast_def, num_div_denom]
@[simp] theorem cast_eq_id : (coe : ℚ → ℚ) = id := funext cast_id
@[simp] lemma cast_hom_rat : cast_hom ℚ = ring_hom.id ℚ := ring_hom.ext cast_id

end rat

open rat

@[simp] lemma map_rat_cast [division_ring α] [division_ring β] [ring_hom_class F α β]
  (f : F) (q : ℚ) : f q = q :=
by rw [cast_def, map_div₀, map_int_cast, map_nat_cast, cast_def]

@[simp] lemma eq_rat_cast {k} [division_ring k] [ring_hom_class F ℚ k] (f : F) (r : ℚ) : f r = r :=
by rw [← map_rat_cast f, rat.cast_id]

namespace monoid_with_zero_hom

variables {M₀ : Type*} [monoid_with_zero M₀] [monoid_with_zero_hom_class F ℚ M₀] {f g : F}
include M₀

/-- If `f` and `g` agree on the integers then they are equal `φ`. -/
theorem ext_rat' (h : ∀ m : ℤ, f m = g m) : f = g :=
fun_like.ext f g $ λ r, by rw [← r.num_div_denom, div_eq_mul_inv, map_mul, map_mul, h,
  ← int.cast_coe_nat, eq_on_inv₀ f g (h _)]

/-- If `f` and `g` agree on the integers then they are equal `φ`.

See note [partially-applied ext lemmas] for why `comp` is used here. -/
@[ext] theorem ext_rat {f g : ℚ →*₀ M₀}
  (h : f.comp (int.cast_ring_hom ℚ : ℤ →*₀ ℚ) = g.comp (int.cast_ring_hom ℚ)) : f = g :=
ext_rat' $ congr_fun h

/-- Positive integer values of a morphism `φ` and its value on `-1` completely determine `φ`. -/
theorem ext_rat_on_pnat
  (same_on_neg_one : f (-1) = g (-1)) (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
ext_rat' $ fun_like.congr_fun $ show (f : ℚ →*₀ M₀).comp (int.cast_ring_hom ℚ : ℤ →*₀ ℚ) =
  (g : ℚ →*₀ M₀).comp (int.cast_ring_hom ℚ : ℤ →*₀ ℚ),
  from ext_int' (by simpa) (by simpa)

end monoid_with_zero_hom

/-- Any two ring homomorphisms from `ℚ` to a semiring are equal. If the codomain is a division ring,
then this lemma follows from `eq_rat_cast`. -/
lemma ring_hom.ext_rat {R : Type*} [semiring R] [ring_hom_class F ℚ R] (f g : F) : f = g :=
monoid_with_zero_hom.ext_rat' $ ring_hom.congr_fun $
  ((f : ℚ →+* R).comp (int.cast_ring_hom ℚ)).ext_int ((g : ℚ →+* R).comp (int.cast_ring_hom ℚ))

instance rat.subsingleton_ring_hom {R : Type*} [semiring R] : subsingleton (ℚ →+* R) :=
⟨ring_hom.ext_rat⟩

namespace mul_opposite

variables [division_ring α]

@[simp, norm_cast] lemma op_rat_cast (r : ℚ) : op (r : α) = (↑r : αᵐᵒᵖ) :=
by rw [cast_def, div_eq_mul_inv, op_mul, op_inv, op_nat_cast, op_int_cast,
    (commute.cast_int_right _ r.num).eq, cast_def, div_eq_mul_inv]

@[simp, norm_cast] lemma unop_rat_cast (r : ℚ) : unop (r : αᵐᵒᵖ) = r :=
by rw [cast_def, div_eq_mul_inv, unop_mul, unop_inv, unop_nat_cast, unop_int_cast,
    (commute.cast_int_right _ r.num).eq, cast_def, div_eq_mul_inv]

end mul_opposite

section smul

namespace rat

variables {K : Type*} [division_ring K]

@[priority 100]
instance distrib_smul  : distrib_smul ℚ K :=
{ smul := (•),
  smul_zero := λ a, by rw [smul_def, mul_zero],
  smul_add := λ a x y, by simp only [smul_def, mul_add, cast_add] }

instance is_scalar_tower_right : is_scalar_tower ℚ K K :=
⟨λ a x y, by simp only [smul_def, smul_eq_mul, mul_assoc]⟩

end rat

end smul

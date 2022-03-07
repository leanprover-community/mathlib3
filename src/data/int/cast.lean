/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.int.basic
import data.nat.cast
import tactic.pi_instances

/-!
# Cast of integers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`int.cast`).

## Main declarations

* `cast_add_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.
-/

open nat

namespace int

/-- Coercion `ℕ → ℤ` as a `ring_hom`. -/
def of_nat_hom : ℕ →+* ℤ := ⟨coe, rfl, int.of_nat_mul, rfl, int.of_nat_add⟩

section cast
variables {α : Type*}

@[simp, norm_cast] theorem cast_mul [ring α] : ∀ m n, ((m * n : ℤ) : α) = m * n :=
λ m, int.induction_on' m 0 (by simp) (λ k _ ih n, by simp [add_mul, ih])
  (λ k _ ih n, by simp [sub_mul, ih])

/-- `coe : ℤ → α` as an `add_monoid_hom`. -/
def cast_add_hom (α : Type*) [add_group_with_one α] : ℤ →+ α := ⟨coe, cast_zero, cast_add⟩

@[simp] lemma coe_cast_add_hom [add_group_with_one α] : ⇑(cast_add_hom α) = coe := rfl

/-- `coe : ℤ → α` as a `ring_hom`. -/
def cast_ring_hom (α : Type*) [ring α] : ℤ →+* α := ⟨coe, cast_one, cast_mul, cast_zero, cast_add⟩

@[simp] lemma coe_cast_ring_hom [ring α] : ⇑(cast_ring_hom α) = coe := rfl

lemma cast_commute [ring α] : ∀ (m : ℤ) (x : α), commute ↑m x
| (n : ℕ) x := by simpa using n.cast_commute x
| -[1+ n] x := by simpa only [cast_neg_succ_of_nat, commute.neg_left_iff, commute.neg_right_iff]
  using (n + 1).cast_commute (-x)

lemma cast_comm [ring α] (m : ℤ) (x : α) : (m : α) * x = x * m :=
(cast_commute m x).eq

lemma commute_cast [ring α] (x : α) (m : ℤ) : commute x m :=
(m.cast_commute x).symm

theorem cast_mono [ordered_ring α] : monotone (coe : ℤ → α) :=
begin
  intros m n h,
  rw ← sub_nonneg at h,
  lift n - m to ℕ using h with k,
  rw [← sub_nonneg, ← cast_sub, ← h_1, cast_coe_nat],
  exact k.cast_nonneg
end

@[simp] theorem cast_nonneg [ordered_ring α] [nontrivial α] : ∀ {n : ℤ}, (0 : α) ≤ n ↔ 0 ≤ n
| (n : ℕ) := by simp
| -[1+ n] := have -(n:α) < 1, from lt_of_le_of_lt (by simp) zero_lt_one,
             by simpa [(neg_succ_lt_zero n).not_le, ← sub_eq_add_neg, le_neg] using this.not_le

@[simp, norm_cast] theorem cast_le [ordered_ring α] [nontrivial α] {m n : ℤ} :
  (m : α) ≤ n ↔ m ≤ n :=
by rw [← sub_nonneg, ← cast_sub, cast_nonneg, sub_nonneg]

theorem cast_strict_mono [ordered_ring α] [nontrivial α] : strict_mono (coe : ℤ → α) :=
strict_mono_of_le_iff_le $ λ m n, cast_le.symm

@[simp, norm_cast] theorem cast_lt [ordered_ring α] [nontrivial α] {m n : ℤ} :
  (m : α) < n ↔ m < n :=
cast_strict_mono.lt_iff_lt

@[simp] theorem cast_nonpos [ordered_ring α] [nontrivial α] {n : ℤ} : (n : α) ≤ 0 ↔ n ≤ 0 :=
by rw [← cast_zero, cast_le]

@[simp] theorem cast_pos [ordered_ring α] [nontrivial α] {n : ℤ} : (0 : α) < n ↔ 0 < n :=
by rw [← cast_zero, cast_lt]

@[simp] theorem cast_lt_zero [ordered_ring α] [nontrivial α] {n : ℤ} : (n : α) < 0 ↔ n < 0 :=
by rw [← cast_zero, cast_lt]

@[simp, norm_cast] theorem cast_min [linear_ordered_ring α] {a b : ℤ} :
  (↑(min a b) : α) = min a b :=
monotone.map_min cast_mono

@[simp, norm_cast] theorem cast_max [linear_ordered_ring α] {a b : ℤ} :
  (↑(max a b) : α) = max a b :=
monotone.map_max cast_mono

@[simp, norm_cast] theorem cast_abs [linear_ordered_ring α] {q : ℤ} :
  ((|q| : ℤ) : α) = |q| :=
by simp [abs_eq_max_neg]

lemma cast_nat_abs {R : Type*} [linear_ordered_ring R] : ∀ (n : ℤ), (n.nat_abs : R) = |n|
| (n : ℕ) := by simp only [int.nat_abs_of_nat, int.cast_coe_nat, nat.abs_cast]
| -[1+n]  := by simp only [int.nat_abs, int.cast_neg_succ_of_nat, abs_neg,
                           ← nat.cast_succ, nat.abs_cast]

lemma coe_int_dvd [comm_ring α] (m n : ℤ) (h : m ∣ n) :
  (m : α) ∣ (n : α) :=
ring_hom.map_dvd (int.cast_ring_hom α) h

/--
Auxiliary lemma for norm_cast to move the cast `-↑n` upwards to `↑-↑n`.

(The restriction to `field` is necessary, otherwise this would also apply in the case where
`R = ℤ` and cause nontermination.)
-/
@[norm_cast]
lemma cast_neg_nat_cast {R} [field R] (n : ℕ) : ((-n : ℤ) : R) = -n := by simp

end cast

end int

namespace prod

variables {α : Type*} {β : Type*} [add_group_with_one α] [add_group_with_one β]

instance : add_group_with_one (α × β) :=
{ int_cast := λ n, (n, n),
  int_cast_of_nat := λ _, by simp; refl,
  int_cast_neg_succ_of_nat := λ _, by simp; refl,
  .. prod.add_monoid_with_one, .. prod.add_group }

@[simp] lemma fst_int_cast (n : ℤ) : (n : α × β).fst = n := rfl

@[simp] lemma snd_int_cast (n : ℤ) : (n : α × β).snd = n := rfl

end prod

open int

namespace add_monoid_hom

variables {A : Type*}

/-- Two additive monoid homomorphisms `f`, `g` from `ℤ` to an additive monoid are equal
if `f 1 = g 1`. -/
@[ext] theorem ext_int [add_monoid A] {f g : ℤ →+ A} (h1 : f 1 = g 1) : f = g :=
have f.comp (int.of_nat_hom : ℕ →+ ℤ) = g.comp (int.of_nat_hom : ℕ →+ ℤ) := ext_nat' _ _ h1,
have ∀ n : ℕ, f n = g n := ext_iff.1 this,
ext $ λ n, int.cases_on n this $ λ n, eq_on_neg (this $ n + 1)

variables [add_group_with_one A]

theorem eq_int_cast_hom (f : ℤ →+ A) (h1 : f 1 = 1) : f = int.cast_add_hom A :=
ext_int $ by simp [h1]

theorem eq_int_cast (f : ℤ →+ A) (h1 : f 1 = 1) : ∀ n : ℤ, f n = n :=
ext_iff.1 (f.eq_int_cast_hom h1)

end add_monoid_hom

namespace monoid_hom
variables {M : Type*} [monoid M]
open multiplicative

@[ext] theorem ext_mint {f g : multiplicative ℤ →* M} (h1 : f (of_add 1) = g (of_add 1)) : f = g :=
monoid_hom.ext $ add_monoid_hom.ext_iff.mp $
  @add_monoid_hom.ext_int _ _ f.to_additive g.to_additive h1

/-- If two `monoid_hom`s agree on `-1` and the naturals then they are equal. -/
@[ext] theorem ext_int {f g : ℤ →* M}
  (h_neg_one : f (-1) = g (-1))
  (h_nat : f.comp int.of_nat_hom.to_monoid_hom = g.comp int.of_nat_hom.to_monoid_hom) :
  f = g :=
begin
  ext (x | x),
  { exact (monoid_hom.congr_fun h_nat x : _), },
  { rw [int.neg_succ_of_nat_eq, ← neg_one_mul, f.map_mul, g.map_mul],
    congr' 1,
    exact_mod_cast (monoid_hom.congr_fun h_nat (x + 1) : _), }
end

end monoid_hom

namespace monoid_with_zero_hom

variables {M : Type*} [monoid_with_zero M]

/-- If two `monoid_with_zero_hom`s agree on `-1` and the naturals then they are equal. -/
@[ext] lemma ext_int {f g : ℤ →*₀ M} (h_neg_one : f (-1) = g (-1))
  (h_nat : f.comp int.of_nat_hom.to_monoid_with_zero_hom =
           g.comp int.of_nat_hom.to_monoid_with_zero_hom) :
  f = g :=
to_monoid_hom_injective $ monoid_hom.ext_int h_neg_one $ monoid_hom.ext (congr_fun h_nat : _)

/-- If two `monoid_with_zero_hom`s agree on `-1` and the _positive_ naturals then they are equal. -/
lemma ext_int' {φ₁ φ₂ : ℤ →*₀ M} (h_neg_one : φ₁ (-1) = φ₂ (-1))
  (h_pos : ∀ n : ℕ, 0 < n → φ₁ n = φ₂ n) : φ₁ = φ₂ :=
ext_int h_neg_one $ ext_nat h_pos

end monoid_with_zero_hom

namespace ring_hom

variables {α : Type*} {β : Type*} [ring α] [ring β]

@[simp] lemma eq_int_cast (f : ℤ →+* α) (n : ℤ) : f n  = n :=
f.to_add_monoid_hom.eq_int_cast f.map_one n

lemma eq_int_cast' (f : ℤ →+* α) : f = int.cast_ring_hom α :=
ring_hom.ext f.eq_int_cast

@[simp] lemma map_int_cast (f : α →+* β) (n : ℤ) : f n = n :=
(f.comp (int.cast_ring_hom α)).eq_int_cast n

lemma ext_int {R : Type*} [semiring R] (f g : ℤ →+* R) : f = g :=
coe_add_monoid_hom_injective $ add_monoid_hom.ext_int $ f.map_one.trans g.map_one.symm

instance int.subsingleton_ring_hom {R : Type*} [semiring R] : subsingleton (ℤ →+* R) :=
⟨ring_hom.ext_int⟩

end ring_hom

@[simp, norm_cast] theorem int.cast_id (n : ℤ) : ↑n = n :=
((ring_hom.id ℤ).eq_int_cast n).symm

namespace pi
variables {α : Type*} {β : α → Type*} [∀ a, add_group_with_one (β a)]

instance : add_group_with_one (∀ a, β a) :=
by refine_struct { .. }; tactic.pi_instance_derive_field

lemma int_apply (n : ℤ) (a : α) : (n : ∀ a, β a) a = n := rfl

@[simp] lemma coe_int (n : ℤ) : (n : ∀ a, β a) = λ _, n := rfl

end pi

namespace mul_opposite

variables {α : Type*} [add_group_with_one α]

@[simp, norm_cast] lemma op_int_cast (z : ℤ) : op (z : α) = z := rfl

@[simp, norm_cast] lemma unop_int_cast (n : ℤ) : unop (n : αᵐᵒᵖ) = n := rfl

end mul_opposite

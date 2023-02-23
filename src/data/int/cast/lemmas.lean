/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.int.order.basic
import data.nat.cast.basic

/-!
# Cast of integers (additional theorems)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`int.cast`),
particularly results involving algebraic homomorphisms or the order structure on `ℤ`
which were not available in the import dependencies of `data.int.cast.basic`.

## Main declarations

* `cast_add_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.
-/

open nat

variables {F ι α β : Type*}

namespace int

/-- Coercion `ℕ → ℤ` as a `ring_hom`. -/
def of_nat_hom : ℕ →+* ℤ := ⟨coe, rfl, int.of_nat_mul, rfl, int.of_nat_add⟩

@[simp] theorem coe_nat_pos {n : ℕ} : (0 : ℤ) < n ↔ 0 < n := nat.cast_pos

lemma coe_nat_succ_pos (n : ℕ) : 0 < (n.succ : ℤ) := int.coe_nat_pos.2 (succ_pos n)

lemma to_nat_lt {a : ℤ} {b : ℕ} (hb : b ≠ 0) : a.to_nat < b ↔ a < b :=
by { rw [←to_nat_lt_to_nat, to_nat_coe_nat], exact coe_nat_pos.2 hb.bot_lt }

lemma nat_mod_lt {a : ℤ} {b : ℕ} (hb : b ≠ 0) : a.nat_mod b < b :=
(to_nat_lt hb).2 $ mod_lt_of_pos _ $ coe_nat_pos.2 hb.bot_lt

section cast

@[simp, norm_cast] theorem cast_mul [non_assoc_ring α] : ∀ m n, ((m * n : ℤ) : α) = m * n :=
λ m, int.induction_on' m 0 (by simp) (λ k _ ih n, by simp [add_mul, ih])
  (λ k _ ih n, by simp [sub_mul, ih])

@[simp, norm_cast] theorem cast_ite [add_group_with_one α] (P : Prop) [decidable P] (m n : ℤ) :
  ((ite P m n : ℤ) : α) = ite P m n :=
apply_ite _ _ _ _

/-- `coe : ℤ → α` as an `add_monoid_hom`. -/
def cast_add_hom (α : Type*) [add_group_with_one α] : ℤ →+ α := ⟨coe, cast_zero, cast_add⟩

@[simp] lemma coe_cast_add_hom [add_group_with_one α] : ⇑(cast_add_hom α) = coe := rfl

/-- `coe : ℤ → α` as a `ring_hom`. -/
def cast_ring_hom (α : Type*) [non_assoc_ring α] : ℤ →+* α :=
⟨coe, cast_one, cast_mul, cast_zero, cast_add⟩

@[simp] lemma coe_cast_ring_hom [non_assoc_ring α] : ⇑(cast_ring_hom α) = coe := rfl

lemma cast_commute [non_assoc_ring α] : ∀ (m : ℤ) (x : α), commute ↑m x
| (n : ℕ) x := by simpa using n.cast_commute x
| -[1+ n] x := by simpa only [cast_neg_succ_of_nat, commute.neg_left_iff, commute.neg_right_iff]
  using (n + 1).cast_commute (-x)

lemma cast_comm [non_assoc_ring α] (m : ℤ) (x : α) : (m : α) * x = x * m :=
(cast_commute m x).eq

lemma commute_cast [non_assoc_ring α] (x : α) (m : ℤ) : commute x m :=
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

section linear_ordered_ring

variables [linear_ordered_ring α] {a b : ℤ} (n : ℤ)

@[simp, norm_cast] theorem cast_min : (↑(min a b) : α) = min a b :=
monotone.map_min cast_mono

@[simp, norm_cast] theorem cast_max : (↑(max a b) : α) = max a b :=
monotone.map_max cast_mono

@[simp, norm_cast] theorem cast_abs : ((|a| : ℤ) : α) = |a| :=
by simp [abs_eq_max_neg]

lemma cast_one_le_of_pos (h : 0 < a) : (1 : α) ≤ a :=
by exact_mod_cast int.add_one_le_of_lt h

lemma cast_le_neg_one_of_neg (h : a < 0) : (a : α) ≤ -1 :=
begin
  rw [← int.cast_one, ← int.cast_neg, cast_le],
  exact int.le_sub_one_of_lt h,
end

variables (α) {n}

lemma cast_le_neg_one_or_one_le_cast_of_ne_zero (hn : n ≠ 0) : (n : α) ≤ -1 ∨ 1 ≤ (n : α) :=
hn.lt_or_lt.imp cast_le_neg_one_of_neg cast_one_le_of_pos

variables {α} (n)

lemma nneg_mul_add_sq_of_abs_le_one {x : α} (hx : |x| ≤ 1) :
  (0 : α) ≤ n * x + n * n :=
begin
  have hnx : 0 < n → 0 ≤ x + n := λ hn, by
  { convert add_le_add (neg_le_of_abs_le hx) (cast_one_le_of_pos hn),
    rw add_left_neg, },
  have hnx' : n < 0 → x + n ≤ 0 := λ hn, by
  { convert add_le_add (le_of_abs_le hx) (cast_le_neg_one_of_neg hn),
    rw add_right_neg, },
  rw [← mul_add, mul_nonneg_iff],
  rcases lt_trichotomy n 0 with h | rfl | h,
  { exact or.inr ⟨by exact_mod_cast h.le, hnx' h⟩, },
  { simp [le_total 0 x], },
  { exact or.inl ⟨by exact_mod_cast h.le, hnx h⟩, },
end

lemma cast_nat_abs : (n.nat_abs : α) = |n| :=
begin
  cases n,
  { simp, },
  { simp only [int.nat_abs, int.cast_neg_succ_of_nat, abs_neg, ← nat.cast_succ, nat.abs_cast], },
end

end linear_ordered_ring

lemma coe_int_dvd [comm_ring α] (m n : ℤ) (h : m ∣ n) :
  (m : α) ∣ (n : α) :=
ring_hom.map_dvd (int.cast_ring_hom α) h

end cast

end int

open int

namespace add_monoid_hom

variables {A : Type*}

/-- Two additive monoid homomorphisms `f`, `g` from `ℤ` to an additive monoid are equal
if `f 1 = g 1`. -/
@[ext] theorem ext_int [add_monoid A] {f g : ℤ →+ A} (h1 : f 1 = g 1) : f = g :=
have f.comp (int.of_nat_hom : ℕ →+ ℤ) = g.comp (int.of_nat_hom : ℕ →+ ℤ) := ext_nat' _ _ h1,
have ∀ n : ℕ, f n = g n := ext_iff.1 this,
ext $ λ n, int.cases_on n this $ λ n, eq_on_neg _ _ (this $ n + 1)

variables [add_group_with_one A]

theorem eq_int_cast_hom (f : ℤ →+ A) (h1 : f 1 = 1) : f = int.cast_add_hom A :=
ext_int $ by simp [h1]

end add_monoid_hom

lemma eq_int_cast' [add_group_with_one α] [add_monoid_hom_class F ℤ α] (f : F) (h₁ : f 1 = 1) :
  ∀ n : ℤ, f n = n :=
add_monoid_hom.ext_iff.1 $ (f : ℤ →+ α).eq_int_cast_hom h₁

@[simp] lemma int.cast_add_hom_int : int.cast_add_hom ℤ = add_monoid_hom.id ℤ :=
((add_monoid_hom.id ℤ).eq_int_cast_hom rfl).symm

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

end monoid_with_zero_hom

/-- If two `monoid_with_zero_hom`s agree on `-1` and the _positive_ naturals then they are equal. -/
lemma ext_int' [monoid_with_zero α] [monoid_with_zero_hom_class F ℤ α] {f g : F}
  (h_neg_one : f (-1) = g (-1)) (h_pos : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
fun_like.ext _ _ $ λ n, by { have := fun_like.congr_fun (@monoid_with_zero_hom.ext_int _ _
  (f : ℤ →*₀ α) (g : ℤ →*₀ α) h_neg_one $ monoid_with_zero_hom.ext_nat h_pos) n, exact this }

section non_assoc_ring
variables [non_assoc_ring α] [non_assoc_ring β]

@[simp] lemma eq_int_cast [ring_hom_class F ℤ α] (f : F) (n : ℤ) : f n = n :=
eq_int_cast' f (map_one _) n

@[simp] lemma map_int_cast [ring_hom_class F α β] (f : F) (n : ℤ) : f n = n :=
eq_int_cast ((f : α →+* β).comp (int.cast_ring_hom α)) n

namespace ring_hom

lemma eq_int_cast' (f : ℤ →+* α) : f = int.cast_ring_hom α := ring_hom.ext $ eq_int_cast f

lemma ext_int {R : Type*} [non_assoc_semiring R] (f g : ℤ →+* R) : f = g :=
coe_add_monoid_hom_injective $ add_monoid_hom.ext_int $ f.map_one.trans g.map_one.symm

instance int.subsingleton_ring_hom {R : Type*} [non_assoc_semiring R] : subsingleton (ℤ →+* R) :=
⟨ring_hom.ext_int⟩

end ring_hom
end non_assoc_ring

@[simp, norm_cast] lemma int.cast_id (n : ℤ) : ↑n = n := (eq_int_cast (ring_hom.id ℤ) _).symm

@[simp] lemma int.cast_ring_hom_int : int.cast_ring_hom ℤ = ring_hom.id ℤ :=
(ring_hom.id ℤ).eq_int_cast'.symm

namespace pi
variables {π : ι → Type*} [Π i, has_int_cast (π i)]

instance : has_int_cast (Π i, π i) :=
by refine_struct { .. }; tactic.pi_instance_derive_field

lemma int_apply (n : ℤ) (i : ι) : (n : Π i, π i) i = n := rfl

@[simp] lemma coe_int (n : ℤ) : (n : Π i, π i) = λ _, n := rfl

end pi

lemma sum.elim_int_cast_int_cast {α β γ : Type*} [has_int_cast γ] (n : ℤ) :
  sum.elim (n : α → γ) (n : β → γ) = n :=
@sum.elim_lam_const_lam_const α β γ n

namespace pi
variables {π : ι → Type*} [Π i, add_group_with_one (π i)]

instance : add_group_with_one (Π i, π i) :=
by refine_struct { .. }; tactic.pi_instance_derive_field

end pi

namespace mul_opposite
variables [add_group_with_one α]

@[simp, norm_cast] lemma op_int_cast (z : ℤ) : op (z : α) = z := rfl

@[simp, norm_cast] lemma unop_int_cast (n : ℤ) : unop (n : αᵐᵒᵖ) = n := rfl

end mul_opposite

/-! ### Order dual -/

open order_dual

instance [h : has_int_cast α] : has_int_cast αᵒᵈ := h
instance [h : add_group_with_one α] : add_group_with_one αᵒᵈ := h
instance [h : add_comm_group_with_one α] : add_comm_group_with_one αᵒᵈ := h

@[simp] lemma to_dual_int_cast [has_int_cast α] (n : ℤ) : to_dual (n : α) = n := rfl
@[simp] lemma of_dual_int_cast [has_int_cast α] (n : ℤ) : (of_dual n : α) = n := rfl

/-! ### Lexicographic order -/

instance [h : has_int_cast α] : has_int_cast (lex α) := h
instance [h : add_group_with_one α] : add_group_with_one (lex α) := h
instance [h : add_comm_group_with_one α] : add_comm_group_with_one (lex α) := h

@[simp] lemma to_lex_int_cast [has_int_cast α] (n : ℤ) : to_lex (n : α) = n := rfl
@[simp] lemma of_lex_int_cast [has_int_cast α] (n : ℤ) : (of_lex n : α) = n := rfl

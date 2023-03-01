/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.char_zero.defs
import algebra.group_with_zero.commute
import algebra.hom.ring
import algebra.order.group.abs
import algebra.ring.commute
import data.nat.order.basic
import algebra.group.opposite

/-!
# Cast of natural numbers (additional theorems)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves additional properties about the *canonical* homomorphism from
the natural numbers into an additive monoid with a one (`nat.cast`).

## Main declarations

* `cast_add_monoid_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.
-/

variables {α β : Type*}

namespace nat

/-- `coe : ℕ → α` as an `add_monoid_hom`. -/
def cast_add_monoid_hom (α : Type*) [add_monoid_with_one α] : ℕ →+ α :=
{ to_fun := coe,
  map_add' := cast_add,
  map_zero' := cast_zero }

@[simp] lemma coe_cast_add_monoid_hom [add_monoid_with_one α] :
  (cast_add_monoid_hom α : ℕ → α) = coe := rfl

@[simp, norm_cast] theorem cast_mul [non_assoc_semiring α] (m n : ℕ) :
  ((m * n : ℕ) : α) = m * n :=
by induction n; simp [mul_succ, mul_add, *]

/-- `coe : ℕ → α` as a `ring_hom` -/
def cast_ring_hom (α : Type*) [non_assoc_semiring α] : ℕ →+* α :=
{ to_fun := coe,
  map_one' := cast_one,
  map_mul' := cast_mul,
  .. cast_add_monoid_hom α }

@[simp] lemma coe_cast_ring_hom [non_assoc_semiring α] : (cast_ring_hom α : ℕ → α) = coe := rfl

lemma cast_commute [non_assoc_semiring α] (n : ℕ) (x : α) : commute ↑n x :=
nat.rec_on n (by rw [cast_zero]; exact commute.zero_left x) $
λ n ihn, by rw [cast_succ]; exact ihn.add_left (commute.one_left x)

lemma cast_comm [non_assoc_semiring α] (n : ℕ) (x : α) : (n : α) * x = x * n :=
(cast_commute n x).eq

lemma commute_cast [non_assoc_semiring α] (x : α) (n : ℕ) : commute x n :=
(n.cast_commute x).symm

section ordered_semiring
variables [ordered_semiring α]

@[mono] theorem mono_cast : monotone (coe : ℕ → α) :=
monotone_nat_of_le_succ $ λ n, by rw [nat.cast_succ]; exact le_add_of_nonneg_right zero_le_one

@[simp] theorem cast_nonneg (n : ℕ) : 0 ≤ (n : α) :=
@nat.cast_zero α _ ▸ mono_cast (nat.zero_le n)

section nontrivial
variable [nontrivial α]

lemma cast_add_one_pos (n : ℕ) : 0 < (n : α) + 1 :=
zero_lt_one.trans_le $ le_add_of_nonneg_left n.cast_nonneg

@[simp] lemma cast_pos {n : ℕ} : (0 : α) < n ↔ 0 < n := by cases n; simp [cast_add_one_pos]

end nontrivial

variables [char_zero α] {m n : ℕ}

lemma strict_mono_cast : strict_mono (coe : ℕ → α) :=
mono_cast.strict_mono_of_injective cast_injective

/-- `coe : ℕ → α` as an `order_embedding` -/
@[simps { fully_applied := ff }] def cast_order_embedding : ℕ ↪o α :=
order_embedding.of_strict_mono coe nat.strict_mono_cast

@[simp, norm_cast] lemma cast_le : (m : α) ≤ n ↔ m ≤ n := strict_mono_cast.le_iff_le
@[simp, norm_cast, mono] lemma cast_lt : (m : α) < n ↔ m < n := strict_mono_cast.lt_iff_lt

@[simp, norm_cast] lemma one_lt_cast : 1 < (n : α) ↔ 1 < n := by rw [←cast_one, cast_lt]
@[simp, norm_cast] lemma one_le_cast : 1 ≤ (n : α) ↔ 1 ≤ n := by rw [←cast_one, cast_le]

@[simp, norm_cast] lemma cast_lt_one : (n : α) < 1 ↔ n = 0 :=
by rw [←cast_one, cast_lt, lt_succ_iff, ←bot_eq_zero, le_bot_iff]

@[simp, norm_cast] lemma cast_le_one : (n : α) ≤ 1 ↔ n ≤ 1 := by rw [←cast_one, cast_le]

end ordered_semiring

/-- A version of `nat.cast_sub` that works for `ℝ≥0` and `ℚ≥0`. Note that this proof doesn't work
for `ℕ∞` and `ℝ≥0∞`, so we use type-specific lemmas for these types. -/
@[simp, norm_cast] lemma cast_tsub [canonically_ordered_comm_semiring α] [has_sub α]
  [has_ordered_sub α] [contravariant_class α α (+) (≤)] (m n : ℕ) :
  ↑(m - n) = (m - n : α) :=
begin
  cases le_total m n with h h,
  { rw [tsub_eq_zero_of_le h, cast_zero, tsub_eq_zero_of_le],
    exact mono_cast h },
  { rcases le_iff_exists_add'.mp h with ⟨m, rfl⟩,
    rw [add_tsub_cancel_right, cast_add, add_tsub_cancel_right] }
end

@[simp, norm_cast] theorem cast_min [linear_ordered_semiring α] {a b : ℕ} :
  (↑(min a b) : α) = min a b :=
(@mono_cast α _).map_min

@[simp, norm_cast] theorem cast_max [linear_ordered_semiring α] {a b : ℕ} :
  (↑(max a b) : α) = max a b :=
(@mono_cast α _).map_max

@[simp, norm_cast] theorem abs_cast [linear_ordered_ring α] (a : ℕ) :
  |(a : α)| = a :=
abs_of_nonneg (cast_nonneg a)

lemma coe_nat_dvd [semiring α] {m n : ℕ} (h : m ∣ n) : (m : α) ∣ (n : α) :=
map_dvd (nat.cast_ring_hom α) h

alias coe_nat_dvd ← _root_.has_dvd.dvd.nat_cast

end nat

section add_monoid_hom_class

variables {A B F : Type*} [add_monoid_with_one B]

lemma ext_nat' [add_monoid A] [add_monoid_hom_class F ℕ A] (f g : F) (h : f 1 = g 1) : f = g :=
fun_like.ext f g $ begin
  apply nat.rec,
  { simp only [nat.nat_zero_eq_zero, map_zero] },
  simp [nat.succ_eq_add_one, h] {contextual := tt}
end

@[ext] lemma add_monoid_hom.ext_nat [add_monoid A] : ∀ {f g : ℕ →+ A}, ∀ h : f 1 = g 1, f = g :=
ext_nat'

variable [add_monoid_with_one A]

-- these versions are primed so that the `ring_hom_class` versions aren't
lemma eq_nat_cast' [add_monoid_hom_class F ℕ A] (f : F) (h1 : f 1 = 1) :
  ∀ n : ℕ, f n = n
| 0     := by simp
| (n+1) := by rw [map_add, h1, eq_nat_cast' n, nat.cast_add_one]

lemma map_nat_cast' {A} [add_monoid_with_one A] [add_monoid_hom_class F A B]
                    (f : F) (h : f 1 = 1) : ∀ (n : ℕ), f n = n
| 0     := by simp
| (n+1) := by rw [nat.cast_add, map_add, nat.cast_add, map_nat_cast', nat.cast_one, h, nat.cast_one]

end add_monoid_hom_class

section monoid_with_zero_hom_class

variables {A F : Type*} [mul_zero_one_class A]

/-- If two `monoid_with_zero_hom`s agree on the positive naturals they are equal. -/
theorem ext_nat'' [monoid_with_zero_hom_class F ℕ A] (f g : F)
  (h_pos : ∀ {n : ℕ}, 0 < n → f n = g n) : f = g :=
begin
  apply fun_like.ext,
  rintro (_|n),
  { simp },
  exact h_pos n.succ_pos
end

@[ext] theorem monoid_with_zero_hom.ext_nat :
  ∀ {f g : ℕ →*₀ A}, (∀ {n : ℕ}, 0 < n → f n = g n) → f = g := ext_nat''

end monoid_with_zero_hom_class

section ring_hom_class

variables {R S F : Type*} [non_assoc_semiring R] [non_assoc_semiring S]

@[simp] lemma eq_nat_cast [ring_hom_class F ℕ R] (f : F) : ∀ n, f n = n :=
eq_nat_cast' f $ map_one f

@[simp] lemma map_nat_cast [ring_hom_class F R S] (f : F) : ∀ n : ℕ, f (n : R) = n :=
map_nat_cast' f $ map_one f

lemma ext_nat [ring_hom_class F ℕ R] (f g : F) : f = g :=
ext_nat' f g $ by simp only [map_one]

lemma ne_zero.nat_of_injective {n : ℕ} [h : ne_zero (n : R)]
  [ring_hom_class F R S] {f : F} (hf : function.injective f) : ne_zero (n : S) :=
⟨λ h, (ne_zero.nat_cast_ne n R) $ hf $ by simpa only [map_nat_cast, map_zero]⟩

lemma ne_zero.nat_of_ne_zero {R S} [semiring R] [semiring S] {F} [ring_hom_class F R S] (f : F)
  {n : ℕ} [hn : ne_zero (n : S)] : ne_zero (n : R) :=
by { apply ne_zero.of_map f, simp only [map_nat_cast, hn] }

end ring_hom_class

namespace ring_hom

/-- This is primed to match `eq_int_cast'`. -/
lemma eq_nat_cast' {R} [non_assoc_semiring R] (f : ℕ →+* R) : f = nat.cast_ring_hom R :=
ring_hom.ext $ eq_nat_cast f

end ring_hom

@[simp, norm_cast] theorem nat.cast_id (n : ℕ) : ↑n = n :=
rfl

@[simp] lemma nat.cast_ring_hom_nat : nat.cast_ring_hom ℕ = ring_hom.id ℕ := rfl

-- I don't think `ring_hom_class` is good here, because of the `subsingleton` TC slowness
instance nat.unique_ring_hom {R : Type*} [non_assoc_semiring R] : unique (ℕ →+* R) :=
{ default := nat.cast_ring_hom R, uniq := ring_hom.eq_nat_cast' }

namespace mul_opposite
variables [add_monoid_with_one α]

@[simp, norm_cast] lemma op_nat_cast (n : ℕ) : op (n : α) = n := rfl

@[simp, norm_cast] lemma unop_nat_cast (n : ℕ) : unop (n : αᵐᵒᵖ) = n := rfl

end mul_opposite

namespace pi
variables {π : α → Type*} [Π a, has_nat_cast (π a)]

instance : has_nat_cast (Π a, π a) :=
by refine_struct { .. }; tactic.pi_instance_derive_field

lemma nat_apply (n : ℕ) (a : α) : (n : Π a, π a) a = n := rfl

@[simp] lemma coe_nat (n : ℕ) : (n : Π a, π a) = λ _, n := rfl

end pi

lemma sum.elim_nat_cast_nat_cast {α β γ : Type*} [has_nat_cast γ] (n : ℕ) :
  sum.elim (n : α → γ) (n : β → γ) = n :=
@sum.elim_lam_const_lam_const α β γ n

namespace pi
variables {π : α → Type*} [Π a, add_monoid_with_one (π a)]

instance : add_monoid_with_one (Π a, π a) :=
by refine_struct { .. }; tactic.pi_instance_derive_field

end pi

/-! ### Order dual -/

open order_dual

instance [h : has_nat_cast α] : has_nat_cast αᵒᵈ := h
instance [h : add_monoid_with_one α] : add_monoid_with_one αᵒᵈ := h
instance [h : add_comm_monoid_with_one α] : add_comm_monoid_with_one αᵒᵈ := h

@[simp] lemma to_dual_nat_cast [has_nat_cast α] (n : ℕ) : to_dual (n : α) = n := rfl
@[simp] lemma of_dual_nat_cast [has_nat_cast α] (n : ℕ) : (of_dual n : α) = n := rfl

/-! ### Lexicographic order -/

instance [h : has_nat_cast α] : has_nat_cast (lex α) := h
instance [h : add_monoid_with_one α] : add_monoid_with_one (lex α) := h
instance [h : add_comm_monoid_with_one α] : add_comm_monoid_with_one (lex α) := h

@[simp] lemma to_lex_nat_cast [has_nat_cast α] (n : ℕ) : to_lex (n : α) = n := rfl
@[simp] lemma of_lex_nat_cast [has_nat_cast α] (n : ℕ) : (of_lex n : α) = n := rfl

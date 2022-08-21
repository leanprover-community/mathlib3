/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.nat.basic
import data.nat.cast.defs
import algebra.group.pi
import tactic.pi_instances
import data.sum.basic

/-!
# Cast of natural numbers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the natural numbers into an additive monoid with a one (`nat.cast`).

## Main declarations

* `cast_add_monoid_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.
-/

namespace nat
variables {α : Type*}

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

section

variables [ordered_semiring α]

@[mono] theorem mono_cast : monotone (coe : ℕ → α) :=
monotone_nat_of_le_succ $ λ n, by rw [nat.cast_succ]; exact le_add_of_nonneg_right zero_le_one

@[simp] theorem cast_nonneg (n : ℕ) : 0 ≤ (n : α) :=
@nat.cast_zero α _ ▸ mono_cast (nat.zero_le n)

variable [nontrivial α]

@[simp, norm_cast] theorem cast_le {m n : ℕ} :
  (m : α) ≤ n ↔ m ≤ n :=
strict_mono_cast.le_iff_le

@[simp, norm_cast, mono] theorem cast_lt {m n : ℕ} : (m : α) < n ↔ m < n :=
strict_mono_cast.lt_iff_lt

@[simp] theorem cast_pos {n : ℕ} : (0 : α) < n ↔ 0 < n :=
by rw [← cast_zero, cast_lt]

lemma cast_add_one_pos (n : ℕ) : 0 < (n : α) + 1 :=
  add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

@[simp, norm_cast] theorem one_lt_cast {n : ℕ} : 1 < (n : α) ↔ 1 < n :=
by rw [← cast_one, cast_lt]

@[simp, norm_cast] theorem one_le_cast {n : ℕ} : 1 ≤ (n : α) ↔ 1 ≤ n :=
by rw [← cast_one, cast_le]

@[simp, norm_cast] theorem cast_lt_one {n : ℕ} : (n : α) < 1 ↔ n = 0 :=
by rw [← cast_one, cast_lt, lt_succ_iff, le_zero_iff]

@[simp, norm_cast] theorem cast_le_one {n : ℕ} : (n : α) ≤ 1 ↔ n ≤ 1 :=
by rw [← cast_one, cast_le]

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

namespace prod

variables {α : Type*} {β : Type*} [add_monoid_with_one α] [add_monoid_with_one β]

instance : add_monoid_with_one (α × β) :=
{ nat_cast := λ n, (n, n),
  nat_cast_zero := congr_arg2 prod.mk nat.cast_zero nat.cast_zero,
  nat_cast_succ := λ n, congr_arg2 prod.mk (nat.cast_succ _) (nat.cast_succ _),
  .. prod.add_monoid, .. prod.has_one }

@[simp] lemma fst_nat_cast (n : ℕ) : (n : α × β).fst = n :=
by induction n; simp *

@[simp] lemma snd_nat_cast (n : ℕ) : (n : α × β).snd = n :=
by induction n; simp *

end prod

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

end ring_hom_class

namespace ring_hom

/-- This is primed to match `eq_int_cast'`. -/
lemma eq_nat_cast' {R} [non_assoc_semiring R] (f : ℕ →+* R) : f = nat.cast_ring_hom R :=
ring_hom.ext $ eq_nat_cast f

end ring_hom

@[simp, norm_cast] theorem nat.cast_id (n : ℕ) : ↑n = n :=
rfl

@[simp] lemma nat.cast_ring_hom_nat : nat.cast_ring_hom ℕ = ring_hom.id ℕ := rfl

@[simp] theorem nat.cast_with_bot (n : ℕ) :
  @coe ℕ (with_bot ℕ) (@coe_to_lift _ _ nat.cast_coe) n = n := rfl

-- I don't think `ring_hom_class` is good here, because of the `subsingleton` TC slowness
instance nat.unique_ring_hom {R : Type*} [non_assoc_semiring R] : unique (ℕ →+* R) :=
{ default := nat.cast_ring_hom R, uniq := ring_hom.eq_nat_cast' }

namespace mul_opposite

variables {α : Type*} [add_monoid_with_one α]

@[simp, norm_cast] lemma op_nat_cast (n : ℕ) : op (n : α) = n := rfl

@[simp, norm_cast] lemma unop_nat_cast (n : ℕ) : unop (n : αᵐᵒᵖ) = n := rfl

end mul_opposite

namespace with_top
variables {α : Type*}

variables [add_monoid_with_one α]

@[simp, norm_cast] lemma coe_nat : ∀ (n : ℕ), ((n : α) : with_top α) = n
| 0     := rfl
| (n+1) := by { push_cast, rw [coe_nat n] }

@[simp] lemma nat_ne_top (n : nat) : (n : with_top α) ≠ ⊤ :=
by { rw [←coe_nat n], apply coe_ne_top }

@[simp] lemma top_ne_nat (n : nat) : (⊤ : with_top α) ≠ n :=
by { rw [←coe_nat n], apply top_ne_coe }

lemma add_one_le_of_lt {i n : with_top ℕ} (h : i < n) : i + 1 ≤ n :=
begin
  cases n, { exact le_top },
  cases i, { exact (not_le_of_lt h le_top).elim },
  exact with_top.coe_le_coe.2 (with_top.coe_lt_coe.1 h)
end

lemma one_le_iff_pos {n : with_top ℕ} : 1 ≤ n ↔ 0 < n :=
⟨lt_of_lt_of_le (coe_lt_coe.mpr zero_lt_one),
  λ h, by simpa only [zero_add] using add_one_le_of_lt h⟩

@[elab_as_eliminator]
lemma nat_induction {P : with_top ℕ → Prop} (a : with_top ℕ)
  (h0 : P 0) (hsuc : ∀n:ℕ, P n → P n.succ) (htop : (∀n : ℕ, P n) → P ⊤) : P a :=
begin
  have A : ∀n:ℕ, P n := λ n, nat.rec_on n h0 hsuc,
  cases a,
  { exact htop A },
  { exact A a }
end

end with_top

namespace pi
variables {α : Type*} {β : α → Type*} [∀ a, has_nat_cast (β a)]

instance : has_nat_cast (∀ a, β a) :=
by refine_struct { .. }; tactic.pi_instance_derive_field

lemma nat_apply (n : ℕ) (a : α) : (n : ∀ a, β a) a = n := rfl

@[simp] lemma coe_nat (n : ℕ) : (n : ∀ a, β a) = λ _, n := rfl

end pi

lemma sum.elim_nat_cast_nat_cast {α β γ : Type*} [has_nat_cast γ] (n : ℕ) :
  sum.elim (n : α → γ) (n : β → γ) = n :=
@sum.elim_lam_const_lam_const α β γ n

namespace pi
variables {α : Type*} {β : α → Type*} [∀ a, add_monoid_with_one (β a)]

instance : add_monoid_with_one (∀ a, β a) :=
by refine_struct { .. }; tactic.pi_instance_derive_field

end pi

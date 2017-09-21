/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.order algebra.ordered_group algebra.ring

universe u
variable {α : Type u}

section linear_ordered_semiring
variable [linear_ordered_semiring α]

@[simp] lemma mul_le_mul_left {a b c : α} (h : 0 < c) : c * a ≤ c * b ↔ a ≤ b :=
⟨λ h', le_of_mul_le_mul_left h' h, λ h', mul_le_mul_of_nonneg_left h' (le_of_lt h)⟩

@[simp] lemma mul_le_mul_right {a b c : α} (h : 0 < c) : a * c ≤ b * c ↔ a ≤ b :=
⟨λ h', le_of_mul_le_mul_right h' h, λ h', mul_le_mul_of_nonneg_right h' (le_of_lt h)⟩

@[simp] lemma mul_lt_mul_left {a b c : α} (h : 0 < c) : c * a < c * b ↔ a < b :=
⟨λ h', lt_of_mul_lt_mul_left h' (le_of_lt h), λ h', mul_lt_mul_of_pos_left h' h⟩

@[simp] lemma mul_lt_mul_right {a b c : α} (h : 0 < c) : a * c < b * c ↔ a < b :=
⟨λ h', lt_of_mul_lt_mul_right h' (le_of_lt h), λ h', mul_lt_mul_of_pos_right h' h⟩

lemma le_mul_iff_one_le_left {a b : α} (hb : b > 0) : b ≤ a * b ↔ 1 ≤ a :=
suffices 1 * b ≤ a * b ↔ 1 ≤ a, by rwa one_mul at this,
mul_le_mul_right hb

lemma lt_mul_iff_one_lt_left {a b : α} (hb : b > 0) : b < a * b ↔ 1 < a :=
suffices 1 * b < a * b ↔ 1 < a, by rwa one_mul at this,
mul_lt_mul_right hb

lemma le_mul_iff_one_le_right {a b : α} (hb : b > 0) : b ≤ b * a ↔ 1 ≤ a :=
suffices b * 1 ≤ b * a ↔ 1 ≤ a, by rwa mul_one at this,
mul_le_mul_left hb

lemma lt_mul_iff_one_lt_right {a b : α} (hb : b > 0) : b < b * a ↔ 1 < a :=
suffices b * 1 < b * a ↔ 1 < a, by rwa mul_one at this,
mul_lt_mul_left hb

lemma lt_mul_of_gt_one_right' {a b : α} (hb : b > 0) : a > 1 → b < b * a :=
(lt_mul_iff_one_lt_right hb).2

lemma le_mul_of_ge_one_right' {a b : α} (hb : b ≥ 0) (h : a ≥ 1) : b ≤ b * a :=
suffices b * 1 ≤ b * a, by rwa mul_one at this,
mul_le_mul_of_nonneg_left h hb

lemma le_mul_of_ge_one_left' {a b : α} (hb : b ≥ 0) (h : a ≥ 1) : b ≤ a * b :=
suffices 1 * b ≤ a * b, by rwa one_mul at this,
mul_le_mul_of_nonneg_right h hb

end linear_ordered_semiring

instance to_domain [s : linear_ordered_ring α] : domain α :=
{ s with
  eq_zero_or_eq_zero_of_mul_eq_zero := @linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero α s }

section linear_ordered_ring
variable [linear_ordered_ring α]

@[simp] lemma mul_le_mul_left_of_neg {a b c : α} (h : c < 0) : c * a ≤ c * b ↔ b ≤ a :=
⟨le_imp_le_iff_lt_imp_lt.2 $ λ h', mul_lt_mul_of_neg_left h' h,
  λ h', mul_le_mul_of_nonpos_left h' (le_of_lt h)⟩

@[simp] lemma mul_le_mul_right_of_neg {a b c : α} (h : c < 0) : a * c ≤ b * c ↔ b ≤ a :=
⟨le_imp_le_iff_lt_imp_lt.2 $ λ h', mul_lt_mul_of_neg_right h' h,
  λ h', mul_le_mul_of_nonpos_right h' (le_of_lt h)⟩

@[simp] lemma mul_lt_mul_left_of_neg {a b c : α} (h : c < 0) : c * a < c * b ↔ b < a :=
le_iff_le_iff_lt_iff_lt.1 (mul_le_mul_left_of_neg h)

@[simp] lemma mul_lt_mul_right_of_neg {a b c : α} (h : c < 0) : a * c < b * c ↔ b < a :=
le_iff_le_iff_lt_iff_lt.1 (mul_le_mul_right_of_neg h)

end linear_ordered_ring

set_option old_structure_cmd true
class nonneg_ring (α : Type*)
  extends ring α, zero_ne_one_class α, nonneg_comm_group α :=
(mul_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a * b))
(mul_pos : ∀ {a b}, pos a → pos b → pos (a * b))

class linear_nonneg_ring (α : Type*) extends domain α, nonneg_comm_group α :=
(mul_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a * b))
(nonneg_total : ∀ a, nonneg a ∨ nonneg (-a))

namespace nonneg_ring
open nonneg_comm_group
variable [s : nonneg_ring α]

instance to_ordered_ring : ordered_ring α :=
{ s with
  le := (≤),
  lt := (<),
  lt_iff_le_not_le := @lt_iff_le_not_le _ _,
  le_refl := @le_refl _ _,
  le_trans := @le_trans _ _,
  le_antisymm := @le_antisymm _ _,
  add_lt_add_left := @add_lt_add_left _ _,
  add_le_add_left := @add_le_add_left _ _,
  mul_nonneg := λ a b, by simp [nonneg_def.symm]; exact mul_nonneg,
  mul_pos := λ a b, by simp [pos_def.symm]; exact mul_pos }

def nonneg_ring.to_linear_nonneg_ring
  (nonneg_total : ∀ a : α, nonneg a ∨ nonneg (-a))
  : linear_nonneg_ring α :=
{ s with
  nonneg_total := nonneg_total,
  eq_zero_or_eq_zero_of_mul_eq_zero :=
    suffices ∀ {a} b : α, nonneg a → a * b = 0 → a = 0 ∨ b = 0,
    from λ a b, (nonneg_total a).elim (this b)
      (λ na, by simpa using this b na),
    suffices ∀ {a b : α}, nonneg a → nonneg b → a * b = 0 → a = 0 ∨ b = 0,
    from λ a b na, (nonneg_total b).elim (this na)
      (λ nb, by simpa using this na nb),
    λ a b na nb z, classical.by_cases
      (λ nna : nonneg (-a), or.inl (nonneg_antisymm na nna))
      (λ pa, classical.by_cases
        (λ nnb : nonneg (-b), or.inr (nonneg_antisymm nb nnb))
        (λ pb, absurd z $ ne_of_gt $ pos_def.1 $ mul_pos
          ((pos_iff _ _).2 ⟨na, pa⟩)
          ((pos_iff _ _).2 ⟨nb, pb⟩))) }

end nonneg_ring

namespace linear_nonneg_ring
open nonneg_comm_group
variable [s : linear_nonneg_ring α]

instance to_nonneg_ring : nonneg_ring α :=
{ s with
  mul_pos := λ a b pa pb,
  let ⟨a1, a2⟩ := (pos_iff α a).1 pa,
      ⟨b1, b2⟩ := (pos_iff α b).1 pb in
  have ab : nonneg (a * b), from mul_nonneg a1 b1,
  (pos_iff α _).2 ⟨ab, λ hn,
    have a * b = 0, from nonneg_antisymm ab hn,
    (eq_zero_or_eq_zero_of_mul_eq_zero _ _ this).elim
      (ne_of_gt (pos_def.1 pa))
      (ne_of_gt (pos_def.1 pb))⟩ }

instance to_linear_order : linear_order α :=
{ s with
  le := (≤),
  lt := (<),
  lt_iff_le_not_le := @lt_iff_le_not_le _ _,
  le_refl := @le_refl _ _,
  le_trans := @le_trans _ _,
  le_antisymm := @le_antisymm _ _,
  le_total := nonneg_total_iff.1 nonneg_total }

instance to_linear_ordered_ring : linear_ordered_ring α :=
{ s with
  le := (≤),
  lt := (<),
  lt_iff_le_not_le := @lt_iff_le_not_le _ _,
  le_refl := @le_refl _ _,
  le_trans := @le_trans _ _,
  le_antisymm := @le_antisymm _ _,
  le_total := @le_total _ _,
  add_lt_add_left := @add_lt_add_left _ _,
  add_le_add_left := @add_le_add_left _ _,
  mul_nonneg := by simp [nonneg_def.symm]; exact @mul_nonneg _ _,
  mul_pos := by simp [pos_def.symm]; exact @nonneg_ring.mul_pos _ _,
  zero_lt_one := lt_of_not_ge $ λ (h : nonneg (0 - 1)), begin
    rw [zero_sub] at h,
    have := mul_nonneg h h, simp at this,
    exact zero_ne_one _ (nonneg_antisymm this h).symm
  end }

instance to_decidable_linear_ordered_comm_ring
  [decidable_pred (@nonneg α _)]
  [comm : @is_commutative α (*)]
  : decidable_linear_ordered_comm_ring α :=
{ @linear_nonneg_ring.to_linear_ordered_ring _ s with
  decidable_le := by apply_instance,
  decidable_eq := by apply_instance,
  decidable_lt := by apply_instance,
  mul_comm := is_commutative.comm (*) }

end linear_nonneg_ring

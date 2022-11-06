/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import algebra.order.field.defs
import data.rat.basic
import tactic.find_unused

/-!
# Order for Rational Numbers

## Summary

We define the order on `ℚ`, prove that `ℚ` is a discrete, linearly ordered field, and define
functions such as `abs` and `sqrt` that depend on this order.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering, sqrt, abs
-/

namespace rat
variables (a b c : ℚ)
open_locale rat

/-- A rational number is called nonnegative if its numerator is nonnegative. -/
protected def nonneg (r : ℚ) : Prop := 0 ≤ r.num

@[simp] theorem mk_nonneg (a : ℤ) {b : ℤ} (h : 0 < b) : (a /. b).nonneg ↔ 0 ≤ a :=
begin
  generalize ha : a /. b = x, cases x with n₁ d₁ h₁ c₁, rw num_denom' at ha,
  simp [rat.nonneg],
  have d0 := int.coe_nat_lt.2 h₁,
  have := (mk_eq (ne_of_gt h) (ne_of_gt d0)).1 ha,
  constructor; intro h₂,
  { apply nonneg_of_mul_nonneg_left _ d0,
    rw this, exact mul_nonneg h₂ (le_of_lt h) },
  { apply nonneg_of_mul_nonneg_left _ h,
    rw ← this, exact mul_nonneg h₂ (int.coe_zero_le _) },
end

protected lemma nonneg_add {a b} : rat.nonneg a → rat.nonneg b → rat.nonneg (a + b) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
begin
  have d₁0 : 0 < (d₁:ℤ) := int.coe_nat_pos.2 (nat.pos_of_ne_zero h₁),
  have d₂0 : 0 < (d₂:ℤ) := int.coe_nat_pos.2 (nat.pos_of_ne_zero h₂),
  simp [d₁0, d₂0, h₁, h₂, mul_pos d₁0 d₂0],
  intros n₁0 n₂0,
  apply add_nonneg; apply mul_nonneg; {assumption <|> apply int.coe_zero_le},
end

protected lemma nonneg_mul {a b} : rat.nonneg a → rat.nonneg b → rat.nonneg (a * b) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
begin
  have d₁0 : 0 < (d₁:ℤ) := int.coe_nat_pos.2 (nat.pos_of_ne_zero h₁),
  have d₂0 : 0 < (d₂:ℤ) := int.coe_nat_pos.2 (nat.pos_of_ne_zero h₂),
  simp [d₁0, d₂0, h₁, h₂, mul_pos d₁0 d₂0, mul_nonneg] { contextual := tt }
end

protected lemma nonneg_antisymm {a} : rat.nonneg a → rat.nonneg (-a) → a = 0 :=
num_denom_cases_on' a $ λ n d h,
begin
  have d0 : 0 < (d:ℤ) := int.coe_nat_pos.2 (nat.pos_of_ne_zero h),
  simp [d0, h],
  exact λ h₁ h₂, le_antisymm h₂ h₁
end

protected lemma nonneg_total : rat.nonneg a ∨ rat.nonneg (-a) :=
by cases a with n; exact
or.imp_right neg_nonneg_of_nonpos (le_total 0 n)

instance decidable_nonneg : decidable (rat.nonneg a) :=
by cases a; unfold rat.nonneg; apply_instance

/-- Relation `a ≤ b` on `ℚ` defined as `a ≤ b ↔ rat.nonneg (b - a)`. Use `a ≤ b` instead of
`rat.le a b`. -/
protected def le (a b : ℚ) := rat.nonneg (b - a)

instance : has_le ℚ := ⟨rat.le⟩

instance decidable_le : decidable_rel ((≤) : ℚ → ℚ → Prop)
| a b := show decidable (rat.nonneg (b - a)), by apply_instance

protected theorem le_def {a b c d : ℤ} (b0 : 0 < b) (d0 : 0 < d) :
  a /. b ≤ c /. d ↔ a * d ≤ c * b :=
begin
  show rat.nonneg _ ↔ _,
  rw ← sub_nonneg,
  simp [sub_eq_add_neg, ne_of_gt b0, ne_of_gt d0, mul_pos d0 b0]
end

protected theorem le_refl : a ≤ a :=
show rat.nonneg (a - a), by rw sub_self; exact le_refl (0 : ℤ)

protected theorem le_total : a ≤ b ∨ b ≤ a :=
by have := rat.nonneg_total (b - a); rwa neg_sub at this

protected theorem le_antisymm {a b : ℚ} (hab : a ≤ b) (hba : b ≤ a) : a = b :=
by { have := eq_neg_of_add_eq_zero_left (rat.nonneg_antisymm hba $
 by rwa [← sub_eq_add_neg, neg_sub]), rwa neg_neg at this }

protected theorem le_trans {a b c : ℚ} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
have rat.nonneg (b - a + (c - b)), from rat.nonneg_add hab hbc,
by simpa [sub_eq_add_neg, add_comm, add_left_comm]

instance : linear_order ℚ :=
{ le              := rat.le,
  le_refl         := rat.le_refl,
  le_trans        := @rat.le_trans,
  le_antisymm     := @rat.le_antisymm,
  le_total        := rat.le_total,
  decidable_eq    := by apply_instance,
  decidable_le    := assume a b, rat.decidable_nonneg (b - a) }

/- Extra instances to short-circuit type class resolution -/
instance : has_lt ℚ          := by apply_instance
instance : distrib_lattice ℚ := by apply_instance
instance : lattice ℚ         := by apply_instance
instance : semilattice_inf ℚ := by apply_instance
instance : semilattice_sup ℚ := by apply_instance
instance : has_inf ℚ         := by apply_instance
instance : has_sup ℚ         := by apply_instance
instance : partial_order ℚ   := by apply_instance
instance : preorder ℚ        := by apply_instance

protected lemma le_def' {p q : ℚ} : p ≤ q ↔ p.num * q.denom ≤ q.num * p.denom :=
begin
  rw [←(@num_denom q), ←(@num_denom p)],
  conv_rhs { simp only [num_denom] },
  exact rat.le_def (by exact_mod_cast p.pos) (by exact_mod_cast q.pos)
end

protected lemma lt_def {p q : ℚ} : p < q ↔ p.num * q.denom < q.num * p.denom :=
begin
  rw [lt_iff_le_and_ne, rat.le_def'],
  suffices : p ≠ q ↔ p.num * q.denom ≠ q.num * p.denom, by
  { split; intro h,
    { exact lt_iff_le_and_ne.elim_right ⟨h.left, (this.elim_left h.right)⟩ },
    { have tmp := lt_iff_le_and_ne.elim_left h, exact ⟨tmp.left, this.elim_right tmp.right⟩ }},
  exact (not_iff_not.elim_right eq_iff_mul_eq_mul)
end

theorem nonneg_iff_zero_le {a} : rat.nonneg a ↔ 0 ≤ a :=
show rat.nonneg a ↔ rat.nonneg (a - 0), by simp

theorem num_nonneg_iff_zero_le : ∀ {a : ℚ}, 0 ≤ a.num ↔ 0 ≤ a
| ⟨n, d, h, c⟩ := @nonneg_iff_zero_le ⟨n, d, h, c⟩

protected theorem add_le_add_left {a b c : ℚ} : c + a ≤ c + b ↔ a ≤ b :=
by unfold has_le.le rat.le; rw add_sub_add_left_eq_sub

protected theorem mul_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
by rw ← nonneg_iff_zero_le at ha hb ⊢; exact rat.nonneg_mul ha hb

@[main_declaration]
instance : linear_ordered_field ℚ :=
{ zero_le_one     := dec_trivial,
  add_le_add_left := assume a b ab c, rat.add_le_add_left.2 ab,
  mul_pos         := assume a b ha hb, lt_of_le_of_ne
    (rat.mul_nonneg (le_of_lt ha) (le_of_lt hb))
    (mul_ne_zero (ne_of_lt ha).symm (ne_of_lt hb).symm).symm,
  ..rat.field,
  ..rat.linear_order,
  ..rat.semiring }

#print rat.mk_neg_one_one
#print rat.num_nonneg_iff_zero_le
#print rat.repr
#print rat.div_int_inj
#print rat.semigroup
#print rat.coe_nat_eq_mk
#print rat.has_inf
#print rat.forall
#print rat.exists
#print rat.add_mk
#print rat.mul_num
#print rat.add_num_denom'
#print rat.add_left_cancel_semigroup
#print rat.mul_num_denom
#print rat.eq_iff_mul_eq_mul
#print rat.denom_div_cast_eq_one_iff
#print rat.num_neg_eq_neg_num
#print rat.mk_div_mk_cancel_right
#print rat.num_one
#print rat.nontrivial
#print rat.coe_int_denom
#print rat.pnat_denom_eq_iff_denom_eq
#print rat.num_dvd
#print rat.coe_int_div_eq_mk
#print rat.can_lift
#print rat.coe_pnat_denom
#print rat.denom_zero
#print rat.inv_coe_nat_denom
#print rat.coe_int_div_self
#print rat.mk_num_ne_zero_of_ne_zero
#print rat.ext
#print rat.distrib_lattice
#print rat.mk_pnat_pnat_denom_eq
#print rat.has_to_string
#print rat.le_def
#print rat.le_def'
#print rat.add_semigroup
#print rat.add_denom_dvd
#print rat.mk_div_mk_cancel_left
#print rat.coe_int_eq_mk
#print rat.lt_def
#print rat.coe_int_num
#print rat.mk_zero_one
#print rat.denom_ne_zero
#print rat.num_div_denom
#print rat.has_sup
#print rat.num_ne_zero_of_ne_zero
#print rat.inv_coe_int_denom_of_pos
#print rat.mul_denom_eq_num
#print rat.inhabited
#print rat.denom_eq_one_iff
#print rat.has_repr
#print rat.mk_ne_zero_of_ne_zero
#print rat.num_denom_mk
#print rat.substr_num_denom'
#print rat.coe_nat_div
#print rat.div_num_denom
#print rat.inv_coe_int_denom
#print rat.inv_coe_nat_num
#print rat.mk_pnat_num
#print rat.inv_def'
#print rat.mul_self_num
#print rat.mul_num_denom'
#print rat.mul_self_denom
#print rat.mk_nat_eq
#print rat.add_monoid
#print rat.mk_denom_ne_zero_of_ne_zero
#print rat.inv_coe_nat_num_of_pos
#print rat.comm_semiring
#print rat.coe_int_inj
#print rat.sub_def
#print rat.inv_coe_nat_denom_of_pos
#print rat.ext_iff
#print rat.exists_eq_mul_div_num_and_eq_mul_div_denom
#print rat.zero_iff_num_zero
#print rat.num_div_eq_of_coprime
#print rat.mul_denom_dvd
#print rat.pnat_denom_one
#print rat.monoid
#print rat.mk_pnat_denom_dvd
#print rat.has_lt
#print rat.has_to_format
#print rat.inv_coe_int_num_of_pos
#print rat.inv_coe_int_num
#print rat.comm_semigroup
#print rat.mk_mul_mk_cancel
#print rat.coe_nat_denom
#print rat.denom_neg_eq_denom
#print rat.pnat_denom_zero
#print rat.zero_of_num_zero
#print rat.denom_div_eq_of_coprime
#print rat.mk_neg_denom
#print rat.coe_nat_num
#print rat.coe_int_div
#print rat.inv_mul_cancel
#print rat.mk_eq_div
#print rat.mk_pnat_denom
#print rat.coe_int_num_of_denom_eq_one
#print rat.denom_one
#print rat.denom_mk
#print rat.coe_int_eq_of_int
#print rat.semiring
#print rat.semilattice_sup
#print rat.mul_denom
#print rat.num_mk
#print rat.add_right_cancel_semigroup
#print rat.inv_neg
#print rat.num_zero
#print rat.add_num_denom
#print rat.denom_dvd
#print rat.comm_monoid
#print rat.coe_nat_div_self

#list_unused_decls ["src/data/rat/defs.lean"]

/- Extra instances to short-circuit type class resolution -/
instance : linear_ordered_comm_ring ℚ       := by apply_instance
instance : linear_ordered_ring ℚ            := by apply_instance
instance : ordered_ring ℚ                   := by apply_instance
instance : linear_ordered_semiring ℚ        := by apply_instance
instance : ordered_semiring ℚ               := by apply_instance
instance : linear_ordered_add_comm_group ℚ  := by apply_instance
instance : ordered_add_comm_group ℚ         := by apply_instance
instance : ordered_cancel_add_comm_monoid ℚ := by apply_instance
instance : ordered_add_comm_monoid ℚ        := by apply_instance

attribute [irreducible] rat.le

theorem num_pos_iff_pos {a : ℚ} : 0 < a.num ↔ 0 < a :=
lt_iff_lt_of_le_iff_le $
by simpa [(by cases a; refl : (-a).num = -a.num)]
   using @num_nonneg_iff_zero_le (-a)

lemma div_lt_div_iff_mul_lt_mul {a b c d : ℤ} (b_pos : 0 < b) (d_pos : 0 < d) :
  (a : ℚ) / b < c / d ↔ a * d < c * b :=
begin
  simp only [lt_iff_le_not_le],
  apply and_congr,
  { simp [div_num_denom, (rat.le_def b_pos d_pos)] },
  { apply not_iff_not_of_iff, simp [div_num_denom, (rat.le_def d_pos b_pos)] }
end

lemma lt_one_iff_num_lt_denom {q : ℚ} : q < 1 ↔ q.num < q.denom :=
by simp [rat.lt_def]

theorem abs_def (q : ℚ) : |q| = q.num.nat_abs /. q.denom :=
begin
  cases le_total q 0 with hq hq,
  { rw [abs_of_nonpos hq],
    rw [←(@num_denom q), ← mk_zero_one, rat.le_def (int.coe_nat_pos.2 q.pos) zero_lt_one,
        mul_one, zero_mul] at hq,
    rw [int.of_nat_nat_abs_of_nonpos hq, ← neg_def, num_denom] },
  { rw [abs_of_nonneg hq],
    rw [←(@num_denom q), ← mk_zero_one, rat.le_def zero_lt_one (int.coe_nat_pos.2 q.pos),
        mul_one, zero_mul] at hq,
    rw [int.nat_abs_of_nonneg hq, num_denom] }
end

end rat

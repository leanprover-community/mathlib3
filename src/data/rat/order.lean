/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.rat.basic
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

protected def nonneg : ℚ → Prop
| ⟨n, d, h, c⟩ := n ≥ 0

@[simp] theorem mk_nonneg (a : ℤ) {b : ℤ} (h : b > 0) : (a /. b).nonneg ↔ a ≥ 0 :=
begin
  generalize ha : a /. b = x, cases x with n₁ d₁ h₁ c₁, rw num_denom' at ha,
  simp [rat.nonneg],
  have d0 := int.coe_nat_lt.2 h₁,
  have := (mk_eq (ne_of_gt h) (ne_of_gt d0)).1 ha,
  constructor; intro h₂,
  { apply nonneg_of_mul_nonneg_right _ d0,
    rw this, exact mul_nonneg h₂ (le_of_lt h) },
  { apply nonneg_of_mul_nonneg_right _ h,
    rw ← this, exact mul_nonneg h₂ (int.coe_zero_le _) },
end

protected def nonneg_add {a b} : rat.nonneg a → rat.nonneg b → rat.nonneg (a + b) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
begin
  have d₁0 : (d₁:ℤ) > 0 := int.coe_nat_pos.2 (nat.pos_of_ne_zero h₁),
  have d₂0 : (d₂:ℤ) > 0 := int.coe_nat_pos.2 (nat.pos_of_ne_zero h₂),
  simp [d₁0, d₂0, h₁, h₂, mul_pos d₁0 d₂0],
  intros n₁0 n₂0,
  apply add_nonneg; apply mul_nonneg; {assumption <|> apply int.coe_zero_le}
end

protected def nonneg_mul {a b} : rat.nonneg a → rat.nonneg b → rat.nonneg (a * b) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
begin
  have d₁0 : (d₁:ℤ) > 0 := int.coe_nat_pos.2 (nat.pos_of_ne_zero h₁),
  have d₂0 : (d₂:ℤ) > 0 := int.coe_nat_pos.2 (nat.pos_of_ne_zero h₂),
  simp [d₁0, d₂0, h₁, h₂, mul_pos d₁0 d₂0],
  exact mul_nonneg
end

protected def nonneg_antisymm {a} : rat.nonneg a → rat.nonneg (-a) → a = 0 :=
num_denom_cases_on' a $ λ n d h,
begin
  have d0 : (d:ℤ) > 0 := int.coe_nat_pos.2 (nat.pos_of_ne_zero h),
  simp [d0, h],
  exact λ h₁ h₂, le_antisymm (nonpos_of_neg_nonneg h₂) h₁
end

protected def nonneg_total : rat.nonneg a ∨ rat.nonneg (-a) :=
by cases a with n; exact
or.imp_right neg_nonneg_of_nonpos (le_total 0 n)

instance decidable_nonneg : decidable (rat.nonneg a) :=
by cases a; unfold rat.nonneg; apply_instance

protected def le (a b : ℚ) := rat.nonneg (b - a)

instance : has_le ℚ := ⟨rat.le⟩

instance decidable_le : decidable_rel ((≤) : ℚ → ℚ → Prop)
| a b := show decidable (rat.nonneg (b - a)), by apply_instance

protected theorem le_def {a b c d : ℤ} (b0 : b > 0) (d0 : d > 0) :
  a /. b ≤ c /. d ↔ a * d ≤ c * b :=
show rat.nonneg _ ↔ _,
by simpa [ne_of_gt b0, ne_of_gt d0, mul_pos b0 d0, mul_comm]
   using @sub_nonneg _ _ (b * c) (a * d)

protected theorem le_refl : a ≤ a :=
show rat.nonneg (a - a), by rw sub_self; exact le_refl (0 : ℤ)

protected theorem le_total : a ≤ b ∨ b ≤ a :=
by have := rat.nonneg_total (b - a); rwa neg_sub at this

protected theorem le_antisymm {a b : ℚ} (hab : a ≤ b) (hba : b ≤ a) : a = b :=
by have := eq_neg_of_add_eq_zero (rat.nonneg_antisymm hba $ by simpa);
   rwa neg_neg at this

protected theorem le_trans {a b c : ℚ} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
have rat.nonneg (b - a + (c - b)), from rat.nonneg_add hab hbc,
by simpa

instance : decidable_linear_order ℚ :=
{ le              := rat.le,
  le_refl         := rat.le_refl,
  le_trans        := @rat.le_trans,
  le_antisymm     := @rat.le_antisymm,
  le_total        := rat.le_total,
  decidable_eq    := by apply_instance,
  decidable_le    := assume a b, rat.decidable_nonneg (b - a) }

/- Extra instances to short-circuit type class resolution -/
instance : has_lt ℚ                  := by apply_instance
instance : lattice.distrib_lattice ℚ := by apply_instance
instance : lattice.lattice ℚ         := by apply_instance
instance : lattice.semilattice_inf ℚ := by apply_instance
instance : lattice.semilattice_sup ℚ := by apply_instance
instance : lattice.has_inf ℚ         := by apply_instance
instance : lattice.has_sup ℚ         := by apply_instance
instance : linear_order ℚ            := by apply_instance
instance : partial_order ℚ           := by apply_instance
instance : preorder ℚ                := by apply_instance

protected lemma le_def' {p q : ℚ} (p_pos : 0 < p) (q_pos : 0 < q) :
  p ≤ q ↔ p.num * q.denom ≤ q.num * p.denom :=
begin
  rw [←(@num_denom q), ←(@num_denom p)],
  conv_rhs { simp only [num_denom] },
  exact rat.le_def (by exact_mod_cast p.pos) (by exact_mod_cast q.pos)
end

protected lemma lt_def {p q : ℚ} (p_pos : 0 < p) (q_pos : 0 < q) :
  p < q ↔ p.num * q.denom < q.num * p.denom :=
begin
  rw [lt_iff_le_and_ne, (rat.le_def' p_pos q_pos)],
  suffices : p ≠ q ↔ p.num * q.denom ≠ q.num * p.denom, by {
    split; intro h,
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

instance : discrete_linear_ordered_field ℚ :=
{ zero_lt_one     := dec_trivial,
  add_le_add_left := assume a b ab c, rat.add_le_add_left.2 ab,
  add_lt_add_left := assume a b ab c, lt_of_not_ge $ λ ba,
    not_le_of_lt ab $ rat.add_le_add_left.1 ba,
  mul_nonneg      := @rat.mul_nonneg,
  mul_pos         := assume a b ha hb, lt_of_le_of_ne
    (rat.mul_nonneg (le_of_lt ha) (le_of_lt hb))
    (mul_ne_zero (ne_of_lt ha).symm (ne_of_lt hb).symm).symm,
  ..rat.discrete_field, ..rat.decidable_linear_order }

/- Extra instances to short-circuit type class resolution -/
instance : linear_ordered_field ℚ                := by apply_instance
instance : decidable_linear_ordered_comm_ring ℚ  := by apply_instance
instance : linear_ordered_comm_ring ℚ            := by apply_instance
instance : linear_ordered_ring ℚ                 := by apply_instance
instance : ordered_ring ℚ                        := by apply_instance
instance : decidable_linear_ordered_semiring ℚ   := by apply_instance
instance : linear_ordered_semiring ℚ             := by apply_instance
instance : ordered_semiring ℚ                    := by apply_instance
instance : decidable_linear_ordered_comm_group ℚ := by apply_instance
instance : ordered_comm_group ℚ                  := by apply_instance
instance : ordered_cancel_comm_monoid ℚ          := by apply_instance
instance : ordered_comm_monoid ℚ                 := by apply_instance

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
begin
  cases decidable.em (0 < q) with q_pos q_nonpos,
  { simp [(rat.lt_def q_pos zero_lt_one)] },
  { replace q_nonpos : q ≤ 0, from not_lt.elim_left q_nonpos,
    have : q.num < q.denom, by
    { have : ¬0 < q.num ↔ ¬0 < q, from not_iff_not.elim_right num_pos_iff_pos,
      simp only [not_lt] at this,
      exact lt_of_le_of_lt (this.elim_right q_nonpos) (by exact_mod_cast q.pos) },
    simp only [this, (lt_of_le_of_lt q_nonpos zero_lt_one)] }
end

theorem abs_def (q : ℚ) : abs q = q.num.nat_abs /. q.denom :=
begin
  have hz : (0:ℚ) = 0 /. 1 := rfl,
  cases le_total q 0 with hq hq,
  { rw [abs_of_nonpos hq],
    rw [←(@num_denom q), hz, rat.le_def (int.coe_nat_pos.2 q.pos) zero_lt_one,
        mul_one, zero_mul] at hq,
    rw [int.of_nat_nat_abs_of_nonpos hq, ← neg_def, num_denom] },
  { rw [abs_of_nonneg hq],
    rw [←(@num_denom q), hz, rat.le_def zero_lt_one (int.coe_nat_pos.2 q.pos),
        mul_one, zero_mul] at hq,
    rw [int.nat_abs_of_nonneg hq, num_denom] }
end

section sqrt

def sqrt (q : ℚ) : ℚ := rat.mk (int.sqrt q.num) (nat.sqrt q.denom)

theorem sqrt_eq (q : ℚ) : rat.sqrt (q*q) = abs q :=
by rw [sqrt, mul_self_num, mul_self_denom, int.sqrt_eq, nat.sqrt_eq, abs_def]

theorem exists_mul_self (x : ℚ) : (∃ q, q * q = x) ↔ rat.sqrt x * rat.sqrt x = x :=
⟨λ ⟨n, hn⟩, by rw [← hn, sqrt_eq, abs_mul_abs_self],
λ h, ⟨rat.sqrt x, h⟩⟩

theorem sqrt_nonneg (q : ℚ) : 0 ≤ rat.sqrt q :=
nonneg_iff_zero_le.1 $ (mk_nonneg _ $ int.coe_nat_pos.2 $
nat.pos_of_ne_zero $ λ H, nat.pos_iff_ne_zero.1 q.pos $ nat.sqrt_eq_zero.1 H).2 trivial

end sqrt
end rat

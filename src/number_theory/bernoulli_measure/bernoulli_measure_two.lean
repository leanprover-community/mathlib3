/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.bernoulli_measure.bernoulli_measure_one
import number_theory.zmod_properties

/-!
# Bernoulli measure and the p-adic L-function

This file defines the Bernoulli distribution on `zmod d × ℤ_[p]`. One of the main theorems is that
this p-adic distribution is indeed a p-adic measure. As a consequence, we are also able to define
the p-adic L-function in terms of a p-adic integral.

## Main definitions
 * `bernoulli_measure_of_measure`
 * `p_adic_L_function`

## Implementation notes
TODO (optional)

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

local attribute [instance] zmod.topological_space

variables {p : ℕ} [fact p.prime] {d : ℕ}
variables (R : Type*) [normed_comm_ring R]

open eventually_constant_seq

namespace padic_int

/-- Given `a ∈ zmod (d * p^n)`, and `n < m`, the set of all `b ∈ zmod (d * p^m)` such that
  `b = a mod (d * p^n)`. -/
def equi_class {n : ℕ} (m : ℕ) (a : zmod (d * p^n)) :=
 {b : zmod (d * p^m) | (b : zmod (d * p^n)) = a}
-- change def to a + k*dp^m
-- need h to be n ≤ m, not n < m for g_char_fn

lemma mem_equi_class {n m : ℕ} (a : zmod (d * p^n)) (b : zmod (d * p^m)) :
  b ∈ equi_class m a ↔ (b : zmod (d * p^n)) = a := ⟨λ hb, hb, λ hb, hb⟩

variable [fact (0 < d)]

lemma equi_class_some {n : ℕ} (x : zmod (d * p^n)) (y : equi_class n.succ x) : ∃ k : ℕ, k < p ∧
  (y : zmod (d * p^n.succ)).val = x.val + k * d * p^n :=
begin
  conv { congr, funext, conv { congr, skip, to_rhs,
    rw ←((@mem_equi_class p _ d n n.succ x y).1 (y.prop)), }, },
  rw [← zmod.nat_cast_val (y : zmod (d * p^n.succ)), zmod.val_nat_cast],
  refine ⟨(y : zmod (d * p^n.succ)).val / (d * p^n), nat.div_lt_of_lt_mul _, _⟩,
  { rw [nat.mul_assoc, ←pow_succ'], apply zmod.val_lt (y : zmod (d * p^n.succ)), },
  { rw [mul_assoc, nat.mod_add_div' (y : zmod (d * p^n.succ)).val (d * p^n)], },
end

/-- Giving an equivalence between `equi_class` and `fin p`. -/
def equi_iso_fin (m : ℕ) (a : zmod (d * p^m)) : equi_class m.succ a ≃ fin p :=
{ to_fun := λ y, ⟨((y.val).val - a.val) / (d * p^m), nat.div_lt_of_lt_mul begin
    rw [mul_assoc, ←pow_succ'],
    exact lt_of_le_of_lt (nat.sub_le (y.val).val a.val) (zmod.val_lt y.val), end⟩,
  inv_fun := λ k, ⟨(a.val + k * d * p^m : ℕ), begin
    have g : (d * (p^m)) ∣ (d * p^(m.succ)) := mul_dvd_mul dvd_rfl (pow_dvd_pow p (nat.le_succ _)),
    rw [mem_equi_class, zmod.cast_nat_cast g _, nat.cast_add, zmod.nat_cast_zmod_val, mul_assoc,
      nat.cast_mul, zmod.nat_cast_self, mul_zero, add_zero],
    refine zmod.char_p _, end⟩,
  left_inv := λ x, begin
    rw subtype.ext_iff_val, simp only [fin.coe_mk, subtype.val_eq_coe, _root_.coe_coe],
    rw mul_assoc,
    obtain ⟨k, hk, h⟩ := equi_class_some a x,
    rw nat.div_mul_cancel,
    { rw [← nat.add_sub_assoc _ _, nat.add_sub_cancel_left],
      { rw zmod.nat_cast_val _, norm_cast, apply_instance, },
      { rw h, apply nat.le_add_right, }, },
    { rw [h, nat.add_sub_cancel_left, mul_assoc], simp, }, end,
  right_inv := λ x, begin
    simp only [nat.cast_pow],
    rw subtype.ext_iff_val,
    simp only [fin.coe_mk, subtype.val_eq_coe, _root_.coe_coe],
    apply nat.div_eq_of_eq_mul_left (fact.out _) (tsub_eq_of_eq_add _),
    { apply_instance, },
    rw [mul_assoc, zmod.val_nat_cast, nat.mod_eq_of_lt],
    rw add_comm,
    have h2 : ↑x * (d * p ^ m) ≤ (d * p ^ m) * (p - 1),
    { rw mul_comm, apply nat.mul_le_mul_left,
      rw [←nat.lt_succ_iff, nat.succ_eq_add_one, nat.sub_add_cancel], apply x.2,
      { apply le_of_lt (fact_iff.1 (nat.prime.one_lt' p)), }, },
    convert add_lt_add_of_lt_of_le (zmod.val_lt a) h2,
    ring_nf, rw nat.sub_add_cancel,
    { rw ←pow_succ, },
    { apply le_of_lt (fact_iff.1 (nat.prime.one_lt' p)), }, end}

noncomputable instance {n m : ℕ} (a : zmod (d * p^n)) : fintype (equi_class m a) :=
set.finite.fintype (set.finite.subset (set.univ_finite_iff_nonempty_fintype.2
  (nonempty.intro infer_instance)) (set.subset_univ _))

end padic_int

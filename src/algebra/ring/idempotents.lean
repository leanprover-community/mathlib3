/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import order.basic
import algebra.group_power.basic
import algebra.ring.defs
import tactic.nth_rewrite

/-!
# Idempotents

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines idempotents for an arbitary multiplication and proves some basic results,
including:

* `is_idempotent_elem.mul_of_commute`: In a semigroup, the product of two commuting idempotents is
  an idempotent;
* `is_idempotent_elem.one_sub_iff`: In a (non-associative) ring, `p` is an idempotent if and only if
  `1-p` is an idempotent.
* `is_idempotent_elem.pow_succ_eq`: In a monoid `p ^ (n+1) = p` for `p` an idempotent and `n` a
  natural number.

## Tags

projection, idempotent
-/

variables {M N S M₀ M₁ R G G₀ : Type*}
variables [has_mul M] [monoid N] [semigroup S] [mul_zero_class M₀] [mul_one_class M₁]
  [non_assoc_ring R] [group G] [cancel_monoid_with_zero G₀]

/--
An element `p` is said to be idempotent if `p * p = p`
-/
def is_idempotent_elem (p : M) : Prop := p * p = p

namespace is_idempotent_elem

lemma of_is_idempotent [is_idempotent M (*)] (a : M) : is_idempotent_elem a :=
is_idempotent.idempotent a

lemma eq {p : M} (h : is_idempotent_elem p) : p * p = p := h

lemma mul_of_commute {p q : S} (h : commute p q) (h₁ : is_idempotent_elem p)
  (h₂ : is_idempotent_elem q) : is_idempotent_elem (p * q)  :=
by rw [is_idempotent_elem, mul_assoc, ← mul_assoc q, ← h.eq, mul_assoc p, h₂.eq, ← mul_assoc, h₁.eq]

lemma zero : is_idempotent_elem (0 : M₀) := mul_zero _

lemma one : is_idempotent_elem (1 : M₁) := mul_one _

lemma one_sub {p : R} (h : is_idempotent_elem p) : is_idempotent_elem (1 - p) :=
by rw [is_idempotent_elem, mul_sub, mul_one, sub_mul, one_mul, h.eq, sub_self, sub_zero]

@[simp] lemma one_sub_iff {p : R} : is_idempotent_elem (1 - p) ↔ is_idempotent_elem p :=
⟨ λ h, sub_sub_cancel 1 p ▸ h.one_sub, is_idempotent_elem.one_sub ⟩

lemma pow {p : N} (n : ℕ) (h : is_idempotent_elem p) : is_idempotent_elem (p ^ n) :=
nat.rec_on n ((pow_zero p).symm ▸ one) (λ n ih, show p ^ n.succ * p ^ n.succ = p ^ n.succ,
  by { nth_rewrite 2 ←h.eq, rw [←sq, ←sq, ←pow_mul, ←pow_mul'] })

lemma pow_succ_eq {p : N} (n : ℕ) (h : is_idempotent_elem p) : p ^ (n + 1) = p :=
nat.rec_on n ((nat.zero_add 1).symm ▸ pow_one p) (λ n ih, by rw [pow_succ, ih, h.eq])

@[simp] lemma iff_eq_one {p : G} : is_idempotent_elem p ↔ p = 1 :=
iff.intro (λ h, mul_left_cancel ((mul_one p).symm ▸ h.eq : p * p = p * 1)) (λ h, h.symm ▸ one)

@[simp] lemma iff_eq_zero_or_one {p : G₀}  : is_idempotent_elem p ↔ p = 0 ∨ p = 1 :=
begin
  refine iff.intro
    (λ h, or_iff_not_imp_left.mpr (λ hp, _))
    (λ h, h.elim (λ hp, hp.symm ▸ zero) (λ hp, hp.symm ▸ one)),
  exact mul_left_cancel₀ hp (h.trans (mul_one p).symm)
end

/-! ### Instances on `subtype is_idempotent_elem` -/
section instances

instance : has_zero { p : M₀ // is_idempotent_elem p } := { zero := ⟨ 0, zero ⟩ }

@[simp] lemma coe_zero : ↑(0 : {p : M₀ // is_idempotent_elem p}) = (0 : M₀) := rfl

instance : has_one { p : M₁ // is_idempotent_elem p } := { one := ⟨ 1, one ⟩ }

@[simp] lemma coe_one : ↑(1 : { p : M₁ // is_idempotent_elem p }) = (1 : M₁) := rfl

instance : has_compl { p : R // is_idempotent_elem p } := ⟨λ p, ⟨1 - p, p.prop.one_sub⟩⟩

@[simp] lemma coe_compl (p : { p : R // is_idempotent_elem p }) : ↑(pᶜ) = (1 : R) - ↑p := rfl

@[simp] lemma compl_compl (p : {p : R // is_idempotent_elem p}) : pᶜᶜ = p :=
subtype.ext $ sub_sub_cancel _ _

@[simp] lemma zero_compl : (0 : {p : R // is_idempotent_elem p})ᶜ = 1 := subtype.ext $ sub_zero _

@[simp] lemma one_compl : (1 : {p : R // is_idempotent_elem p})ᶜ = 0 := subtype.ext $ sub_self _

end instances

end is_idempotent_elem

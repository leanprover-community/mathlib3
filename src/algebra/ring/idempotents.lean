/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import algebra.ring.basic

/-!
# Idempotents

This file defines idempotents for an arbitary multiplication and proves some basic results:

* In a semigroup, the product of two commuting idempotents is an idempotent;
* In a (non-associative) ring, p is an idempotent if and only if 1-p is an idempotent.

## Tags

projection, idempotent
-/

variables {M : Type*} [has_mul M]

/--
An element `p` is said to be idempotent if `p * p = p`
-/
def is_idempotent_elem (p : M) : Prop := p * p = p

lemma all [is_idempotent M (*)] (a : M) : is_idempotent_elem a :=
begin
  unfold is_idempotent_elem,
  exact is_idempotent.idempotent a,
end

namespace is_idempotent_elem

lemma eq {p : M} (h : is_idempotent_elem p) : p * p = p := h

variables {S : Type*} [semigroup S]

lemma mul_of_commute {p q : S} (h : commute p q) (h₁ : is_idempotent_elem p)
  (h₂ : is_idempotent_elem q) : is_idempotent_elem (p * q)  :=
begin
  rw [is_idempotent_elem, mul_assoc, ← mul_assoc q, ←h.eq, mul_assoc p, h₂.eq, ← mul_assoc, h₁.eq],
end

variables {M₀ : Type*} [mul_zero_class M₀]

lemma zero : is_idempotent_elem (0 : M₀) := by rw [is_idempotent_elem, mul_zero]

instance : has_zero { p : M₀ // is_idempotent_elem p } := {
  zero := ⟨ 0, zero ⟩
}

variables {M₁ : Type*} [mul_one_class M₁]

lemma one : is_idempotent_elem (1 : M₁) := by rw [is_idempotent_elem, mul_one]

instance : has_one { p : M₁ // is_idempotent_elem p } := {
  one := ⟨ 1, one ⟩
}

variables {R : Type*} [non_assoc_ring R]

lemma one_sub {p : R} (h : is_idempotent_elem p) : is_idempotent_elem (1 - p) :=
begin
  rw is_idempotent_elem at h,
  rw [is_idempotent_elem, mul_sub_left_distrib, mul_one, sub_mul, one_mul, h, sub_self, sub_zero],
end

@[simp] lemma one_sub_iff {p : R} : is_idempotent_elem (1 - p) ↔ is_idempotent_elem p :=
⟨ λ h, sub_sub_cancel 1 p ▸ h.one_sub, is_idempotent_elem.one_sub ⟩

instance : has_compl { p : R // is_idempotent_elem p } :=
⟨λ P, ⟨1 - P, P.prop.one_sub⟩⟩

end is_idempotent_elem

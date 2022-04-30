/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import algebra.ring.basic

/-!
# Projections

This file defines projections for an arbitary multiplication and proves some basic results:

* In a semigroup, the product of two commuting projections is a projection;
* In a (non-associative) ring, p is a projection if and only if 1-p is a projection.

## Implementation notes

A better name would probably be `is_idempotent`, but that is already used in a different sense in
Lean's internal library.

## Tags

projection, idempotent
-/

variables {M : Type*} [has_mul M]

def is_projection (x : M) : Prop := x*x = x

lemma projection_def {P : M} (h : is_projection P) : P*P = P := h

namespace is_projection

variables {S : Type*} [semigroup S]

lemma mul_of_commute {P Q : S} (h : commute P Q) (h₁ : is_projection P) (h₂ : is_projection Q) :
  is_projection (P * Q)  :=
begin
  rw is_projection at h₁,
  rw is_projection at h₂,
  rw [commute, semiconj_by] at h,
  rw [is_projection, mul_assoc, ← mul_assoc Q, ←h, mul_assoc P, h₂, ← mul_assoc, h₁],
end

variables {R : Type*} [non_assoc_ring R]

lemma complement {P : R} (h : is_projection P) : is_projection (1 - P) :=
begin
  rw is_projection at h,
  rw [is_projection, mul_sub_left_distrib, mul_one, sub_mul, one_mul, h, sub_self, sub_zero],
end

lemma complement_iff {P : R} : is_projection P ↔ is_projection (1 - P) :=
⟨ is_projection.complement , λ h, sub_sub_cancel 1 P ▸ h.complement⟩

instance : has_compl (subtype (is_projection  : R → Prop)) :=
⟨λ P, ⟨1 - P, P.prop.complement⟩⟩

end is_projection

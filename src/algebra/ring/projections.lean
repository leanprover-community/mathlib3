/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import algebra.ring.basic
import algebra.group_power.basic

/-!
# Projections

This file defines projections in a monoid and the complement of a projection in a ring.

## Tags

projection, idempotent
-/

variables {M : Type*} [monoid M]

def is_projection (x : M) : Prop := x^2 = x

lemma projection_def {P : M} (h : is_projection P) : P^2 = P := by exact h

namespace is_projection

lemma mul_of_commute {P Q : M} (h : commute P Q) (h₁ : is_projection P) (h₂ : is_projection Q) :
  is_projection (P * Q)  :=
begin
  rw is_projection at h₁,
  rw is_projection at h₂,
  rw [commute, semiconj_by] at h,
  rw [is_projection, sq, mul_assoc, ← mul_assoc Q, ←h, mul_assoc P, ← sq, h₂, ← mul_assoc, ← sq,
    h₁],
end

variables {R : Type*} [ring R]

lemma complement {P : R} (h : is_projection P) : is_projection (1 - P) :=
begin
  rw [is_projection, sq] at h,
  rw [is_projection, sq, mul_sub_left_distrib, mul_one, sub_mul, one_mul, h, sub_self, sub_zero],
end


lemma complement_iff {P : R} : is_projection P ↔ is_projection (1 - P) :=
⟨ is_projection.complement , λ h, sub_sub_cancel 1 P ▸ h.complement⟩

instance : has_compl (subtype (is_projection  : R → Prop)) :=
⟨λ P, ⟨1 - P, P.prop.complement⟩⟩

end is_projection

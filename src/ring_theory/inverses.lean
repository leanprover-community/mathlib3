/-
Copyright (c) 2022 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
import algebra.ring.basic
import tactic.noncomm_ring
/-!
# Some facts about inverses in a ring

This file gives some facts about left and right invertible elements in a noncommutative ring.
Note that all the statements are trivial for commutative rings.
-/

universe u
variables {R : Type u} {a : R} {b : R} [ring R]

lemma has_left_inv.one_add_mul_swap
  (h : has_left_inv (1 + a * b)) : has_left_inv (1 + b * a) :=
begin
  obtain ⟨u, hu⟩ := h,
  existsi 1 - b * u * a,
  calc (1 - b * u * a) * (1 + b * a)
        = 1 + b * a - b * (u * (1 + a * b)) * a : by noncomm_ring
    ... = 1 : by rw [hu, mul_one, add_sub_cancel],
end

lemma has_right_inv.one_add_mul_swap
  (h : has_right_inv (1 + a * b)) : has_right_inv (1 + b * a) :=
begin
  obtain ⟨u, hu⟩ := h,
  existsi 1 - b * u * a,
  calc (1 + b * a) * (1 - b * u * a)
        = 1 + b * a - b * ((1 + a * b ) * u) * a : by noncomm_ring
    ... = 1 : by rw [hu, mul_one, add_sub_cancel],
end

lemma is_unit.one_add_mul_swap
  (h : is_unit (1 + a * b)) : is_unit (1 + b * a) :=
begin
  rw is_unit_iff_has_left_inv_right_inv at *,
  obtain ⟨h₁, h₂⟩ := h,
  exact ⟨h₁.one_add_mul_swap, h₂.one_add_mul_swap⟩,
end

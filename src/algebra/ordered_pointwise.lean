/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import algebra.ordered_field
import algebra.algebra.basic

/-!
# Pointwise operations on ordered algebraic objects

This file contains lemmas about the effect of pointwise operations on sets with an order structure.

-/

open_locale pointwise

namespace linear_ordered_field

variables {K : Type*} [linear_ordered_field K] {a b r : K} (hr : 0 < r)
open set

include hr

lemma smul_Ioo : r • Ioo a b = Ioo (r • a) (r • b) :=
begin
  ext x,
  simp only [mem_smul_set, algebra.id.smul_eq_mul, mem_Ioo],
  split,
  { rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩, split,
    exact (mul_lt_mul_left hr).mpr a_h_left_left,
    exact (mul_lt_mul_left hr).mpr a_h_left_right, },
  { rintro ⟨a_left, a_right⟩,
    use x / r,
    refine ⟨⟨(lt_div_iff' hr).mpr a_left, (div_lt_iff' hr).mpr a_right⟩, _⟩,
    rw mul_div_cancel' _ (ne_of_gt hr), }
end

lemma smul_Icc : r • Icc a b = Icc (r • a) (r • b) :=
begin
  ext x,
  simp only [mem_smul_set, algebra.id.smul_eq_mul, mem_Icc],
  split,
  { rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩, split,
    exact (mul_le_mul_left hr).mpr a_h_left_left,
    exact (mul_le_mul_left hr).mpr a_h_left_right, },
  { rintro ⟨a_left, a_right⟩,
    use x / r,
    refine ⟨⟨(le_div_iff' hr).mpr a_left, (div_le_iff' hr).mpr a_right⟩, _⟩,
    rw mul_div_cancel' _ (ne_of_gt hr), }
end

lemma smul_Ico : r • Ico a b = Ico (r • a) (r • b) :=
begin
  ext x,
  simp only [mem_smul_set, algebra.id.smul_eq_mul, mem_Ico],
  split,
  { rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩, split,
    exact (mul_le_mul_left hr).mpr a_h_left_left,
    exact (mul_lt_mul_left hr).mpr a_h_left_right, },
  { rintro ⟨a_left, a_right⟩,
    use x / r,
    refine ⟨⟨(le_div_iff' hr).mpr a_left, (div_lt_iff' hr).mpr a_right⟩, _⟩,
    rw mul_div_cancel' _ (ne_of_gt hr), }
end

lemma smul_Ioc : r • Ioc a b = Ioc (r • a) (r • b) :=
begin
  ext x,
  simp only [mem_smul_set, algebra.id.smul_eq_mul, mem_Ioc],
  split,
  { rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩, split,
    exact (mul_lt_mul_left hr).mpr a_h_left_left,
    exact (mul_le_mul_left hr).mpr a_h_left_right, },
  { rintro ⟨a_left, a_right⟩,
    use x / r,
    refine ⟨⟨(lt_div_iff' hr).mpr a_left, (div_le_iff' hr).mpr a_right⟩, _⟩,
    rw mul_div_cancel' _ (ne_of_gt hr), }
end

lemma smul_Ioi : r • Ioi a = Ioi (r • a) :=
begin
  ext x,
  simp only [mem_smul_set, algebra.id.smul_eq_mul, mem_Ioi],
  split,
  { rintro ⟨a_w, a_h_left, rfl⟩,
    exact (mul_lt_mul_left hr).mpr a_h_left, },
  { rintro h,
    use x / r,
    split,
    exact (lt_div_iff' hr).mpr h,
    exact mul_div_cancel' _ (ne_of_gt hr), }
end

lemma smul_Iio : r • Iio a = Iio (r • a) :=
begin
  ext x,
  simp only [mem_smul_set, algebra.id.smul_eq_mul, mem_Iio],
  split,
  { rintro ⟨a_w, a_h_left, rfl⟩,
    exact (mul_lt_mul_left hr).mpr a_h_left, },
  { rintro h,
    use x / r,
    split,
    exact (div_lt_iff' hr).mpr h,
    exact mul_div_cancel' _ (ne_of_gt hr), }
end

lemma smul_Ici : r • Ici a = Ici (r • a) :=
begin
  ext x,
  simp only [mem_smul_set, algebra.id.smul_eq_mul, mem_Ioi],
  split,
  { rintro ⟨a_w, a_h_left, rfl⟩,
    exact (mul_le_mul_left hr).mpr a_h_left, },
  { rintro h,
    use x / r,
    split,
    exact (le_div_iff' hr).mpr h,
    exact mul_div_cancel' _ (ne_of_gt hr), }
end

lemma smul_Iic : r • Iic a = Iic (r • a) :=
begin
  ext x,
  simp only [mem_smul_set, algebra.id.smul_eq_mul, mem_Iio],
  split,
  { rintro ⟨a_w, a_h_left, rfl⟩,
    exact (mul_le_mul_left hr).mpr a_h_left, },
  { rintro h,
    use x / r,
    split,
    exact (div_le_iff' hr).mpr h,
    exact mul_div_cancel' _ (ne_of_gt hr), }
end
end linear_ordered_field

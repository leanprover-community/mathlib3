/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Topology of the complex numbers.
-/
import data.complex analysis.metric_space

noncomputable theory

instance : metric_space ℂ :=
{ dist               := λx y, (x - y).abs,
  dist_self          := by simp [abs_zero],
  eq_of_dist_eq_zero := by simp [add_neg_eq_zero],
  dist_comm          := assume x y, by rw [complex.abs_sub],
  dist_triangle      := assume x y z, complex.abs_sub_le _ _ _ }

theorem complex.dist_eq (x y : ℂ) : dist x y = (x - y).abs := rfl

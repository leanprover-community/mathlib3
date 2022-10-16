/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.specific_functions

/-!
# Arbitrary support

We show that any open set is the support of a smooth function taking values in `[0, 1]`
-/

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]

theorem is_open.exists_smooth_support_eq {s : set E} (hs : is_open s) :
  ∃ (f : E → ℝ), f.support = s ∧ cont_diff ℝ ⊤ f ∧ set.range f ⊆ set.Icc 0 1 :=
begin

end

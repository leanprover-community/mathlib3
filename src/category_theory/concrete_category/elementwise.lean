/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import tactic.elementwise
import category_theory.limits.has_limits
import category_theory.limits.shapes.kernels

/-!
In this file we provide various simp lemmas in its elementwise form via `tactic.elementwise`.
-/

open category_theory category_theory.limits

attribute [elementwise]
  cone.w limit.lift_π limit.w cocone.w colimit.ι_desc colimit.w
  kernel.lift_ι cokernel.π_desc
  kernel.condition cokernel.condition
  -- Note that the elementwise forms of `iso.hom_inv_id` and `iso.inv_hom_id` are already
  -- provided as `category_theory.coe_hom_inv_id` and `category_theory.coe_inv_hom_id`.
  is_iso.hom_inv_id is_iso.inv_hom_id

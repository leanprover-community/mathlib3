/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/

import analysis.convex.uniform
import analysis.inner_product_space.basic

/-!
# Uniform convex space structure on real inner product spaces

## Tags

inner product space, uniform convex space
-/

variables {F : Type*} [inner_product_space ℝ F]
open real

@[priority 100] -- See note [lower instance priority]
instance inner_product_space.to_uniform_convex_space : uniform_convex_space F :=
⟨λ ε hε, begin
  refine ⟨2 - sqrt (4 - ε^2), sub_pos_of_lt $ (sqrt_lt' zero_lt_two).2 _, λ x hx y hy hxy, _⟩,
  { norm_num,
    exact pow_pos hε _ },
  rw sub_sub_cancel,
  refine le_sqrt_of_sq_le _,
  rw [sq, eq_sub_iff_add_eq.2 (parallelogram_law_with_norm x y), ←sq (‖x - y‖), hx, hy],
  norm_num,
  exact pow_le_pow_of_le_left hε.le hxy _,
end⟩

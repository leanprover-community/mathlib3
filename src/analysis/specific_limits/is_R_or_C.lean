/-
Copyright (c) 2023 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Patrick Massot
-/
import analysis.specific_limits.basic
import analysis.complex.re_im_topology

/-!
# A collection of specific limit computations for is_R_or_C
-/

open set algebra filter

variables (𝕜 : Type*) [is_R_or_C 𝕜]

lemma is_R_or_C.tendsto_inverse_at_top_nhds_0_nat : 
  tendsto (λ n : ℕ, (n : 𝕜)⁻¹) at_top (nhds 0) :=
begin   
  rw show (λ n : ℕ, (n : 𝕜)⁻¹) = coe ∘  (λ n : ℕ, (n : ℝ)⁻¹), { ext1 n, simp },
  exact tendsto_algebra_map_inverse_at_top_nhds_0_nat 𝕜
end

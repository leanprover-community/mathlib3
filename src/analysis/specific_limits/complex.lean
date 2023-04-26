/-
Copyright (c) 2023 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Patrick Massot
-/


import data.complex.basic
import analysis.specific_limits.basic
import analysis.complex.re_im_topology

/-!
# A collection of specific limit computations in ℂ 
-/

namespace complex
open complex filter

lemma tendsto_inverse_at_top_nhds_0_nat : tendsto (λ n : ℕ, (n : ℂ)⁻¹) at_top (nhds 0) :=
begin   
  rw show (λ n : ℕ, (n : ℂ)⁻¹) = coe ∘  (λ n : ℕ, (n : ℝ)⁻¹), { ext1 n, simp },
  exact tendsto.comp continuous_of_real.continuous_at tendsto_inverse_at_top_nhds_0_nat
end

end complex
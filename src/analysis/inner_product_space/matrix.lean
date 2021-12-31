/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import analysis.inner_product_space.adjoint
import linear_algebra.matrix.to_lin

variables {𝕜 : Type*} {E : Type*} {F : Type*} {m : Type*} {n : Type*}
variables [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]
variables [fintype m] [fintype n] [decidable_eq m] [decidable_eq n]

variables {v₁ : basis m 𝕜 E} {v₂ : basis n 𝕜 F}

namespace matrix

local notation `adj` := @linear_map.adjoint 𝕜 _ _ _ _ _
  (finite_dimensional.of_fintype_basis v₁) (finite_dimensional.of_fintype_basis v₂)

lemma conj_transpose_eq_adjoint (A : matrix n m 𝕜) :
   (to_lin v₂ v₁ A.conj_transpose) = adj (to_lin v₁ v₂ A) := sorry

example (A : matrix m n 𝕜) : (to_lin v₁ v₂ A.conj_transpose) = 0 :=
begin
  rw [conj_transpose_eq_adjoint],
end

end matrix

/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import algebra.module.conjugate
import analysis.normed_space.inner_product

/-!
# Conjugate normed spaces and inner product spaces

## Implementation notes

## References

* https://en.wikipedia.org/wiki/Complex_conjugate_vector_space

## Tags
-/


section instances
open conj_semimodule is_R_or_C

variables {E 𝕜 : Type*} [is_R_or_C 𝕜]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

instance [e : normed_group E] : normed_group (conj_semimodule 𝕜 E) := e

instance [normed_group E] [e : normed_space 𝕜 E]: normed_space 𝕜 (conj_semimodule 𝕜 E) :=
{ norm_smul_le := λ r x,
  begin
    change ∥from_conj 𝕜 (r • x)∥ ≤ ∥r∥ * ∥x∥,
    rw [smul_def', norm_smul, norm_conj],
    apply le_of_eq,
    refl,
  end }

instance [normed_group E] [normed_space 𝕜 E] [has_inner 𝕜 E] : has_inner 𝕜 (conj_semimodule 𝕜 E) :=
{ inner := λ x y, ⟪from_conj 𝕜 y, from_conj 𝕜 x⟫ }

instance [inner_product_space 𝕜 E] : inner_product_space 𝕜 (conj_semimodule 𝕜 E) :=
{
  norm_sq_eq_inner := λ x, by { change ∥from_conj 𝕜 x∥^2 = re ⟪x, x⟫, exact norm_sq_eq_inner x },
  conj_sym := λ x y, inner_conj_sym _ _,
  nonneg_im := λ x, inner_self_nonneg_im,
  add_left := λ x y z,
  begin
    change ⟪from_conj 𝕜 z, from_conj 𝕜 (x + y)⟫ = ⟪from_conj 𝕜 z, from_conj 𝕜 x⟫ + ⟪from_conj 𝕜 z, from_conj 𝕜 y⟫,
    simp [from_conj_add, inner_add_right],
  end,
  smul_left := λ x y r, by simp [has_inner.inner, smul_def', inner_smul_right] }

end instances

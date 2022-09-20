/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.inner_product_space.adjoint
import analysis.normed_space.weak_dual

/-!
# Weak topology on Hilbert spaces

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open topological_space function inner_product_space
open_locale complex_conjugate

namespace weak_space

variables (𝕜 E F : Type*) [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]

local notation `E_σ` := weak_space 𝕜 E
local notation `Φ` := to_dual 𝕜 E

instance : has_inner 𝕜 E_σ :=
⟨(inner : E → E → 𝕜)⟩

protected lemma inducing_swap_inner [complete_space E] : inducing (swap inner : E_σ → E_σ → 𝕜) :=
begin
  split,
  refine le_antisymm _ _;
  refine continuous_iff_le_induced.mp _,
  { exact @continuous_pi E_σ _ _ _ _ (swap inner : E_σ → E_σ → 𝕜)
      (λ x, weak_bilin.eval_continuous _ (Φ x)) },
  { rw continuous_pi_iff,
    intros l,
    convert (continuous_apply $ (Φ).symm l).comp continuous_induced_dom,
    { refl },
    { refine heq_of_eq (eq.symm _),
      ext x,
      exact to_dual_symm_apply } }
end

protected lemma inducing_inner [complete_space E] : inducing (inner : E_σ → E_σ → 𝕜) :=
begin
  have : (inner : E_σ → E_σ → 𝕜) = ((∘) conj) ∘ (swap inner : E_σ → E_σ → 𝕜),
  { ext x y,
    exact (inner_conj_sym _ _).symm },
  rw this,
  let conjₜ : 𝕜 ≃ₜ 𝕜 :=
  { continuous_to_fun := is_R_or_C.continuous_conj,
    continuous_inv_fun := is_R_or_C.continuous_conj,
    ..star_involutive.to_perm _ },
  let comp_conjₜ := homeomorph.Pi_congr_right (λ (_ : E_σ), conjₜ),
  exact comp_conjₜ.inducing.comp (weak_space.inducing_swap_inner 𝕜 E)
end

lemma goal [complete_space E] [has_smul ℝ E] {s : set E} (hs₁ : is_closed s) (hs₂ : convex ℝ s) :
  is_closed (s : set E_σ) :=
begin
  sorry
end

end weak_space

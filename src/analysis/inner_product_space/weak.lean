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

open topological_space function inner_product_space is_R_or_C filter
open_locale complex_conjugate topological_space

namespace weak_space

variables (𝕜 E F : Type*) [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]

local notation `E_σ` := weak_space 𝕜 E
local notation `Φ` := to_dual 𝕜 E
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

instance : has_inner 𝕜 E_σ :=
⟨(inner : E → E → 𝕜)⟩

protected lemma inducing_swap_inner [complete_space E] : inducing (swap inner : E_σ → E_σ → 𝕜) :=
begin
  split,
  change induced _ (⨅ i, _) = induced _ (⨅ i, _),
  rw [induced_infi, induced_infi],
  refine ((to_dual 𝕜 E).to_equiv.infi_congr (λ x, _)).symm,
  rw [induced_compose, induced_compose],
  refl
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

protected lemma _root_.inner_product_space.tendsto_of_weak [complete_space E] {ι : Type*}
  {l : filter ι} {f : ι → E_σ} {x : E_σ} (hl₁ : tendsto (f : ι → E_σ) l (𝓝 (x : E_σ)))
  (hl₂ : tendsto (norm ∘ (coe : E_σ → E) ∘ f) l (𝓝 $ 0)) :
  tendsto (coe ∘ f : ι → E) l (𝓝 (x : E)) :=
begin
  assumption,
end

lemma goal [complete_space E] [has_smul ℝ E] {s : set E} (hs₁ : is_closed s) (hs₂ : convex ℝ s) :
  is_closed (s : set E_σ) :=
begin
  let H : E_σ → set E_σ := λ x, {z | re ⟪x, z⟫ ≤ re ⟪x - orthogonal_projection },
  have : s = ⋂ x,
end

end weak_space

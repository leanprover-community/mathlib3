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
  refine inducing.comp _ (weak_space.inducing_swap_inner 𝕜 E),
  have : (((∘) conj) ∘ ((∘) conj : (E_σ → 𝕜) → E_σ → 𝕜)) = id,
  { ext x y,
    exact is_R_or_C.conj_conj _ },
  have key := @inducing_id (E_σ → 𝕜) _,
  rw ← this at key,
  refine inducing_of_inducing_compose _ _ key;
  exact continuous_pi (λ x, is_R_or_C.continuous_conj.comp (continuous_apply x))
end

end weak_space

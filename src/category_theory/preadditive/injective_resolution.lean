import category_theory.preadditive.injective
import algebra.homology.single
import algebra.homology.homotopy_category

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

open injective

section
variables [has_zero_object C] [has_zero_morphisms C] [has_equalizers C] [has_images C]

@[nolint has_inhabited_instance]
structure InjectiveResolution (Z : C) :=
(cocomplex : cochain_complex C ℕ)
(ι: homological_complex.hom ((cochain_complex.single₀ C).obj Z) cocomplex)
(injective : ∀ n, injective (cocomplex.X n) . tactic.apply_instance)
(exact₀ : exact (ι.f 0) (cocomplex.d 0 1) . tactic.apply_instance)
(exact : ∀ n, exact (cocomplex.d (n+2) (n+1)) (cocomplex.d (n+1) n) . tactic.apply_instance)
(mono : mono (ι.f 0) . tactic.apply_instance)

attribute [instance] InjectiveResolution.injective InjectiveResolution.exact₀
  InjectiveResolution.exact InjectiveResolution.mono

end

end category_theory

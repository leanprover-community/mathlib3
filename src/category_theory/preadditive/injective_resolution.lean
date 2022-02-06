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

class has_injective_resolution (Z : C) : Prop :=
(out [] : nonempty (InjectiveResolution Z))

end

section
variables (C) [has_zero_object C] [has_zero_morphisms C] [has_equalizers C] [has_images C]

/--
You will rarely use this typeclass directly: it is implied by the combination
`[enough_projectives C]` and `[abelian C]`.
By itself it's enough to set up the basic theory of derived functors.
-/
class has_injective_resolutions : Prop :=
(out : ∀ Z : C, has_injective_resolution Z)

attribute [instance, priority 100] has_injective_resolutions.out

end

namespace InjectiveResolution
variables (C) [has_zero_object C] [has_zero_morphisms C] [has_equalizers C] [has_images C]

@[simp] lemma ι_f_succ {Z : C} (P : InjectiveResolution Z) (n : ℕ) :
  P.ι.f (n+1) = 0 :=
begin
  apply zero_of_source_iso_zero,
  dsimp, refl,
end

instance {Z : C} (P : InjectiveResolution Z) (n : ℕ) : category_theory.mono (P.ι.f n) :=
by cases n; apply_instance

def self (Z : C) [category_theory.injective Z] : InjectiveResolution Z :=
{ cocomplex := (cochain_complex.single₀ C).obj Z,
  ι := 𝟙 ((cochain_complex.single₀ C).obj Z),
  injective := λ n, begin
    cases n;
    { dsimp, apply_instance },
  end,
  exact₀ := by { dsimp, apply_instance },
  exact := λ n, by { dsimp, apply_instance, },
  mono := by { dsimp, apply_instance, }, }


end InjectiveResolution

end category_theory

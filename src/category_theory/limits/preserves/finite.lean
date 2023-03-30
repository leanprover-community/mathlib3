/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.limits.preserves.basic
import category_theory.fin_category

/-!
# Preservation of finite (co)limits.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These functors are also known as left exact (flat) or right exact functors when the categories
involved are abelian, or more generally, finitely (co)complete.

## Related results
* `category_theory.limits.preserves_finite_limits_of_preserves_equalizers_and_finite_products` :
  see `category_theory/limits/constructions/limits_of_products_and_equalizers.lean`. Also provides
  the dual version.
* `category_theory.limits.preserves_finite_limits_iff_flat` :
  see `category_theory/flat_functors.lean`.

-/

open category_theory

namespace category_theory.limits

-- declare the `v`'s first; see `category_theory.category` for an explanation
universes w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]
variables {E : Type u₃} [category.{v₃} E]

variables {J : Type w} [small_category J] {K : J ⥤ C}

/--
A functor is said to preserve finite limits, if it preserves all limits of shape `J`,
where `J : Type` is a finite category.
-/
class preserves_finite_limits (F : C ⥤ D) :=
(preserves_finite_limits : Π (J : Type) [small_category J] [fin_category J],
  preserves_limits_of_shape J F . tactic.apply_instance)

attribute [instance] preserves_finite_limits.preserves_finite_limits

/-- Preserving finite limits also implies preserving limits over finite shapes in higher universes,
though through a noncomputable instance. -/
@[priority 100]
noncomputable instance preserves_limits_of_shape_of_preserves_finite_limits (F : C ⥤ D)
  [preserves_finite_limits F] (J : Type w) [small_category J] [fin_category J] :
  preserves_limits_of_shape J F :=
by apply preserves_limits_of_shape_of_equiv (fin_category.equiv_as_type J)

@[priority 100]
noncomputable instance preserves_limits.preserves_finite_limits_of_size (F : C ⥤ D)
  [preserves_limits_of_size.{w w₂} F] : preserves_finite_limits F :=
⟨λ J sJ fJ,
  begin
    haveI := preserves_smallest_limits_of_preserves_limits F,
    exact preserves_limits_of_shape_of_equiv (fin_category.equiv_as_type J) F,
  end⟩

@[priority 120]
noncomputable instance preserves_limits.preserves_finite_limits (F : C ⥤ D)
  [preserves_limits F] : preserves_finite_limits F :=
preserves_limits.preserves_finite_limits_of_size F

/-- We can always derive `preserves_finite_limits C` by showing that we are preserving limits at an
arbitrary universe. -/
def preserves_finite_limits_of_preserves_finite_limits_of_size (F : C ⥤ D)
  (h : ∀ (J : Type w) {𝒥 : small_category J} (hJ : @fin_category J 𝒥),
    by { resetI, exact preserves_limits_of_shape J F }) :
  preserves_finite_limits F :=
⟨λ J hJ hhJ,
  begin
    resetI,
    letI : category.{w w} (ulift_hom.{w} (ulift.{w 0} J)),
    { apply ulift_hom.category.{0}, exact category_theory.ulift_category J },
    haveI := h (ulift_hom.{w} (ulift.{w} J)) category_theory.fin_category_ulift,
    exact preserves_limits_of_shape_of_equiv (ulift_hom_ulift_category.equiv.{w w} J).symm F
  end⟩

instance id_preserves_finite_limits : preserves_finite_limits (𝟭 C) := {}

/-- The composition of two left exact functors is left exact. -/
def comp_preserves_finite_limits (F : C ⥤ D) (G : D ⥤ E)
  [preserves_finite_limits F] [preserves_finite_limits G] : preserves_finite_limits (F ⋙ G) :=
⟨λ _ _ _, by { resetI, apply_instance }⟩

/--
A functor is said to preserve finite colimits, if it preserves all colimits of
shape `J`, where `J : Type` is a finite category.
-/
class preserves_finite_colimits (F : C ⥤ D) :=
(preserves_finite_colimits : Π (J : Type) [small_category J] [fin_category J],
  preserves_colimits_of_shape J F . tactic.apply_instance)

attribute [instance] preserves_finite_colimits.preserves_finite_colimits

/-- Preserving finite limits also implies preserving limits over finite shapes in higher universes,
though through a noncomputable instance. -/
@[priority 100]
noncomputable instance preserves_colimits_of_shape_of_preserves_finite_colimits (F : C ⥤ D)
  [preserves_finite_colimits F] (J : Type w) [small_category J] [fin_category J] :
  preserves_colimits_of_shape J F :=
by apply preserves_colimits_of_shape_of_equiv (fin_category.equiv_as_type J)

@[priority 100]
noncomputable instance preserves_colimits.preserves_finite_colimits (F : C ⥤ D)
  [preserves_colimits_of_size.{w w₂} F] : preserves_finite_colimits F :=
⟨λ J sJ fJ,
  begin
    haveI := preserves_smallest_colimits_of_preserves_colimits F,
    exact preserves_colimits_of_shape_of_equiv (fin_category.equiv_as_type J) F,
  end⟩

/-- We can always derive `preserves_finite_limits C` by showing that we are preserving limits at an
arbitrary universe. -/
def preserves_finite_colimits_of_preserves_finite_colimits_of_size (F : C ⥤ D)
  (h : ∀ (J : Type w) {𝒥 : small_category J} (hJ : @fin_category J 𝒥),
    by { resetI, exact preserves_colimits_of_shape J F }) :
  preserves_finite_colimits F :=
⟨λ J hJ hhJ,
  begin
    resetI,
    letI : category.{w w} (ulift_hom.{w} (ulift.{w 0} J)),
    { apply ulift_hom.category.{0}, exact category_theory.ulift_category J },
    haveI := h (ulift_hom.{w} (ulift.{w} J)) category_theory.fin_category_ulift,
    exact preserves_colimits_of_shape_of_equiv (ulift_hom_ulift_category.equiv.{w w} J).symm F
  end⟩

instance id_preserves_finite_colimits : preserves_finite_colimits (𝟭 C) := {}

/-- The composition of two right exact functors is right exact. -/
def comp_preserves_finite_colimits (F : C ⥤ D) (G : D ⥤ E)
  [preserves_finite_colimits F] [preserves_finite_colimits G] :
  preserves_finite_colimits (F ⋙ G) :=
⟨λ _ _ _, by { resetI, apply_instance }⟩

end category_theory.limits

/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.sites.cover_preserving
import category_theory.sites.left_exact

/-!
# Pushforward of sheaves

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `category_theory.sites.pushforward`: the induced functor `Sheaf J A ⥤ Sheaf K A` for a
cover-preserving and compatible-preserving functor `G : (C, J) ⥤ (D, K)`.

-/

universes v₁ u₁
noncomputable theory

open category_theory.limits

namespace category_theory

variables {C : Type v₁} [small_category C] {D : Type v₁} [small_category D]
variables (A : Type u₁) [category.{v₁} A]
variables (J : grothendieck_topology C) (K : grothendieck_topology D)

instance [has_limits A] : creates_limits (Sheaf_to_presheaf J A) :=
category_theory.Sheaf.category_theory.Sheaf_to_presheaf.category_theory.creates_limits.{u₁ v₁ v₁}

-- The assumptions so that we have sheafification
variables [concrete_category.{v₁} A] [preserves_limits (forget A)] [has_colimits A] [has_limits A]
variables [preserves_filtered_colimits (forget A)] [reflects_isomorphisms (forget A)]

local attribute [instance] reflects_limits_of_reflects_isomorphisms

instance {X : C} : is_cofiltered (J.cover X) := infer_instance

/-- The pushforward functor `Sheaf J A ⥤ Sheaf K A` associated to a functor `G : C ⥤ D` in the
same direction as `G`. -/
@[simps] def sites.pushforward (G : C ⥤ D) : Sheaf J A ⥤ Sheaf K A :=
Sheaf_to_presheaf J A ⋙ Lan G.op ⋙ presheaf_to_Sheaf K A

instance (G : C ⥤ D) [representably_flat G] :
  preserves_finite_limits (sites.pushforward A J K G) :=
begin
  apply_with comp_preserves_finite_limits { instances := ff },
  { apply_instance },
  apply_with comp_preserves_finite_limits { instances := ff },
  { apply category_theory.Lan_preserves_finite_limits_of_flat },
  { apply category_theory.presheaf_to_Sheaf.limits.preserves_finite_limits.{u₁ v₁ v₁},
    apply_instance }
end

/-- The pushforward functor is left adjoint to the pullback functor. -/
def sites.pullback_pushforward_adjunction {G : C ⥤ D} (hG₁ : compatible_preserving K G)
  (hG₂ : cover_preserving J K G) : sites.pushforward A J K G ⊣ sites.pullback A hG₁ hG₂ :=
((Lan.adjunction A G.op).comp (sheafification_adjunction K A)).restrict_fully_faithful
  (Sheaf_to_presheaf J A) (𝟭 _)
  (nat_iso.of_components (λ _, iso.refl _)
    (λ _ _ _,(category.comp_id _).trans (category.id_comp _).symm))
  (nat_iso.of_components (λ _, iso.refl _)
    (λ _ _ _,(category.comp_id _).trans (category.id_comp _).symm))

end category_theory

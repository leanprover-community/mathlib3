import category_theory.limits.preserves.basic
import category_theory.limits.shapes.finite_limits
import category_theory.limits.functor_category
import category_theory.filtered
import category_theory.full_subcategory

namespace category_theory

universes w v u₁ u₂

variables {J : Type v} [small_category J]
variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]

namespace limits

class preserves_filtered_colimits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
(preserves_colimits_of_shape : Π {J : Type v} [𝒥 : small_category J] [is_filtered J],
  by exactI preserves_colimits_of_shape J F)

variables (C D)

def PreservesFilteredColimits := Σ F : C ⥤ D, preserves_filtered_colimits F

instance : category.{max u₁ v} (PreservesFilteredColimits C D) :=
induced_category.category (λ F, F.1)

namespace PreservesFilteredColimits

@[derive [full, faithful]]
def forget : PreservesFilteredColimits C D ⥤ (C ⥤ D) :=
induced_functor _

def small_ulift (J : Type v) := ulift.{w} J
instance (J : Type v) [small_category J] : small_category (small_ulift.{w} J) :=
{ hom  := λ X Y, ulift (X.down ⟶ Y.down),
  id   := λ X, ulift.up (𝟙 X.down),
  comp := λ _ _ _ f g, ulift.up (f.down ≫ g.down) }

def down (J : Type v) [small_category J] : small_ulift.{w} J ⥤ J :=
{ obj := λ X, X.down,
  map := λ X Y f, f.down, }

variables {C' : Type (u₁+1)} [large_category C']
variables {D' : Type (u₁+1)} [large_category D']
variables {J' : Type (u₁+1)} [small_category J']

variables [has_limits D']
-- example : has_limits (C ⥤ D) := by apply_instance


example (F : J' ⥤ (C' ⥤ D')) : has_limit F := by apply_instance

instance : has_finite_limits (PreservesFilteredColimits C D) :=
λ J 𝒥 ℱ, by exactI
{ has_limit := λ F,
  { cone :=
    { X := ⟨limit (F ⋙ forget C D), sorry⟩,
      π := sorry, },
    is_limit := sorry, } }

-- TODO forget preserves finite limits

end PreservesFilteredColimits

end limits

end category_theory

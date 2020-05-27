import category_theory.comma
import category_theory.full_subcategory
import category_theory.isomorphism_classes
import category_theory.limits.shapes.zero

open category_theory.limits

namespace category_theory

universes v u
variables {C : Type u} [category.{v} C]
variables [has_zero_morphisms.{v} C]

class simple (X : C) :=
(mono_is_iso_equiv_nonzero : ∀ {Y : C} (f : Y ⟶ X) [mono f], is_iso.{v} f ≃ (f ≠ 0))

def is_iso_of_mono_of_nonzero {X Y : C} [simple.{v} X] (f : Y ⟶ X) [mono f] (w : f ≠ 0) : is_iso f :=
(simple.mono_is_iso_equiv_nonzero f).symm w

section
variable [has_zero_object.{v} C]
local attribute [instance] has_zero_object.has_zero

lemma zero_not_simple [simple.{v} (0 : C)] : false :=
(simple.mono_is_iso_equiv_nonzero (0 : (0 : C) ⟶ (0 : C))) { inv := 0, } rfl

end

end category_theory

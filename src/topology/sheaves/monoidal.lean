import category_theory.monoidal.internal.functor_category
import algebra.category.Group.monoidal
import category_theory.functor.equivalence

open category_theory category_theory.monoidal

universes w u₁ v₁
variables {C : Type u₁} [category.{v₁} C]


section Ab

namespace presheaf

local attribute [instance] AddCommGroup.Mon_.tensor_monoidal_category

@[simps] def Mon_presheaf_Ab_equiv_presheaf_ring : Mon_ (Cᵒᵖ ⥤ AddCommGroup.{w}) ≌ (Cᵒᵖ ⥤ Ring.{w}) :=
(Mon_functor_category_equivalence Cᵒᵖ AddCommGroup).trans $
_

end presheaf

end Ab

import category_theory.examples.topological_spaces

import category_theory.opposites
import category_theory.yoneda
import category_theory.limits
import category_theory.limits.types
import category_theory.limits.functor_category

open category_theory

universes u u₁ u₂ v v₁ v₂ w w₁ w₂

section presheaf
open category_theory.limits
variables (X : Type v) [𝒳 : small_category X] (C : Type u) [𝒞 : category.{u v} C]
include 𝒳 𝒞

def presheaf := Xᵒᵖ ⥤ C

variables {X} {C}

instance : category.{(max u v) v} (presheaf X C) := by unfold presheaf; apply_instance

set_option pp.universes true
instance presheaf.has_coequalizers [has_coequalizers.{u v} C] :
  has_coequalizers.{(max u v) v} (presheaf X C) := limits.functor_category_has_coequalizers
instance presheaf.has_coproducts [has_coproducts.{u v} C] :
  has_coproducts.{(max u v) v} (presheaf X C) := limits.functor_category_has_coproducts
instance presheaf.has_limits [has_limits.{u v} C] :
  has_limits.{(max u v) v} (presheaf X C) := limits.functor_category_has_limits
instance presheaf.has_pullbacks [has_pullbacks.{u v} C] :
  has_pullbacks.{(max u v) v} (presheaf X C) := limits.functor_category_has_pullbacks

omit 𝒞

-- TODO these can be removed; just checking they work
instance presheaf_of_types.has_coequalizers : has_coequalizers.{v+1 v} (presheaf X (Type v)) := by apply_instance
instance presheaf_of_types.has_coproducts : has_coproducts.{v+1 v} (presheaf X (Type v)) := by apply_instance
instance presheaf_of_types.has_limits : has_limits.{v+1 v} (presheaf X (Type v)) := by apply_instance
instance presheaf_of_types.has_pullbacks : has_pullbacks.{v+1 v} (presheaf X (Type v)) := by apply_instance

end presheaf

section over_under -- move somewhere else

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def over (X : C) := comma (functor.id C) (category_theory.limits.functor.of_obj X)

def under (X : C) := comma (category_theory.limits.functor.of_obj X) (functor.id C)

instance over.category {X : C} : category (over X) := by unfold over; apply_instance

def over.forget (X : C) : (over X) ⥤ C :=
{ obj  := λ Y, Y.left,
  map' := λ _ _ f, f.left } -- why these underscores? They should be implicit

def over.to_hom {X : C} (Y : over X) : Y.left ⟶ X := Y.hom

end over_under

@[reducible]
def covering_family {X : Type v} [small_category X] (U : X) : Type v := set (over.{v v} U)

namespace covering_family
open category_theory.limits
variables {X : Type v} [𝒳 : small_category X]
include 𝒳

variables {U : X} (c : covering_family U)

def sieve : presheaf X (Type v) :=
let
  y (Ui : c) := (yoneda X).map Ui.val.hom,
  pb (Ujk : c × c) : presheaf X (Type v) := limits.pullback (y Ujk.1) (y Ujk.2),
  re (Ui : c) : presheaf X (Type v) := (yoneda X).obj Ui.val.left,
  left  : limits.sigma pb ⟶ limits.sigma re :=
    sigma.desc $ λUjk:c×c, pullback.π₁ (y Ujk.1) (y Ujk.2) ≫ sigma.ι re Ujk.1,
  right : limits.sigma pb ⟶ limits.sigma re :=
    sigma.desc $ λUjk:c×c, pullback.π₂ (y Ujk.1) (y Ujk.2) ≫ sigma.ι re Ujk.2
in coequalizer left right

def π : c.sieve ⟶ yoneda X U :=
coequalizer.desc _ _ (sigma.desc $ λUi, (yoneda X).map Ui.val.hom)
begin
  ext1, dsimp at *,
  erw ←category.assoc,
  erw ←category.assoc,
  simp,
end

def sheaf_condition := is_iso $ (yoneda (presheaf X (Type v))).map c.π

end covering_family

structure coverage (X : Type u) [small_category.{u} X] :=
(covers   : Π (U : X), set (covering_family U))
(property : ∀ {U V : X} (g : V ⟶ U) (f ∈ covers U),
            ∃ (h ∈ covers V), ∀ Vj : h, ∃ (Ui : f) (k : Vj.left ⟶ Ui.left),
            Vj.hom ≫ g = k ≫ Ui.hom)

#check coverage

class site (X : Type u) extends category.{u u} X :=
(coverage' : coverage X)

namespace site
variables {X : Type u₁} [𝒳 : site.{u₁} X]

definition covers := coverage.covers 𝒳.coverage

end site

section sheaf
variables (X : Type u₁) [𝒳 : site.{u₁} X] (C : Type u₂) [𝒞 : category.{u₂ v₂} C]
include 𝒳 𝒞

structure sheaf :=
(presheaf : presheaf X C)
(sheaf_condition : ∀ {U : X} (c ∈ site.covers U), c.sheaf_condition presheaf)

end sheaf


namespace topological_space

variables {X : Type u} [topological_space X]

instance : site (opens X) :=
{ coverage :=
  { covers := λ U, λ Us, begin sorry -- the union of the Ui should be U
    end,
    property := sorry } }

end topological_space

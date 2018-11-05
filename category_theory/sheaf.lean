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
  has_coequalizers.{(max u v) v} (presheaf X C) :=
sorry
instance presheaf.has_coproducts [has_coproducts.{u v} C] :
  has_coproducts.{(max u v) v} (presheaf X C) :=
sorry
instance presheaf.has_limits [has_limits.{u v} C] :
  has_limits.{(max u v) v} (presheaf X C) :=
begin
  dsimp [presheaf],
  exact limits.functor_category_has_limits
end
instance presheaf.has_pullbacks [has_pullbacks.{u v} C] :
  has_pullbacks.{(max u v) v} (presheaf X C) :=
sorry

omit 𝒞

instance presheaf_of_types.has_coequalizers : has_coequalizers.{v+1 v} (presheaf X (Type v)) := by apply_instance
instance presheaf_of_types.has_coproducts : has_coproducts.{v+1 v} (presheaf X (Type v)) := by apply_instance
instance presheaf_of_types.has_limits : has_limits.{v+1 v} (presheaf X (Type v)) := by apply_instance
instance presheaf_of_types.has_pullbacks : has_pullbacks.{v+1 v} (presheaf X (Type v)) := by apply_instance


end presheaf

-- todo should this be done as a subfunctor?
structure covering_family {X : Type v} [small_category X] (U : X) :=
(index : Type v₁)
(obj : index → X)
(map : Π (i : index), obj i ⟶ U)

namespace covering_family
open category_theory.limits
variables {X : Type v} [𝒳 : small_category X]
include 𝒳

variables {U : X} (f : covering_family U)

set_option pp.universes true
def sieve : presheaf X (Type v) :=
let CP := (((yoneda X) : X → presheaf X (Type v)) ∘ f.obj) in
coequalizer
  (sigma.desc (λ p : (f.index × f.index), (sigma.ι ((yoneda X) ∘ f.obj) p.1) ∘ (pullback.π₁ ((yoneda X).map (f.map p.1)) ((yoneda X).map (f.map p.2)))))
  (sigma.desc (λ p : (f.index × f.index), (sigma.ι ((yoneda X) ∘ f.obj) p.2) ∘ (pullback.π₂ ((yoneda X).map (f.map p.1)) ((yoneda X).map (f.map p.2)))))

def π : f.sieve ⟶ yoneda X U := coequalizer.desc (sigma.desc (λ i : f.index, (yoneda X).map (f.map i))) _

def sheaf_condition (f : (covering_family U)) {C : Type u₂} [category.{u₂ v₂} C] (F : presheaf X C) : Prop := sorry

end covering_family

structure coverage {X : Type u₁} [small_category.{u₁} X] :=
(covers   : Π (U : X), set (covering_family U))
(property : ∀ {U V : X} (g : V ⟶ U) (f : (covering_family U)) (Hf : f ∈ covers U),
            ∃ (h : covering_family V) (Hh : h ∈ covers V), ∀ j : h.index, ∃ {i : f.index} {k : h.obj j ⟶ f.obj i},
            h.map j ≫ g = k ≫ f.map i)

class site (X : Type u₁) extends category.{u₁} X :=
(coverage : @coverage X (by assumption))

namespace site
variables {X : Type u₁} [𝒳 : site.{u₁} X]

definition covers := coverage.covers 𝒳.coverage

end site

section sheaf
variables (X : Type u₁) [𝒳 : site.{u₁} X] (C : Type u₂) [𝒞 : category.{u₂ v₂} C]
include 𝒳 𝒞

structure sheaf :=
(presheaf : presheaf X C)
(sheaf_condition : ∀ {U : X} (f ∈ site.covers U), f.sheaf_condition presheaf)

end sheaf


namespace topological_space

variables {X : Type u} [topological_space X]

instance : site (opens X) :=
{ coverage :=
  { covers := λ U, λ Us, begin sorry -- the union of the Ui should be U
    end,
    property := sorry } }

end topological_space

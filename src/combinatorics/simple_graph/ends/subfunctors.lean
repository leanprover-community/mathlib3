import category_theory.types
import category_theory.functor
import data.set.function

universes u v w

open category_theory

namespace category_theory.functor


def subfunctor {C : Type u} [category C] (F : C ⥤ Type v)
  (obj : ∀ c, set $ F.obj c) 
  (map : ∀ (c d : C) (m : c ⟶ d), set.maps_to (F.map m) (obj c) (obj d)) : C ⥤ Type v := 
{ obj := λ c, subtype (obj c),
  map := λ c d m, set.maps_to.restrict _ _ _ (map c d m),
  map_id' := by {intro, ext, simp only [map_id, set.maps_to.coe_restrict_apply, types_id_apply], },
  map_comp' := by {intros, ext, simp only [map_comp, set.maps_to.coe_restrict_apply, types_comp_apply], },}

lemma subfunctor.ext {C : Type u} [category C] (F : C ⥤ Type v)
  (obj₁ : ∀ c, set $ F.obj c) 
  (map₁ : ∀ (c d : C) (m : c ⟶ d), set.maps_to (F.map m) (obj₁ c) (obj₁ d)) 
  (obj₂ : ∀ c, set $ F.obj c) 
  (map₂ : ∀ (c d : C) (m : c ⟶ d), set.maps_to (F.map m) (obj₂ c) (obj₂ d)) : 
  (∀ c, obj₁ c = obj₂ c) → F.subfunctor obj₁ map₁ = F.subfunctor obj₂ map₂ := 
begin
  rintro objeq,
  dsimp [subfunctor], 
  fapply category_theory.functor.hext,
  dsimp,
  { rintro c, rw objeq c, },
  { rintro c d m,
    dsimp only [set.maps_to.restrict],
    apply function.hfunext, 
    rw objeq, 
    rintro a a' aea',
    dsimp only [subtype.map],
    rw subtype.heq_iff_coe_eq at aea' ⊢,
    { simp only [subtype.coe_mk], rw aea', },
    all_goals { rintro, rw (objeq),},},
end



end category_theory.functor
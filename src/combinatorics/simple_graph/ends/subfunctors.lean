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
  have : obj₁ = obj₂ := funext objeq,
  subst this,
end

-- Thanks Andrew Yang and _Adam Topaz_ for this snippet!
def subfunctor.iso {C : Type u} [category C] (F : C ⥤ Type v)
  (obj₁ : ∀ c, set $ F.obj c)
  (map₁ : ∀ (c d : C) (m : c ⟶ d), set.maps_to (F.map m) (obj₁ c) (obj₁ d))
  (obj₂ : ∀ c, set $ F.obj c)
  (map₂ : ∀ (c d : C) (m : c ⟶ d), set.maps_to (F.map m) (obj₂ c) (obj₂ d)) :
  (∀ c, obj₁ c = obj₂ c) → (F.subfunctor obj₁ map₁ ≅ F.subfunctor obj₂ map₂) := λ objeq,
nat_iso.of_components
(λ X, equiv.to_iso $ equiv.subtype_equiv_prop $ objeq _ ) (by tidy)


def subtype_functor {C : Type u} [category C] (F : C ⥤ Type v)
  (obj : ∀ c, set $ F.obj c)
  (map : ∀ (c d : C) (m : c ⟶ d), set.maps_to (F.map m) (obj c) (obj d)) : C ⥤ Type v :=
{ obj := λ c, subtype (obj c),
  map := λ c d m ⟨x, p⟩, ⟨F.map m x, by {apply map, exact p,}⟩,
  map_id' := by {intro, ext ⟨_, _⟩, show F.map (𝟙 X) x_val = _, rw [F.map_id], refl,},
  map_comp' := by {intros, ext ⟨_, _⟩, show F.map (f ≫ g) x_val = _, rw [F.map_comp], refl,} }


lemma subfunctor.obj_eq {C : Type u} [category C] (F : C ⥤ Type v)
  (obj : ∀ c, set $ F.obj c)
  (map : ∀ (c d : C) (m : c ⟶ d), set.maps_to (F.map m) (obj c) (obj d)) :
    ∀ c, (F.subfunctor obj map).obj c = subtype (obj c) := by {intro, refl,}

lemma subfunctor.map_eq {C : Type u} [category C] (F : C ⥤ Type v)
  (obj : ∀ c, set $ F.obj c)
  (map : ∀ (c d : C) (m : c ⟶ d), set.maps_to (F.map m) (obj c) (obj d)) :
    ∀ (c d : C), ∀ f : c ⟶ d, (F.subfunctor obj map).map f = subtype.map (F.map f) (λ a, by show_term{
      show a ∈ obj c → (F.map f a) ∈ obj d,
    apply map,})  := by {intros, refl,}


lemma subtype_functor_eq_subfunctor {C : Type u} [category C] (F : C ⥤ Type v)
  (obj : ∀ c, set $ F.obj c)
  (map : ∀ (c d : C) (m : c ⟶ d), set.maps_to (F.map m) (obj c) (obj d)) :
  subfunctor F obj map = subtype_functor F obj map := by {
    apply ext,
    {intros, ext ⟨_, _⟩, refl,},
    {intros, refl,} }

end category_theory.functor

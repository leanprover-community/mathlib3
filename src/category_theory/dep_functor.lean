import category_theory.category.Cat

universes v' u' v u

namespace category_theory

variables (C : Type u) [category.{v} C]

structure prelax_functor_to_Cat extends prefunctor C Cat.{v' u'} :=
(map_id (X : C) : map (𝟙 X) ⟶ 𝟭 (obj X))
(map_comp ⦃X Y Z : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ⟶ map f ⋙ map g)

structure prelax_functor_hom (F₁ F₂ : prelax_functor_to_Cat C) :=
(app (X : C) : F₁.obj X ⟶ F₂.obj X)
(naturality {X Y : C} (f : X ⟶ Y) : )

instance : category (prelax_functor_to_Cat C) :=
{ hom := ,

}

variables {C} (F : prelax_functor_to_Cat C)

structure dep_functor :=
(obj (X : C) : F.obj X)
(map {X Y : C} (f : X ⟶ Y) : (F.map f).obj (obj X) ⟶ obj Y)
(map_id (X : C) : map (𝟙 X) = (F.map_id X).app (obj X))
(map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  map (f ≫ g) = (F.map_comp f g).app (obj X) ≫ (F.map g).map (map f) ≫ map g)

variables (Fd₁ Fd₂ : dep_functor F)

structure dep_functor_hom :=
(app (X : C) : Fd₁.obj X ⟶ Fd₂.obj X)
(naturality {X Y : C} (f : X ⟶ Y) : Fd₁.map f ≫ app Y = (F.map f).map (app X) ≫ Fd₂.map f)

instance : quiver (dep_functor F) := { hom := dep_functor_hom F }

variables {Fd₁ Fd₂}

@[ext] lemma dep_functor_hom_ext (α₁ α₂ : Fd₁ ⟶ Fd₂) (h : α₁.app = α₂.app) : α₁ = α₂ :=
by { cases α₁, cases α₂, congr, exact h }

instance : category (dep_functor F) :=
{ hom := dep_functor_hom F,
  id := λ Fd, { app := λ X, 𝟙 _, naturality := by simp },
  comp := λ Fd₁ Fd₂ Fd₃ α₁ α₂,
  { app := λ X, α₁.app X ≫ α₂.app X,
    naturality := λ X Y f, by { rw [← category.assoc, α₁.naturality], simp [α₂.naturality] } } }

def dep_functor_prelax_functor : prelax_functor_to_Cat (prelax_functor_to_Cat F) :=


end category_theory

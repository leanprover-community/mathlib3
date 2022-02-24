import category_theory.category.Cat
import category_theory.bicategory.locally_discrete

universes v' u' v u

namespace category_theory

variables {C : Type u} [category.{v} C] (F : oplax_functor (locally_discrete C) Cat.{v' u'})

namespace oplax_functor

variables ⦃X Y Z W : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (E : F.obj X)

@[simp, reassoc]
lemma id_comp_components :
  (F.map_comp (𝟙 X) f).app E ≫ (F.map f).map ((F.map_id X).app E) = eq_to_hom (by simpa) :=
by { convert nat_trans.congr_app (F.id_comp f) E, simpa }

@[simp, reassoc]
lemma comp_id_components :
  (F.map_comp f (𝟙 Y)).app E ≫ (F.map_id Y).app ((F.map f).obj E) = eq_to_hom (by simpa) :=
by { convert nat_trans.congr_app (F.comp_id f) E, simpa }

@[simp, reassoc]
lemma assoc_components : (F.map_comp (f ≫ g) h).app E ≫ (F.map h).map ((F.map_comp f g).app E) =
  eq_to_hom (by simp) ≫ (F.map_comp f (g ≫ h)).app E ≫ (F.map_comp g h).app ((F.map f).obj E) :=
by { convert nat_trans.congr_app (F.assoc f g h) E using 1, simpa }

end oplax_functor

/-- The type of dependent functors from a category `C` to a family of categories indexed
  by `C` specified by a `oplax_functor` from `locally_discrete C` to `Cat`. For `C` an opposite
  category, this is the type of dependent presheaves. -/
structure dfunctor :=
(obj (X : C) : F.obj X)
(map {X Y : C} (f : X ⟶ Y) : (F.map f).obj (obj X) ⟶ obj Y)
(map_id : ∀ X : C, map (𝟙 X) = (F.map_id X).app (obj X))
(map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) =
  (F.map_comp f g).app (obj X) ≫ (F.map g).map (map f) ≫ map g)

/- TODO: define category structure
   Show category of O-modules is isomorphic to such a category
   (need to use composition of oplax functors).
   Notion of sheaves when `Cᵒᵖ` has a grothendieck topology
   Construct oplax functor from `F : oplax_functor C Cat` to `dfunctor F`.
   Show the grothendieck construction associated to this oplax functor is isomorphic
   to the category of functors from `C` to grothendieck applied to `𝟭 _ : Cat ⥤ Cat`...!
-/

end category_theory

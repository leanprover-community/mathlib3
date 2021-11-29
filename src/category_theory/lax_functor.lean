/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import category_theory.category.Cat

/-! Lax functors and pseudofunctors to the 2-category of categories

A lax functor `F` from a 1-category `C` to the 2-category `Cat` assigns a category
`F.obj X` to each object of `X : C` and a functor `F.map f` to each morphism
`f : X ⟶ Y` in `C` (which we call the component functor at `f`) with natural
transformations from `F.map (𝟙 X)` to the identity functor (`map_id`), and from
the component functor at a composition to the composition of component functors
(`map_comp`), satisfying natural compatibility conditions (`id_comp`, `comp_id`,
and `assoc`).

In case all component functors have right adjoints, we can transfer the
lax functor structure of `F` across the adjunctions to obtain a lax functor
`G` from `Cᵒᵖ` to `Cat` with component functors opposites (`functor.op`) of
the right adjoints.


-/


namespace category_theory

variables (C : Type*) [category C]

structure lax_functor_to_Cat extends prefunctor C Cat :=
(map_id : ∀ (X : C), map (𝟙 X) ⟶ 𝟭 (obj X))
(map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) ⟶ map f ⋙ map g)
(id_comp : ∀ {X Y : C} (f : X ⟶ Y), map_comp (𝟙 X) f ≫ whisker_right (map_id X) (map f) =
  eq_to_hom (by {rw category.id_comp, cases map f, refl}) . obviously)
(comp_id : ∀ {X Y : C} (f : X ⟶ Y), map_comp f (𝟙 Y) ≫ whisker_left (map f) (map_id Y) =
  eq_to_hom (by {rw category.comp_id, cases map f, refl}) . obviously)
(assoc : ∀ {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W),
  map_comp (f ≫ g) h ≫ whisker_right (map_comp f g) (map h) = eq_to_hom (by rw category.assoc) ≫
  map_comp f (g ≫ h) ≫ whisker_left (map f) (map_comp g h) . obviously)

variables {C} (F : lax_functor_to_Cat C)

namespace lax_functor_to_Cat

variables {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (𝒳 : (F.obj X).1)

@[simp, reassoc]
lemma id_comp_components :
  (F.map_comp (𝟙 X) f).app 𝒳 ≫ (F.map f).map ((F.map_id X).app 𝒳) = eq_to_hom (by simp) :=
by { convert nat_trans.congr_app (F.id_comp f) 𝒳, simpa }

@[simp, reassoc]
lemma comp_id_components :
  (F.map_comp f (𝟙 Y)).app 𝒳 ≫ (F.map_id Y).app ((F.map f).obj 𝒳) = eq_to_hom (by simp) :=
by { convert nat_trans.congr_app (F.comp_id f) 𝒳, simpa }

@[simp, reassoc]
lemma assoc_components : (F.map_comp (f ≫ g) h).app 𝒳 ≫ (F.map h).map ((F.map_comp f g).app 𝒳) =
  eq_to_hom (by simp) ≫ (F.map_comp f (g ≫ h)).app 𝒳 ≫ (F.map_comp g h).app ((F.map f).obj 𝒳) :=
by { convert nat_trans.congr_app (F.assoc f g h) 𝒳, simp }

end lax_functor_to_Cat

namespace functor

def to_lax (F : C ⥤ Cat) : lax_functor_to_Cat C :=
{ to_prefunctor := F.to_prefunctor,
  map_id := λ X, eq_to_hom (F.map_id X),
  map_comp := λ _ _ _ f g, eq_to_hom (F.map_comp f g) }

end functor

variable (C)

structure pseudofunctor_to_Cat extends lax_functor_to_Cat C :=
(map_id_iso : ∀ X, is_iso (map_id X))
(map_comp_iso : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z), is_iso (map_comp f g))

variable (G : pseudofunctor_to_Cat C)

instance (X : C) : is_iso (G.map_id X) := G.map_id_iso X

instance {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) : is_iso (G.map_comp f g) := G.map_comp_iso f g

end category_theory

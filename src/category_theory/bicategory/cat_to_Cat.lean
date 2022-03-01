import category_theory.category.Cat
import category_theory.bicategory.locally_discrete
import category_theory.bicategory.functor_bicategory

universes v' u' v u

namespace category_theory

variables {C : Type u} [category.{v} C]

section
variable (F : oplax_functor (locally_discrete C) Cat.{v' u'})

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

end

variable (F : prefunctor C Cat)

/-- The type of dependent functors from a category `C` to a family of categories indexed
  by `C` specified by a `oplax_functor` from `locally_discrete C` to `Cat`. For `C` an opposite
  category, this is the type of dependent presheaves. -/
structure dfunctor :=
(obj (X : C) : F.obj X)
(map {X Y : C} (f : X ⟶ Y) : (F.map f).obj (obj X) ⟶ obj Y)

variable {F}
@[ext]
structure dnat_trans (G₁ G₂ : dfunctor F) :=
(app (X : C) : G₁.obj X ⟶ G₂.obj X)
(naturality' : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), G₁.map f ≫ app Y = (F.map f).map (app X) ≫ G₂.map f
  . obviously)

namespace dnat_trans

/-- `nat_trans.id F` is the identity natural transformation on a functor `F`. -/
def id (G : dfunctor F) : dnat_trans G G :=
{ app := λ X, 𝟙 (G.obj X) }

section
variables {G₁ G₂ G₃ : dfunctor F}

@[simps]
def vcomp (α : dnat_trans G₁ G₂) (β : dnat_trans G₂ G₃) : dnat_trans G₁ G₃ :=
{ app := λ X, α.app X ≫ β.app X,
  naturality' := λ X Y f, by
  { rw [←category.assoc, α.naturality', category.assoc, β.naturality'], simp } }

instance : category (dfunctor F) :=
{ hom := dnat_trans,
  id := id,
  comp := λ _ _ _, vcomp,
  id_comp' := λ X Y f, by { ext, apply category.id_comp },
  comp_id' := λ X Y f, by { ext, apply category.comp_id },
  assoc' := λ X Y Z W f g h, by { ext, apply category.assoc } }
end

section
variables {D : Type*} [category D] (G₁ G₂ : prefunctor C D)
@[ext]
structure pre_nat_trans :=
(app (X : C) : G₁.obj X ⟶ G₂.obj X)
(naturality' : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), G₁.map f ≫ app Y = app X ≫ G₂.map f . obviously)

instance : category (prefunctor C D) :=
{ hom := pre_nat_trans,
  id := λ X, { app := λ _, 𝟙 _ },
  comp := λ _ _ _ α β, { app := λ X, α.app X ≫ β.app X,
    naturality' := λ _ _ _, by
      { rw [←category.assoc, α.naturality', category.assoc, β.naturality'], simp } },
  id_comp' := λ X Y f, by { ext, apply category.id_comp },
  comp_id' := λ X Y f, by { ext, apply category.comp_id },
  assoc' := λ X Y Z W f g h, by { ext, apply category.assoc } }

end

def dfunctor_oplax_functor : prefunctor C Cat ⥤ Cat :=
{ obj := λ F, ⟨dfunctor F⟩,
  map := λ F₁ F₂ α,
  { obj := λ G,
    { obj := λ X, (α.app X).obj (G.obj X),
      map := λ X Y f, eq_to_hom
        (by { change _ = (F₁.map f ≫ α.app Y).obj _, rw α.naturality', refl }) ≫
        (α.app Y).map (G.map f) },
    map := λ G₁ G₂ β, by { dsimp,  } },
}

end dnat_trans

/- TODO: define category structure
   Show category of O-modules is isomorphic to such a category
   (need to use composition of oplax functors).
   Notion of sheaves when `Cᵒᵖ` has a grothendieck topology
   Construct oplax functor from `F : oplax_functor C Cat` to `dfunctor F`.
   Show the grothendieck construction associated to this oplax functor is isomorphic
   to the category of functors from `C` to grothendieck applied to `𝟭 _ : Cat ⥤ Cat`...!
-/

end category_theory

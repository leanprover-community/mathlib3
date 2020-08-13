import category_theory.limits.limits
import category_theory.punit
import category_theory.comma
import category_theory.connected

universes v u

namespace category_theory
open category_theory.limits

variables {C : Type v} [small_category C]
variables {D : Type v} [small_category D]

def final (F : C ⥤ D) : Type (v+1) :=
Π (d : D), connected (comma (functor.from_punit d) F)

attribute [class] final

namespace final

variables (F : C ⥤ D) [ℱ : final F]
include ℱ

instance (d : D) : inhabited (comma (functor.from_punit d) F) := (‹final F› d).to_inhabited

variables {E : Type u} [category.{v} E] (G : D ⥤ E)

def lift (d : D) : C :=
(default (comma (functor.from_punit d) F)).right

def hom_to_lift (d : D) : d ⟶ F.obj (lift F d) :=
(default (comma (functor.from_punit d) F)).hom

def extend_cocone (c : cocone (F ⋙ G)) : cocone G :=
{ X := c.X,
  ι :=
  { app := λ X,
    begin
      have := G.map (hom_to_lift F X),
      exact this ≫ c.ι.app _,
    end,
    naturality' := λ X Y f,
    begin
      dsimp, simp,
    end }}

@[priority 100]
instance comp_has_colimit [has_colimit G] :
  has_colimit (F ⋙ G) :=
{ cocone := (colimit.cocone G).whisker F,
  is_colimit :=
  { desc := λ s, begin simp, sorry, end }, }

instance colimit_pre_is_iso {E : Type u} [category.{v} E] (G : D ⥤ E) [has_colimit G] :
  is_iso (colimit.pre G F) :=
sorry

@[priority 10]
instance has_colimit_of_comp {E : Type u} [category.{v} E] (G : D ⥤ E) [has_colimit (F ⋙ G)] :
  has_colimit G :=
{ cocone :=
  { X := colimit (F ⋙ G),
    ι :=
    { app := λ X,
      begin
        simp,
        have : comma (functor.from_punit X) F := default _,
        have := this.hom, simp at this,
        transitivity,
        exact G.map this,
        apply colimit.ι (F ⋙ G),
      end,
      naturality' := sorry, } },
  is_colimit := sorry, }

instance colimit_pre_is_iso' {E : Type u} [category.{v} E] (G : D ⥤ E) [has_colimit (F ⋙ G)] :
  is_iso (colimit.pre G F) :=
sorry


end final

end category_theory

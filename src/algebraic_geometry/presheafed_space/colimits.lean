import algebraic_geometry.presheafed_space
import topology.Top.limits

universes v u

open category_theory
open category_theory.limits
open Top
open topological_space
open algebraic_geometry
open opposite

variables {C : Type u} [𝒞 : category.{v+1} C] [has_limits.{v} C] {J : Type v} [small_category J]
include 𝒞

namespace algebraic_geometry.PresheafedSpace

def colimit_to_Top (F : J ⥤ PresheafedSpace.{v} C) : Top.{v} := colimit (F ⋙ PresheafedSpace.forget)

def pushforward_to_colimit (F : J ⥤ PresheafedSpace.{v} C) : J ⥤ ((colimit_to_Top F).presheaf C)ᵒᵖ :=
{ obj := λ j, op ((colimit.ι (F ⋙ PresheafedSpace.forget) j) _* (F.obj j).𝒪),
  map := λ j j' f,
  begin
    have g := presheaf.pushforward_map (colimit.ι (F ⋙ PresheafedSpace.forget) j') (F.map f).c ≫
                (presheaf.pushforward.comp _ _ _).inv ≫
                (presheaf.pushforward_eq (limits.colimit.w (F ⋙ PresheafedSpace.forget) _) _).hom,
    exact g.op
  end,
  map_id' := begin intros, dsimp, sorry end,
  map_comp' := sorry }

@[simp] lemma pushforward_to_colimit_obj (F : J ⥤ PresheafedSpace.{v} C) (j) :
  (pushforward_to_colimit F).obj j = op ((colimit.ι (F ⋙ PresheafedSpace.forget) j) _* (F.obj j).𝒪) := rfl

def colimit (F : J ⥤ PresheafedSpace.{v} C) : PresheafedSpace.{v} C :=
{ to_Top := colimit_to_Top F,
  𝒪 := limit (pushforward_to_colimit F).left_op }

@[simp] lemma colimit_𝒪 (F : J ⥤ PresheafedSpace.{v} C) :
  (colimit F).𝒪 = limit (pushforward_to_colimit F).left_op := rfl

def colimit_cocone_ι (F : J ⥤ PresheafedSpace.{v} C) (j : J) : F.obj j ⟶ colimit F :=
{ f := (colimit.ι (F ⋙ PresheafedSpace.forget) j),
  c := limit.π ((pushforward_to_colimit F).left_op) (op j) }

@[simp] lemma colimit_cocone_ι_c (F : J ⥤ PresheafedSpace.{v} C) (j : J) :
  (colimit_cocone_ι F j).c = limit.π ((pushforward_to_colimit F).left_op) (op j) := rfl

def colimit_cocone (F : J ⥤ PresheafedSpace.{v} C) : cocone F :=
{ X := colimit F,
  ι :=
  { app := λ j, colimit_cocone_ι F j,
    naturality' := λ j j f, begin dsimp, ext, dsimp, simp, sorry, sorry end } }

@[simp] lemma colimit_cocone_X (F : J ⥤ PresheafedSpace.{v} C) :
  (colimit_cocone F).X = colimit F := rfl

instance is_colimit (F : J ⥤ PresheafedSpace.{v} C) : is_colimit (colimit_cocone F) :=
{ desc := λ s,
  { f := colimit.desc (F ⋙ PresheafedSpace.forget) (PresheafedSpace.forget.map_cocone s),
    c :=
    { app := λ U, limit.lift.{v} ((functor.flip (functor.left_op (pushforward_to_colimit F))).obj
         (op ((opens.map (colimit.desc (F ⋙ PresheafedSpace.forget) (functor.map_cocone PresheafedSpace.forget s))).obj
               (unop U))))
      { X := ((s.X).𝒪).obj U,
        π :=
        { app := λ j, begin op_induction j, dsimp, erw [←opens.map_comp_obj, colimit.ι_desc, functor.map_cocone_ι], exact (s.ι.app j).c.app U, end,
          naturality' := sorry }},
      naturality' := sorry } },
  fac' := sorry,
  uniq' := sorry }

instance : has_colimits.{v} (PresheafedSpace.{v} C) :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F,
    { cocone := colimit_cocone F } } }

end algebraic_geometry.PresheafedSpace

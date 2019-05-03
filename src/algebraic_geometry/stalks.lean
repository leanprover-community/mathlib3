import algebraic_geometry.presheafed_space
import category_theory.instances.Top.open_nhds
import category_theory.instances.Top.stalks
import category_theory.limits.limits

universes v u v' u'

open category_theory
open category_theory.instances
open category_theory.limits
open algebraic_geometry
open topological_space

variables {C : Type u} [𝒞 : category.{v+1} C] [has_colimits.{v} C]
include 𝒞

open category_theory.instances.Top.presheaf

namespace algebraic_geometry.PresheafedSpace

def stalk (F : PresheafedSpace.{v} C) (x : F.X.α) : C := F.𝒪.stalk x

def stalk_map {F G : PresheafedSpace.{v} C} (α : F ⟶ G) (x : F.X) : G.stalk (α.f x) ⟶ F.stalk x :=
(stalk_functor C (α.f x)).map (α.c) ≫ F.𝒪.stalk_pushforward C α.f x

namespace stalk_map

@[simp] lemma id (F : PresheafedSpace.{v} C) (x : F.X) : stalk_map (𝟙 F) x = 𝟙 (F.stalk x) :=
begin
  dsimp [stalk_map],
  simp only [PresheafedSpace.id_c, functor.map_comp, stalk_pushforward.id, category.assoc],
  rw [←category_theory.functor.map_comp, ←category_theory.functor.map_comp],
  convert (stalk_functor C x).map_id F.𝒪,
  ext U,
  op_induction U,
  dsimp,
  simp only [pushforward.id_hom_app, category.id_comp, opens.op_map_id_obj, opens.map_id_obj],
  rw [←category_theory.functor.map_comp,
      eq_to_hom_op_comp, category_theory.functor.map_id],
end
.

@[simp] lemma comp {F G H : PresheafedSpace.{v} C} (α : F ⟶ G) (β : G ⟶ H) (x : F.X) :
  stalk_map (α ≫ β) x =
    (stalk_map β (α.f x) : H.stalk (β.f (α.f x)) ⟶ G.stalk (α.f x)) ≫
    (stalk_map α x : G.stalk (α.f x) ⟶ F.stalk x) :=
begin
  dsimp [stalk, stalk_map, stalk_functor, stalk_pushforward, comp_c],
  ext U,
  op_induction U,
  cases U,
  cases U_val,
  simp only [colim.ι_map_assoc,
    whisker_left.app,
    colimit.ι_pre_assoc,
    colimit.ι_pre,
    whisker_right.app,
    functor.map_comp,
    category.assoc],
  -- These are all simp lemmas that unfortunately don't fire:
  erw [category_theory.functor.map_id, category_theory.functor.map_id,
    category.id_comp, category.id_comp],
  refl,
end
end stalk_map

end algebraic_geometry.PresheafedSpace

import category_theory.instances.Top.open_nhds
import category_theory.instances.Top.presheaf
import category_theory.limits.limits

universes v u v' u'

open category_theory
open category_theory.instances
open category_theory.instances.Top
open category_theory.limits
open topological_space

lemma eq_to_hom_op_comp  {C : Sort u} [𝒞 : category.{v} C] {X Y : C} (h : X = Y) (k : op X = op Y) :
  (eq_to_hom h).op ≫ (eq_to_hom k) = 𝟙 (op Y) :=
by simp

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞

variables [has_colimits.{v} C]

variables {X Y Z : Top.{v}}

namespace category_theory.instances.Top.presheaf

variables (C)
/-- Stalks are functorial with respect to morphisms of presheaves over a fixed `X`. -/
def stalk_functor (x : X) : X.presheaf C ⥤ C :=
((whiskering_left _ _ C).obj (open_nhds.inclusion x).op) ⋙ colim

variables {C}

/--
The stalk of a presheaf `F` at a point `x` is calculated as the colimit of the functor
nbhds x ⥤ opens F.X ⥤ C
-/
def stalk (ℱ : X.presheaf C) (x : X) : C :=
(stalk_functor C x).obj ℱ -- -- colimit (nbhds_inclusion x ⋙ ℱ)

@[simp] lemma stalk_functor_obj (ℱ : X.presheaf C) (x : X) : (stalk_functor C x).obj ℱ = ℱ.stalk x := rfl

variables (C)

def stalk_pushforward (f : X ⟶ Y) (ℱ : X.presheaf C) (x : X) : (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
begin
  -- This is a hack; Lean doesn't like to elaborate the term written directly.
  transitivity,
  swap,
  exact colimit.pre _ (open_nhds.map f x).op,
  exact colim.map (whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) ℱ),
end

namespace stalk_pushforward
@[simp] def id (ℱ : X.presheaf C) (x : X) :
  ℱ.stalk_pushforward C (𝟙 X) x = (stalk_functor C x).map ((pushforward.id ℱ).hom) :=
begin
  dsimp [stalk_pushforward, stalk_functor],
  ext U,
  op_induction U,
  tidy,
end

@[simp] def comp (ℱ : X.presheaf C) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  ℱ.stalk_pushforward C (f ≫ g) x =
  ((f _* ℱ).stalk_pushforward C g (f x)) ≫ (ℱ.stalk_pushforward C f x) :=
begin
  dsimp [stalk_pushforward, stalk_functor],
  ext U,
  op_induction U,
  cases U,
  cases U_val,
  simp only [colim.ι_map_assoc, colimit.ι_pre_assoc, colimit.ι_pre,
             whisker_right.app, category.assoc],
  -- These are simp lemmas which unfortunately don't fire:
  erw [category_theory.functor.map_id, category.id_comp, category.id_comp],
end

end stalk_pushforward
end category_theory.instances.Top.presheaf

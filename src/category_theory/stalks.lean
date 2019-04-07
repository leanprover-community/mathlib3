import category_theory.presheaf
import category_theory.instances.Top.open_nhds
import category_theory.limits.limits

universes v u v' u'

open category_theory
open category_theory.instances
open category_theory.limits
open topological_space

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞

variables [has_colimits.{v} C]

variables {X : Top.{v}}

namespace category_theory.presheaf_on_space

variables (C)
/-- Stalks are functorial with respect to morphisms of presheaves over a fixed `X`. -/
def stalk_functor (x : X) : presheaf_on_space C X ⥤ C :=
((whiskering_left _ _ C).obj (open_nhds.inclusion x).op) ⋙ colim

variables {C}

/--
The stalk of a presheaf `F` at a point `x` is calculated as the colimit of the functor
nbhds x ⥤ opens F.X ⥤ C
-/
def stalk (ℱ : presheaf_on_space C X) (x : X) : C :=
(stalk_functor C x).obj ℱ -- -- colimit (nbhds_inclusion x ⋙ ℱ)

@[simp] lemma stalk_functor_obj (ℱ : presheaf_on_space C X) (x : X) : (stalk_functor C x).obj ℱ = ℱ.stalk x := rfl

variables (C)
variables {Y : Top.{v}}

/--
Warning: we are accummulating some abstract nonsense debt here.
If you describe the stalk as a filtered colimit (i.e. some quotient of the disjoint union of sections near x)
this map should be pretty close to invisible. Right now it's ... a bit opaque.
-/
def stalk_pushforward (f : X ⟶ Y) (ℱ : presheaf_on_space C X) (x : X) : (ℱ.pushforward f).stalk (f x) ⟶ ℱ.stalk x :=
begin
  transitivity,
  swap,
  exact colimit.pre _ (open_nhds.map f x).op,
  exact colim.map (whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) ℱ),
end

@[simp] def stalk_pushforward_id (ℱ : presheaf_on_space C X) (x : X) :
  ℱ.stalk_pushforward C (𝟙 X) x = (stalk_functor C x).map ((presheaf_on_space.pushforward.id ℱ).hom) :=
begin
  dsimp [stalk_pushforward, stalk_functor],
  tidy,
  erw category_theory.functor.map_id,
  erw category.id_comp,
  dsimp [opposite] at j,
  cases j,
  cases j_val,
  dsimp,
  erw category_theory.functor.map_id,
  erw category.id_comp,
  refl,
end

variables {Z : Top.{v}}
@[simp] def stalk_pushforward_comp (ℱ : presheaf_on_space C X) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  ℱ.stalk_pushforward C (f ≫ g) x =
  begin
    have a := ℱ.stalk_pushforward C f x,
    have b := (ℱ.pushforward f).stalk_pushforward C g (f x),
    exact b ≫ a,
  end :=
begin
  dsimp [stalk_pushforward, stalk_functor],
  tidy,
  erw category_theory.functor.map_id,
  erw category.id_comp,
  erw category.id_comp,
end

end category_theory.presheaf_on_space

open category_theory.presheaf_on_space

namespace category_theory.PresheafedSpace

def stalk (F : PresheafedSpace.{v} C) (x : F.X.α) : C := F.𝒪.stalk x

def stalk_map {F G : PresheafedSpace.{v} C} (α : F ⟶ G) (x : F.X) : G.stalk (α.f x) ⟶ F.stalk x :=
begin
  transitivity,
  have q := (stalk_functor C (α.f x)).map (α.c),
  exact q,
  have p := F.𝒪.stalk_pushforward C α.f x,
  exact p,
end

namespace stalk_map

-- The next two proofs are grotesque.

@[simp] lemma id (F : PresheafedSpace.{v} C) (x : F.X) : stalk_map (𝟙 F) x = 𝟙 (F.stalk x) :=
begin
  dsimp [stalk_map],
  simp [id_c],
  rw ←category_theory.functor.map_comp,
  rw ←category_theory.functor.map_comp,
  convert (stalk_functor C x).map_id F.𝒪,
  tidy,
  rw ←category_theory.functor.map_comp,
  rw ←category_theory.functor.map_id,
  rw [eq_to_hom_op_comp],
  refl,
end
.

@[simp] lemma comp {F G H : PresheafedSpace.{v} C} (α : F ⟶ G) (β : G ⟶ H) (x : F.X) :
  stalk_map (α ≫ β) x =
    (stalk_map β (α.f x) : H.stalk (β.f (α.f x)) ⟶ G.stalk (α.f x)) ≫
    (stalk_map α x : G.stalk (α.f x) ⟶ F.stalk x) :=
begin
  dsimp [stalk, stalk_map, stalk_functor, stalk_pushforward, comp_c],
  tidy,
  erw category_theory.functor.map_id,
  erw category_theory.functor.map_id,
  erw category.id_comp,
  erw category.id_comp,
  refl,
end
end stalk_map

end category_theory.PresheafedSpace

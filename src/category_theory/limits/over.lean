/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import category_theory.over
import category_theory.adjunction.opposites
import category_theory.limits.preserves.basic
import category_theory.limits.shapes.pullbacks
import category_theory.limits.creates

/-!
# Limits and colimits in the over and under categories

Show that the forgetful functor `forget X : over X ⥤ C` creates colimits, and hence `over X` has
any colimits that `C` has (as well as the dual that `forget X : under X ⟶ C` creates limits).

Note that the folder `category_theory.limits.shapes.constructions.over` further shows that
`forget X : over X ⥤ C` creates connected limits (so `over X` has connected limits), and that
`over X` has `J`-indexed products if `C` has `J`-indexed wide pullbacks.

TODO: If `C` has binary products, then `forget X : over X ⥤ C` has a right adjoint.
-/
noncomputable theory

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

open category_theory category_theory.limits

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C]
variable {X : C}

namespace category_theory.functor

/-- We can interpret a functor `F` into the category of arrows with codomain `X` as a cocone over
    the diagram given by the domains of the arrows in the image of `F` such that the apex of the
    cocone is `X`. -/
@[simps] def to_cocone (F : J ⥤ over X) : cocone (F ⋙ over.forget X) :=
{ X := X,
  ι := { app := λ j, (F.obj j).hom } }

/-- We can interpret a functor `F` into the category of arrows with domain `X` as a cone over the
    diagram given by the codomains of the arrows in the image of `F` such that the apex of the cone
    is `X`. -/
@[simps] def to_cone (F : J ⥤ under X) : cone (F ⋙ under.forget X) :=
{ X := X,
  π := { app := λ j, (F.obj j).hom } }

end category_theory.functor

namespace category_theory.over

instance : reflects_colimits (forget X) :=
{ reflects_colimits_of_shape := λ J 𝒥₁,
  { reflects_colimit := λ F,
    { reflects := λ c t, by exactI
      { desc := λ s, hom_mk (t.desc ((forget X).map_cocone s)) $ t.hom_ext $
                         λ j, by { rw t.fac_assoc, exact ((s.ι.app j).w).trans (c.ι.app j).w.symm },
        fac' := λ s j, over_morphism.ext (t.fac _ j),
        uniq' :=
          λ s m w, over_morphism.ext $
          t.uniq ((forget X).map_cocone s) m.left (λ j, congr_arg comma_morphism.left (w j)) } } } }

instance : creates_colimits (forget X) :=
{ creates_colimits_of_shape := λ J 𝒥₁, by exactI
  { creates_colimit := λ K,
    { lifts := λ c t,
      { lifted_cocone :=
        { X := mk (t.desc K.to_cocone),
          ι :=
          { app := λ j, hom_mk (c.ι.app j),
            naturality' := λ j j' f, over_morphism.ext (c.ι.naturality f) } },
        valid_lift := cocones.ext (iso.refl _) (λ j, category.comp_id _) } } } }

instance has_colimit {F : J ⥤ over X} [has_colimit (F ⋙ forget X)] : has_colimit F :=
has_colimit_of_created _ (forget X)

instance has_colimits_of_shape [has_colimits_of_shape J C] :
  has_colimits_of_shape J (over X) :=
{}

instance has_colimits [has_colimits C] : has_colimits (over X) := {}

-- We can automatically infer that the forgetful functor preserves colimits
example [has_colimits C] : preserves_colimits (forget X) := infer_instance

section
variables [has_pullbacks C]

open tactic

/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `over Y ⥤ over X`,
by pulling back a morphism along `f`. -/
@[simps]
def pullback {X Y : C} (f : X ⟶ Y) : over Y ⥤ over X :=
{ obj := λ g, over.mk (pullback.snd : pullback g.hom f ⟶ X),
  map := λ g h k,
    over.hom_mk
      (pullback.lift (pullback.fst ≫ k.left) pullback.snd (by simp [pullback.condition]))
      (by tidy) }

/-- `over.map f` is left adjoint to `over.pullback f`. -/
def map_pullback_adj {A B : C} (f : A ⟶ B) :
  over.map f ⊣ pullback f :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ g h,
  { to_fun := λ X, over.hom_mk (pullback.lift X.left g.hom (over.w X)) (pullback.lift_snd _ _ _),
    inv_fun := λ Y,
    begin
      refine over.hom_mk _ _,
      refine Y.left ≫ pullback.fst,
      dsimp,
      rw [← over.w Y, category.assoc, pullback.condition, category.assoc], refl,
    end,
    left_inv := λ X, by { ext, dsimp, simp, },
    right_inv := λ Y, begin
      ext, dsimp,
      simp only [pullback.lift_fst],
      dsimp,
      rw [pullback.lift_snd, ← over.w Y],
      refl,
    end } }

/-- pullback (𝟙 A) : over A ⥤ over A is the identity functor. -/
def pullback_id {A : C} : pullback (𝟙 A) ≅ 𝟭 _ :=
adjunction.right_adjoint_uniq
  (map_pullback_adj _)
  (adjunction.id.of_nat_iso_left over.map_id.symm)

/-- pullback commutes with composition (up to natural isomorphism). -/
def pullback_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
adjunction.right_adjoint_uniq
  (map_pullback_adj _)
  (((map_pullback_adj _).comp _ _ (map_pullback_adj _)).of_nat_iso_left
    (over.map_comp _ _).symm)

instance pullback_is_right_adjoint {A B : C} (f : A ⟶ B) :
  is_right_adjoint (pullback f) :=
⟨_, map_pullback_adj f⟩

end

end category_theory.over

namespace category_theory.under

instance : reflects_limits (forget X) :=
{ reflects_limits_of_shape := λ J 𝒥₁,
  { reflects_limit := λ F,
    { reflects := λ c t, by exactI
      { lift := λ s, hom_mk (t.lift ((forget X).map_cone s)) $ t.hom_ext $ λ j,
                    by { rw [category.assoc, t.fac], exact (s.π.app j).w.symm.trans (c.π.app j).w },
        fac' := λ s j, under_morphism.ext (t.fac _ j),
        uniq' :=
          λ s m w, under_morphism.ext $
          t.uniq ((forget X).map_cone s) m.right (λ j, congr_arg comma_morphism.right (w j)) } } } }

instance : creates_limits (forget X) :=
{ creates_limits_of_shape := λ J 𝒥₁, by exactI
  { creates_limit := λ K,
    { lifts := λ c t,
      { lifted_cone :=
        { X := mk (t.lift K.to_cone),
          π :=
          { app := λ j, hom_mk (c.π.app j),
            naturality' := λ j j' f, under_morphism.ext (c.π.naturality f) } },
        valid_lift := cones.ext (iso.refl _) (λ j, (category.id_comp _).symm) } } } }

instance has_limit {F : J ⥤ under X} [has_limit (F ⋙ forget X)] : has_limit F :=
has_limit_of_created F (forget X)

instance has_limits_of_shape [has_limits_of_shape J C] :
  has_limits_of_shape J (under X) :=
{}

instance has_limits [has_limits C] : has_limits (under X) := {}

-- We can automatically infer that the forgetful functor preserves limits
example [has_limits C] : preserves_limits (forget X) := infer_instance


section
variables [has_pushouts C]

/-- When `C` has pushouts, a morphism `f : X ⟶ Y` induces a functor `under X ⥤ under Y`,
by pushing a morphism forward along `f`. -/
@[simps]
def pushout {X Y : C} (f : X ⟶ Y) : under X ⥤ under Y :=
{ obj := λ g, under.mk (pushout.inr : Y ⟶ pushout g.hom f),
  map := λ g h k,
    under.hom_mk
      (pushout.desc (k.right ≫ pushout.inl) pushout.inr (by { simp [←pushout.condition], }))
      (by tidy) }

end

end category_theory.under

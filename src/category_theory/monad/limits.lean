/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.monad.adjunction
import category_theory.adjunction.limits

namespace category_theory
open category
open category_theory.limits

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace monad

variables {C : Type u₁} [category.{v₁} C]
variables {T : C ⥤ C} [monad T]

variables {J : Type v₁} [small_category J]

namespace forget_creates_limits

variables (D : J ⥤ algebra T) (c : cone (D ⋙ forget T)) (t : is_limit c)

/-- (Impl) The natural transformation used to define the new cone -/
@[simps] def γ : (D ⋙ forget T ⋙ T) ⟶ (D ⋙ forget T) := { app := λ j, (D.obj j).a }

/-- (Impl) This new cone is used to construct the algebra structure -/
@[simps] def new_cone : cone (D ⋙ forget T) :=
{ X := T.obj c.X,
  π := (functor.const_comp _ _ T).inv ≫ whisker_right c.π T ≫ (γ D) }

/-- The algebra structure which will be the apex of the new limit cone for `D`. -/
@[simps] def cone_point : algebra T :=
{ A := c.X,
  a := t.lift (new_cone D c),
  unit' :=
  begin
    apply t.hom_ext,
    intro j,
    erw [category.assoc, t.fac (new_cone D c), id_comp],
    dsimp,
    erw [id_comp, ← category.assoc, ← (η_ T).naturality, functor.id_map, category.assoc,
         (D.obj j).unit, comp_id],
  end,
  assoc' :=
  begin
    apply t.hom_ext,
    intro j,
    rw [category.assoc, category.assoc, t.fac (new_cone D c)],
    dsimp,
    erw id_comp,
    slice_lhs 1 2 {rw ← (μ_ T).naturality},
    slice_lhs 2 3 {rw (D.obj j).assoc},
    slice_rhs 1 2 {rw ← T.map_comp},
    rw t.fac (new_cone D c),
    dsimp,
    erw [id_comp, T.map_comp, category.assoc]
  end }

/-- (Impl) Construct the lifted cone in `algebra T` which will be limiting. -/
@[simps] def lifted_cone : cone D :=
{ X := cone_point D c t,
  π := { app := λ j, { f := c.π.app j },
         naturality' := λ X Y f, by { ext1, dsimp, erw c.w f, simp } } }

/-- (Impl) Prove that the lifted cone is limiting. -/
@[simps]
def lifted_cone_is_limit : is_limit (lifted_cone D c t) :=
{ lift := λ s,
  { f := t.lift ((forget T).map_cone s),
    h' :=
    begin
      apply t.hom_ext, intro j,
      have := t.fac ((forget T).map_cone s),
      slice_rhs 2 3 {rw t.fac ((forget T).map_cone s) j},
      dsimp,
      slice_lhs 2 3 {rw t.fac (new_cone D c) j},
      dsimp,
      rw category.id_comp,
      slice_lhs 1 2 {rw ← T.map_comp},
      rw t.fac ((forget T).map_cone s) j,
      exact (s.π.app j).h
    end },
  uniq' := λ s m J,
  begin
    ext1,
    apply t.hom_ext,
    intro j,
    simpa [t.fac (functor.map_cone (forget T) s) j] using congr_arg algebra.hom.f (J j),
  end }

end forget_creates_limits

-- Theorem 5.6.5 from [Riehl][riehl2017]
/-- The forgetful functor from the Eilenberg-Moore category creates limits. -/
instance forget_creates_limits : creates_limits (forget T) :=
{ creates_limits_of_shape := λ J 𝒥, by exactI
  { creates_limit := λ D,
    creates_limit_of_reflects_iso (λ c t,
    { lifted_cone := forget_creates_limits.lifted_cone D c t,
      valid_lift := cones.ext (iso.refl _) (λ j, (id_comp _).symm),
      makes_limit := forget_creates_limits.lifted_cone_is_limit _ _ _ } ) } }

/-- `D ⋙ forget T` has a limit, then `D` has a limit. -/
def has_limit_of_comp_forget_has_limit (D : J ⥤ algebra T) [has_limit (D ⋙ forget T)] : has_limit D :=
has_limit_of_created D (forget T)

namespace forget_creates_colimits

-- Let's hide the implementation details in a namespace
variables {D : J ⥤ algebra T} (c : cocone (D ⋙ forget T)) (t : is_colimit c)

-- We have a diagram D of shape J in the category of algebras, and we assume that we are given a
-- colimit for its image D ⋙ forget T under the forgetful functor, say its apex is L.

-- We'll construct a colimiting coalgebra for D, whose carrier will also be L.
-- To do this, we must find a map TL ⟶ L. Since T preserves colimits, TL is also a colimit.
-- In particular, it is a colimit for the diagram `(D ⋙ forget T) ⋙ T`
-- so to construct a map TL ⟶ L it suffices to show that L is the apex of a cocone for this diagram.
-- In other words, we need a natural transformation from const L to `(D ⋙ forget T) ⋙ T`.
-- But we already know that L is the apex of a cocone for the diagram `D ⋙ forget T`, so it
-- suffices to give a natural transformation `((D ⋙ forget T) ⋙ T) ⟶ (D ⋙ forget T)`:

/--
(Impl)
The natural transformation given by the algebra structure maps, used to construct a cocone `c` with
apex `colimit (D ⋙ forget T)`.
 -/
@[simps] def γ : ((D ⋙ forget T) ⋙ T) ⟶ (D ⋙ forget T) := { app := λ j, (D.obj j).a }

/--
(Impl)
A cocone for the diagram `(D ⋙ forget T) ⋙ T` found by composing the natural transformation `γ`
with the colimiting cocone for `D ⋙ forget T`.
-/
@[simps]
def new_cocone : cocone ((D ⋙ forget T) ⋙ T) :=
{ X := c.X,
  ι := γ ≫ c.ι }

variable [preserves_colimits_of_shape J T]

/--
(Impl)
Define the map `λ : TL ⟶ L`, which will serve as the structure of the coalgebra on `L`, and
we will show is the colimiting object. We use the cocone constructed by `c` and the fact that
`T` preserves colimits to produce this morphism.
-/
@[reducible]
def lambda : (functor.map_cocone T c).X ⟶ c.X :=
(preserves_colimit.preserves t).desc (new_cocone c)

/-- (Impl) The key property defining the map `λ : TL ⟶ L`. -/
lemma commuting (j : J) :
T.map (c.ι.app j) ≫ lambda c t = (D.obj j).a ≫ c.ι.app j :=
is_colimit.fac (preserves_colimit.preserves t) (new_cocone c) j

/--
(Impl)
Construct the colimiting algebra from the map `λ : TL ⟶ L` given by `lambda`. We are required to
show it satisfies the two algebra laws, which follow from the algebra laws for the image of `D` and
our `commuting` lemma.
-/
@[simps] def cocone_point :
algebra T :=
{ A := c.X,
  a := lambda c t,
  unit' :=
  begin
    apply t.hom_ext,
    intro j,
    erw [comp_id, ← category.assoc, (η_ T).naturality, category.assoc, commuting, ← category.assoc],
    erw algebra.unit, apply id_comp
  end,
  assoc' :=
  begin
    apply is_colimit.hom_ext (preserves_colimit.preserves (preserves_colimit.preserves t)),
    intro j,
    erw [← category.assoc, nat_trans.naturality (μ_ T), ← functor.map_cocone_ι, category.assoc,
         is_colimit.fac _ (new_cocone c) j],
    rw ← category.assoc,
    erw [← functor.map_comp, commuting],
    dsimp,
    erw [← category.assoc, algebra.assoc, category.assoc, functor.map_comp, category.assoc, commuting],
    apply_instance, apply_instance
  end }

/-- (Impl) Construct the lifted cocone in `algebra T` which will be colimiting. -/
@[simps] def lifted_cocone : cocone D :=
{ X := cocone_point c t,
  ι := { app := λ j, { f := c.ι.app j, h' := commuting _ _ _ },
         naturality' := λ A B f, by { ext1, dsimp, erw [comp_id, c.w] } } }

/-- (Impl) Prove that the lifted cocone is colimiting. -/
@[simps]
def lifted_cocone_is_colimit : is_colimit (lifted_cocone c t) :=
{ desc := λ s,
  { f := t.desc ((forget T).map_cocone s),
    h' :=
    begin
      dsimp,
      apply is_colimit.hom_ext (preserves_colimit.preserves t),
      intro j,
      rw ← category.assoc, erw ← functor.map_comp,
      erw t.fac',
      rw ← category.assoc, erw forget_creates_colimits.commuting,
      rw category.assoc, rw t.fac',
      apply algebra.hom.h,
      apply_instance
    end },
  uniq' := λ s m J, by { ext1, apply t.hom_ext, intro j, simpa using congr_arg algebra.hom.f (J j) } }

end forget_creates_colimits

open forget_creates_colimits

-- TODO: the converse of this is true as well
-- TODO: generalise to monadic functors, as for creating limits
/--
The forgetful functor from the Eilenberg-Moore category for a monad creates any colimit
which the monad itself preserves.
-/
instance forget_creates_colimits [preserves_colimits_of_shape J T] : creates_colimits_of_shape J (forget T) :=
{ creates_colimit := λ D,
  creates_colimit_of_reflects_iso $ λ c t,
  { lifted_cocone :=
    { X := cocone_point c t,
      ι :=
      { app := λ j, { f := c.ι.app j, h' := commuting _ _ _ },
        naturality' := λ A B f, by { ext1, dsimp, erw [comp_id, c.w] } } },
    valid_lift := cocones.ext (iso.refl _) (by tidy),
    makes_colimit := lifted_cocone_is_colimit _ _ } }

/--
For `D : J ⥤ algebra T`, `D ⋙ forget T` has a colimit, then `D` has a colimit provided colimits
of shape `J` are preserved by `T`.
-/
def forget_creates_colimits_of_monad_preserves
  [preserves_colimits_of_shape J T] (D : J ⥤ algebra T) [has_colimit (D ⋙ forget T)] :
has_colimit D :=
has_colimit_of_created D (forget T)


end monad

variables {C : Type u₁} [category.{v₁} C] {D : Type u₁} [category.{v₁} D]
variables {J : Type v₁} [small_category J]

instance comp_comparison_forget_has_limit
  (F : J ⥤ D) (R : D ⥤ C) [monadic_right_adjoint R] [has_limit (F ⋙ R)] :
  has_limit ((F ⋙ monad.comparison R) ⋙ monad.forget ((left_adjoint R) ⋙ R)) :=
(@has_limit_of_iso _ _ _ _ (F ⋙ R) _ _ (iso_whisker_left F (monad.comparison_forget R).symm))

instance comp_comparison_has_limit
  (F : J ⥤ D) (R : D ⥤ C) [monadic_right_adjoint R] [has_limit (F ⋙ R)] :
  has_limit (F ⋙ monad.comparison R) :=
monad.has_limit_of_comp_forget_has_limit (F ⋙ monad.comparison R)

/-- Any monadic functor creates limits. -/
def monadic_creates_limits (F : J ⥤ D) (R : D ⥤ C) [monadic_right_adjoint R] [has_limit (F ⋙ R)] :
  has_limit F :=
adjunction.has_limit_of_comp_equivalence _ (monad.comparison R)

section

/-- If C has limits then any reflective subcategory has limits -/
def has_limits_of_reflective (R : D ⥤ C) [has_limits C] [reflective R] : has_limits D :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, monadic_creates_limits F R } }

local attribute [instance] has_limits_of_reflective

-- We verify that, even jumping through these monadic hoops,
-- the limit is actually calculated in the obvious way:
example (R : D ⥤ C) [reflective R] [has_limits C] (F : J ⥤ D) :
limit F = (left_adjoint R).obj (limit (F ⋙ R)) := rfl

end
end category_theory

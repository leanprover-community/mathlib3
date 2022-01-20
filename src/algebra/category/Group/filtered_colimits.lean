/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import algebra.category.Group.basic
import algebra.category.Mon.filtered_colimits

/-!
# The forgetful functor from (commutative) (additive) groups preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ Group`.
We show that the colimit of `F ⋙ forget₂ Group Mon` (in `Mon`) carries the structure of a group,
thereby showing that the forgetful functor `forget₂ Group Mon` preserves filtered colimits. In
particular, this implies that `forget Group` preserves filtered colimits. Similarly for `AddGroup`,
`CommGroup` and `AddCommGroup`.

-/

universe v

noncomputable theory
open_locale classical

open category_theory
open category_theory.limits
open category_theory.is_filtered (renaming max → max') -- avoid name collision with `_root_.max`.

namespace Group.filtered_colimits

section

open Mon.filtered_colimits (colimit_one_eq colimit_mul_mk_eq)

-- We use parameters here, mainly so we can have the abbreviations `G` and `G.mk` below, without
-- passing around `F` all the time.
parameters {J : Type v} [small_category J] [is_filtered J] (F : J ⥤ Group.{v})

/--
The colimit of `F ⋙ forget₂ Group Mon` in the category `Mon`.
In the following, we will show that this has the structure of a group.
-/
@[to_additive "The colimit of `F ⋙ forget₂ AddGroup AddMon` in the category `AddMon`.
In the following, we will show that this has the structure of an additive group."]
abbreviation G : Mon := Mon.filtered_colimits.colimit (F ⋙ forget₂ Group Mon)

/-- The canonical projection into the colimit, as a quotient type. -/
@[to_additive "The canonical projection into the colimit, as a quotient type."]
abbreviation G.mk : (Σ j, F.obj j) → G := quot.mk (types.quot.rel (F ⋙ forget Group))

@[to_additive]
lemma G.mk_eq (x y : Σ j, F.obj j)
  (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
  G.mk x = G.mk y :=
quot.eqv_gen_sound (types.filtered_colimit.eqv_gen_quot_rel_of_rel (F ⋙ forget Group) x y h)

/-- The "unlifted" version of taking inverses in the colimit. -/
@[to_additive "The \"unlifted\" version of negation in the colimit."]
def colimit_inv_aux (x : Σ j, F.obj j) : G :=
G.mk ⟨x.1, x.2 ⁻¹⟩

@[to_additive]
lemma colimit_inv_aux_eq_of_rel (x y : Σ j, F.obj j)
  (h : types.filtered_colimit.rel (F ⋙ forget Group) x y) :
  colimit_inv_aux x = colimit_inv_aux y :=
begin
  apply G.mk_eq,
  obtain ⟨k, f, g, hfg⟩ := h,
  use [k, f, g],
  rw [monoid_hom.map_inv, monoid_hom.map_inv, inv_inj],
  exact hfg,
end

/-- Taking inverses in the colimit. See also `colimit_inv_aux`. -/
@[to_additive "Negation in the colimit. See also `colimit_neg_aux`."]
instance colimit_has_inv : has_inv G :=
{ inv := λ x, begin
   refine quot.lift (colimit_inv_aux F) _ x,
  intros x y h,
  apply colimit_inv_aux_eq_of_rel,
  apply types.filtered_colimit.rel_of_quot_rel,
  exact h,
end }

@[simp, to_additive]
lemma colimit_inv_mk_eq (x : Σ j, F.obj j) : (G.mk x) ⁻¹ = G.mk ⟨x.1, x.2 ⁻¹⟩ := rfl

@[to_additive]
instance colimit_group : group G :=
{ mul_left_inv := λ x, begin
    apply quot.induction_on x, clear x, intro x,
    cases x with j x,
    erw [colimit_inv_mk_eq, colimit_mul_mk_eq (F ⋙ forget₂ Group Mon) ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j),
      colimit_one_eq (F ⋙ forget₂ Group Mon) j],
    dsimp,
    simp only [category_theory.functor.map_id, id_apply, mul_left_inv],
  end,
  .. G.monoid,
  .. colimit_has_inv }

/-- The bundled group giving the filtered colimit of a diagram. -/
@[to_additive "The bundled additive group giving the filtered colimit of a diagram."]
def colimit : Group := Group.of G

/-- The cocone over the proposed colimit group. -/
@[to_additive "The cocone over the proposed colimit additive group."]
def colimit_cocone : cocone F :=
{ X := colimit,
  ι := { ..(Mon.filtered_colimits.colimit_cocone (F ⋙ forget₂ Group Mon)).ι } }

/-- The proposed colimit cocone is a colimit in `Group`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddGroup`."]
def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
{ desc := λ t, Mon.filtered_colimits.colimit_desc (F ⋙ forget₂ Group Mon)
    ((forget₂ Group Mon).map_cocone t),
  fac' := λ t j, monoid_hom.coe_inj $
    (types.colimit_cocone_is_colimit (F ⋙ forget Group)).fac ((forget Group).map_cocone t) j,
  uniq' := λ t m h, monoid_hom.coe_inj $
    (types.colimit_cocone_is_colimit (F ⋙ forget Group)).uniq ((forget Group).map_cocone t) m
    ((λ j, funext $ λ x, monoid_hom.congr_fun (h j) x)) }

@[to_additive forget₂_AddMon_preserves_filtered_colimits]
instance forget₂_Mon_preserves_filtered_colimits :
  preserves_filtered_colimits (forget₂ Group Mon.{v}) :=
{ preserves_filtered_colimits := λ J _ _, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit F)
      (Mon.filtered_colimits.colimit_cocone_is_colimit (F ⋙ forget₂ Group Mon.{v})) } }

@[to_additive]
instance forget_preserves_filtered_colimits : preserves_filtered_colimits (forget Group) :=
limits.comp_preserves_filtered_colimits (forget₂ Group Mon) (forget Mon)

end

end Group.filtered_colimits


namespace CommGroup.filtered_colimits

section

-- We use parameters here, mainly so we can have the abbreviation `G` below, without
-- passing around `F` all the time.
parameters {J : Type v} [small_category J] [is_filtered J] (F : J ⥤ CommGroup.{v})

/--
The colimit of `F ⋙ forget₂ CommGroup Group` in the category `Group`.
In the following, we will show that this has the structure of a _commutative_ group.
-/
@[to_additive "The colimit of `F ⋙ forget₂ AddCommGroup AddGroup` in the category `AddGroup`.
In the following, we will show that this has the structure of a _commutative_ additive group."]
abbreviation G : Group := Group.filtered_colimits.colimit (F ⋙ forget₂ CommGroup Group.{v})

@[to_additive]
instance colimit_comm_group : comm_group G :=
{ ..G.group,
  ..CommMon.filtered_colimits.colimit_comm_monoid (F ⋙ forget₂ CommGroup CommMon.{v}) }

/-- The bundled commutative group giving the filtered colimit of a diagram. -/
@[to_additive "The bundled additive commutative group giving the filtered colimit of a diagram."]
def colimit : CommGroup := CommGroup.of G

/-- The cocone over the proposed colimit commutative group. -/
@[to_additive "The cocone over the proposed colimit additive commutative group."]
def colimit_cocone : cocone F :=
{ X := colimit,
  ι := { ..(Group.filtered_colimits.colimit_cocone (F ⋙ forget₂ CommGroup Group)).ι } }

/-- The proposed colimit cocone is a colimit in `CommGroup`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddCommGroup`."]
def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
{ desc := λ t,
  (Group.filtered_colimits.colimit_cocone_is_colimit (F ⋙ forget₂ CommGroup Group.{v})).desc
    ((forget₂ CommGroup Group.{v}).map_cocone t),
  fac' := λ t j, monoid_hom.coe_inj $
    (types.colimit_cocone_is_colimit (F ⋙ forget CommGroup)).fac
    ((forget CommGroup).map_cocone t) j,
  uniq' := λ t m h, monoid_hom.coe_inj $
    (types.colimit_cocone_is_colimit (F ⋙ forget CommGroup)).uniq
    ((forget CommGroup).map_cocone t) m ((λ j, funext $ λ x, monoid_hom.congr_fun (h j) x)) }

@[to_additive forget₂_AddGroup_preserves_filtered_colimits]
instance forget₂_Group_preserves_filtered_colimits :
  preserves_filtered_colimits (forget₂ CommGroup Group.{v}) :=
{ preserves_filtered_colimits := λ J _ _, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit F)
      (Group.filtered_colimits.colimit_cocone_is_colimit (F ⋙ forget₂ CommGroup Group.{v})) } }

@[to_additive]
instance forget_preserves_filtered_colimits : preserves_filtered_colimits (forget CommGroup) :=
limits.comp_preserves_filtered_colimits (forget₂ CommGroup Group) (forget Group)

end

end CommGroup.filtered_colimits

/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import algebra.category.Group.basic
import algebra.category.Mon.filtered_colimits
import category_theory.limits.concrete_category
import category_theory.limits.preserves.filtered

/-!
# The forgetful functor `Group ⥤ Type` preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ Group`.
We then construct a monoid structure on the colimit of `F ⋙ forget Group`, thereby showing that
the forgetful functor `forget Group` preserves filtered colimits.

-/

universe v

noncomputable theory
open_locale classical

open category_theory
open category_theory.limits
open category_theory.is_filtered (renaming max → max') -- avoid name collision with `_root_.max`.

namespace Group.filtered_colimits

section

open Mon.filtered_colimits (colimit_mul colimit_one colimit_mul_eq' colimit_one_eq')

parameters {J : Type v} [small_category J] [is_filtered J] (F : J ⥤ Group.{v})

@[to_additive]
abbreviation G : Mon := Mon.filtered_colimits.colimit (F ⋙ forget₂ Group Mon)

@[to_additive]
abbreviation G.mk : (Σ j, F.obj j) → G := quot.mk (types.quot.rel (F ⋙ forget Group))

@[to_additive]
instance group_obj (j) : group (((F ⋙ forget₂ Group Mon.{v}) ⋙ forget Mon).obj j) :=
by { change group (F.obj j), apply_instance }

@[to_additive]
lemma G.mk_eq (x y : Σ j, F.obj j)
  (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
  G.mk x = G.mk y :=
quot.eqv_gen_sound (types.filtered_colimit.eqv_gen_quot_rel_of_rel (F ⋙ forget Group) x y h)

@[to_additive]
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

@[to_additive]
def colimit_inv (x : G) : G :=
begin
  refine quot.lift (colimit_inv_aux F) _ x,
  intros x y h,
  apply colimit_inv_aux_eq_of_rel,
  apply types.filtered_colimit.rel_of_quot_rel,
  exact h,
end

@[to_additive]
lemma colimit_inv_eq' (x : Σ j, F.obj j) : colimit_inv (G.mk x) = G.mk ⟨x.1, x.2 ⁻¹⟩ := rfl

@[to_additive]
lemma colimit_mul_left_inv (x : G) :
  colimit_mul (F ⋙ forget₂ Group Mon) (colimit_inv x) x =
  colimit_one (F ⋙ forget₂ Group Mon) :=
begin
  apply quot.induction_on x, clear x, intro x,
  cases x with j x,
  erw [colimit_inv_eq', colimit_mul_eq' (F ⋙ forget₂ Group Mon) ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j),
    colimit_one_eq' (F ⋙ forget₂ Group Mon) j],
  dsimp,
  simp only [category_theory.functor.map_id, id_apply, mul_left_inv],
end

@[to_additive]
instance colimit_group : group G :=
{ inv := colimit_inv,
  mul_left_inv := colimit_mul_left_inv,
  .. G.monoid }

@[to_additive]
def colimit : Group := ⟨G, by apply_instance⟩

@[to_additive]
lemma colimit_inv_eq (x : Σ j, F.obj j) : (G.mk x) ⁻¹ = G.mk ⟨x.1, x.2 ⁻¹⟩ := rfl

@[to_additive]
def colimit_cocone : cocone F :=
{ X := colimit,
  ι := { ..(Mon.filtered_colimits.colimit_cocone (F ⋙ forget₂ Group Mon)).ι } }

@[to_additive]
def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
{ desc := λ t, Mon.filtered_colimits.colimit_desc (F ⋙ forget₂ Group Mon)
    ((forget₂ Group Mon).map_cocone t),
  fac' := λ t j, monoid_hom.coe_inj $
    (types.colimit_cocone_is_colimit (F ⋙ forget Group)).fac ((forget Group).map_cocone t) j,
  uniq' := λ t m h, monoid_hom.coe_inj $
    (types.colimit_cocone_is_colimit (F ⋙ forget Group)).uniq ((forget Group).map_cocone t) m
    ((λ j, funext $ λ x, monoid_hom.congr_fun (h j) x)) }

@[to_additive]
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

parameters {J : Type v} [small_category J] [is_filtered J] (F : J ⥤ CommGroup.{v})

@[to_additive]
abbreviation G : Group := Group.filtered_colimits.colimit (F ⋙ forget₂ CommGroup Group.{v})

@[to_additive]
instance colimit_comm_group : comm_group G :=
{ ..G.group,
  ..CommMon.filtered_colimits.colimit_comm_monoid (F ⋙ forget₂ CommGroup CommMon.{v}) }

@[to_additive]
def colimit : CommGroup := ⟨G, by apply_instance⟩

@[to_additive]
def colimit_cocone : cocone F :=
{ X := colimit,
  ι := { ..(Group.filtered_colimits.colimit_cocone (F ⋙ forget₂ CommGroup Group)).ι } }

@[to_additive]
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

@[to_additive]
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

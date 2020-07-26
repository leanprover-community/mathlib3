/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Mon.limits
import algebra.category.Group.preadditive
import category_theory.over
import category_theory.limits.types
import category_theory.limits.preserves
import category_theory.limits.shapes.concrete_category
import algebra.group.pi

/-!
# The category of (commutative) (additive) groups has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/

open category_theory
open category_theory.limits

universe u

namespace Group

variables {J : Type u} [small_category J]

@[to_additive AddGroup.add_group_obj]
instance group_obj (F : J ⥤ Group) (j) :
  group ((F ⋙ forget Group).obj j) :=
by { change group (F.obj j), apply_instance }

/--
The flat sections of a functor into `Group` form a subgroup of all sections.
-/
@[to_additive AddGroup.sections_add_subgroup
  "The flat sections of a functor into `AddGroup` form an additive subgroup of all sections."]
def sections_subgroup (F : J ⥤ Group) :
  subgroup (Π j, F.obj j) :=
{ carrier := (F ⋙ forget Group).sections,
  inv_mem' := λ a ah j j' f,
  begin
    simp only [forget_map_eq_coe, functor.comp_map, pi.inv_apply, monoid_hom.map_inv, inv_inj],
    dsimp [functor.sections] at ah,
    rw ah f,
  end,
  ..(Mon.sections_submonoid (F ⋙ forget₂ Group Mon)) }

@[to_additive AddGroup.limit_add_group]
instance limit_group (F : J ⥤ Group) :
  group (limit (F ⋙ forget Group)) :=
begin
  change group (sections_subgroup F),
  apply_instance,
end

/--
We show that the forgetful functor `Group ⥤ Mon` creates limits.

All we need to do is notice that the limit point has a `group` instance available,
and then reuse the existing limit.
-/
@[to_additive AddGroup.creates_limit]
instance (F : J ⥤ Group) : creates_limit F (forget₂ Group Mon) :=
creates_limit_of_reflects_iso (λ c' t,
{ lifted_cone :=
  { X := Group.of (limit (F ⋙ forget Group)),
    π :=
    { app := Mon.limit_π_monoid_hom (F ⋙ forget₂ Group Mon),
      naturality' := (Mon.has_limits.limit (F ⋙ forget₂ _ _)).π.naturality, } },
  valid_lift := is_limit.unique_up_to_iso (limit.is_limit _) t,
  makes_limit := is_limit.of_faithful (forget₂ Group Mon) (limit.is_limit _)
    (λ s, _) (λ s, rfl) })

/-- The category of groups has all limits. -/
@[to_additive AddGroup.has_limits]
instance has_limits : has_limits Group :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit_of_created F (forget₂ Group Mon) } }

/--
The forgetful functor from groups to monoids preserves all limits.
(That is, the underlying monoid could have been computed instead as limits in the category of monoids.)
-/
@[to_additive AddGroup.forget₂_AddMon_preserves_limits]
instance forget₂_Mon_preserves_limits : preserves_limits (forget₂ Group Mon) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F, by apply_instance } }

/--
The forgetful functor from groups to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
@[to_additive AddCommMon.forget_preserves_limits]
instance forget_preserves_limits : preserves_limits (forget Group) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget _)) } }

end Group

namespace CommGroup

variables {J : Type u} [small_category J]

@[to_additive AddCommGroup.add_comm_group_obj]
instance comm_group_obj (F : J ⥤ CommGroup) (j) :
  comm_group ((F ⋙ forget CommGroup).obj j) :=
by { change comm_group (F.obj j), apply_instance }

@[to_additive AddCommGroup.limit_add_comm_monoid]
instance limit_comm_group (F : J ⥤ CommGroup) :
  comm_group (limit (F ⋙ forget CommGroup)) :=
@subgroup.to_comm_group (Π j, F.obj j) _
  (Group.sections_subgroup (F ⋙ forget₂ CommGroup Group))

/--
We show that the forgetful functor `CommGroup ⥤ Group` creates limits.

All we need to do is notice that the limit point has a `comm_group` instance available,
and then reuse the existing limit.
-/
@[to_additive AddCommGroup.creates_limit]
instance (F : J ⥤ CommGroup) : creates_limit F (forget₂ CommGroup Group) :=
creates_limit_of_reflects_iso (λ c' t,
{ lifted_cone :=
  { X := CommGroup.of (limit (F ⋙ forget CommGroup)),
    π :=
    { app := Mon.limit_π_monoid_hom (F ⋙ forget₂ CommGroup Group ⋙ forget₂ Group Mon),
      naturality' := (Mon.has_limits.limit _).π.naturality, } },
  valid_lift := is_limit.unique_up_to_iso (limit.is_limit _) t,
  makes_limit := is_limit.of_faithful (forget₂ _ Group ⋙ forget₂ _ Mon) (limit.is_limit _)
    (λ s, _) (λ s, rfl) })

/-- The category of commutative groups has all limits. -/
@[to_additive AddCommGroup.has_limits]
instance has_limits : has_limits CommGroup :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit_of_created F (forget₂ CommGroup Group) } }

/--
The forgetful functor from commutative groups to groups preserves all limits.
(That is, the underlying group could have been computed instead as limits in the category of groups.)
-/
@[to_additive AddCommGroup.forget₂_AddGroup_preserves_limits]
instance forget₂_Group_preserves_limits : preserves_limits (forget₂ CommGroup Group) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F, by apply_instance } }

/--
An auxiliary declaration to speed up typechecking.
-/
@[to_additive AddCommGroup.forget₂_AddCommMon_preserves_limits_aux
  "An auxiliary declaration to speed up typechecking."]
def forget₂_CommMon_preserves_limits_aux (F : J ⥤ CommGroup) :
  is_limit ((forget₂ CommGroup CommMon).map_cone (limit.cone F)) :=
  limit.is_limit (F ⋙ forget₂ CommGroup CommMon)

/--
The forgetful functor from commutative groups to commutative monoids preserves all limits.
(That is, the underlying commutative monoids could have been computed instead as limits
in the category of commutative monoids.)
-/
@[to_additive AddCommGroup.forget₂_AddCommMon_preserves_limits]
instance forget₂_CommMon_preserves_limits : preserves_limits (forget₂ CommGroup CommMon) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (forget₂_CommMon_preserves_limits_aux F) } }

/--
The forgetful functor from commutative groups to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
@[to_additive AddCommGroup.forget_preserves_limits]
instance forget_preserves_limits : preserves_limits (forget CommGroup) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget _)) } }

end CommGroup

namespace AddCommGroup

/--
The categorical kernel of a morphism in `AddCommGroup`
agrees with the usual group-theoretical kernel.
-/
@[simps]
def kernel_iso_ker {G H : AddCommGroup} (f : G ⟶ H) :
  kernel f ≅ AddCommGroup.of f.ker :=
{ hom :=
  { to_fun := λ g, ⟨kernel.ι f g,
    begin
      -- TODO where is this `has_coe_t_aux.coe` coming from? can we prevent it appearing?
      change (kernel.ι f) g ∈ f.ker,
      simp [add_monoid_hom.mem_ker],
    end⟩,
    map_zero' := rfl,
    map_add' := λ g g', rfl, },
  inv := kernel.lift f (add_subgroup.subtype f.ker) (by tidy),
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }.

lemma kernel_iso_ker_hom_comp_subtype {G H : AddCommGroup} (f : G ⟶ H) :
  (kernel_iso_ker f).hom ≫ add_subgroup.subtype f.ker = kernel.ι f := rfl

lemma kernel_iso_ker_inv_comp_ι {G H : AddCommGroup} (f : G ⟶ H) :
  (kernel_iso_ker f).inv ≫ kernel.ι f = add_subgroup.subtype f.ker := rfl

/--
The categorical kernel inclusion for `f : G ⟶ H`, as an object over `G`,
agrees with the `subtype` map.
-/
@[simps]
def kernel_iso_ker_over {G H : AddCommGroup} (f : G ⟶ H) :
  over.mk (kernel.ι f) ≅ @over.mk _ _ G (AddCommGroup.of f.ker) (add_subgroup.subtype f.ker) :=
-- TODO this would be cleaner if we made a `over.iso_mk`.
{ hom := over.hom_mk (kernel_iso_ker f).hom (by simp),
  inv := over.hom_mk (kernel_iso_ker f).inv (by simp), }.

end AddCommGroup

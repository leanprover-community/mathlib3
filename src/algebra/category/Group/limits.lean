/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Mon.limits
import algebra.category.Group.preadditive
import category_theory.over
import group_theory.subgroup.basic
import category_theory.concrete_category.elementwise

/-!
# The category of (commutative) (additive) groups has all limits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/

open category_theory
open category_theory.limits

universes v u

noncomputable theory

variables {J : Type v} [small_category J]

namespace Group

@[to_additive]
instance group_obj (F : J ⥤ Group.{max v u}) (j) :
  group ((F ⋙ forget Group).obj j) :=
by { change group (F.obj j), apply_instance }

/--
The flat sections of a functor into `Group` form a subgroup of all sections.
-/
@[to_additive
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

@[to_additive]
instance limit_group (F : J ⥤ Group.{max v u}) :
  group (types.limit_cone (F ⋙ forget Group)).X :=
begin
  change group (sections_subgroup F),
  apply_instance,
end

/-- We show that the forgetful functor `Group ⥤ Mon` creates limits.

All we need to do is notice that the limit point has a `group` instance available, and then reuse
the existing limit. -/
@[to_additive "We show that the forgetful functor `AddGroup ⥤ AddMon` creates limits.

All we need to do is notice that the limit point has an `add_group` instance available, and then
reuse the existing limit."]
instance forget₂.creates_limit (F : J ⥤ Group.{max v u}) :
  creates_limit F (forget₂ Group.{max v u} Mon.{max v u}) :=
creates_limit_of_reflects_iso (λ c' t,
{ lifted_cone :=
  { X := Group.of (types.limit_cone (F ⋙ forget Group)).X,
    π :=
    { app := Mon.limit_π_monoid_hom (F ⋙ forget₂ Group Mon.{max v u}),
      naturality' :=
        (Mon.has_limits.limit_cone (F ⋙ forget₂ Group Mon.{max v u})).π.naturality, } },
  valid_lift := by apply is_limit.unique_up_to_iso (Mon.has_limits.limit_cone_is_limit _) t,
  makes_limit := is_limit.of_faithful (forget₂ Group Mon.{max v u})
    (Mon.has_limits.limit_cone_is_limit _) (λ s, _) (λ s, rfl) })

/--
A choice of limit cone for a functor into `Group`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive "A choice of limit cone for a functor into `Group`.
(Generally, you'll just want to use `limit F`.)"]
def limit_cone (F : J ⥤ Group.{max v u}) : cone F :=
lift_limit (limit.is_limit (F ⋙ (forget₂ Group Mon.{max v u})))

/--
The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive "The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)"]
def limit_cone_is_limit (F : J ⥤ Group.{max v u}) : is_limit (limit_cone F) :=
lifted_limit_is_limit _

/-- The category of groups has all limits. -/
@[to_additive "The category of additive groups has all limits."]
instance has_limits_of_size : has_limits_of_size.{v v} Group.{max v u} :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit_of_created F (forget₂ Group Mon.{max v u}) } }

@[to_additive]
instance has_limits : has_limits Group.{u} := Group.has_limits_of_size.{u u}

/-- The forgetful functor from groups to monoids preserves all limits.

This means the underlying monoid of a limit can be computed as a limit in the category of monoids.
-/
@[to_additive AddGroup.forget₂_AddMon_preserves_limits "The forgetful functor from additive groups
to additive monoids preserves all limits.

This means the underlying additive monoid of a limit can be computed as a limit in the category of
additive monoids."]
instance forget₂_Mon_preserves_limits_of_size :
  preserves_limits_of_size.{v v} (forget₂ Group Mon.{max v u}) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F, by apply_instance } }

@[to_additive]
instance forget₂_Mon_preserves_limits : preserves_limits (forget₂ Group Mon.{u}) :=
Group.forget₂_Mon_preserves_limits_of_size.{u u}

/-- The forgetful functor from groups to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive "The forgetful functor from additive groups to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types."]
instance forget_preserves_limits_of_size :
  preserves_limits_of_size.{v v} (forget Group.{max v u}) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, limits.comp_preserves_limit (forget₂ Group Mon) (forget Mon) } }

@[to_additive]
instance forget_preserves_limits : preserves_limits (forget Group.{u}) :=
Group.forget_preserves_limits_of_size.{u u}

end Group

namespace CommGroup

@[to_additive]
instance comm_group_obj (F : J ⥤ CommGroup.{max v u}) (j) :
  comm_group ((F ⋙ forget CommGroup).obj j) :=
by { change comm_group (F.obj j), apply_instance }

@[to_additive]
instance limit_comm_group (F : J ⥤ CommGroup.{max v u}) :
  comm_group (types.limit_cone (F ⋙ forget CommGroup.{max v u})).X :=
@subgroup.to_comm_group (Π j, F.obj j) _
  (Group.sections_subgroup (F ⋙ forget₂ CommGroup Group.{max v u}))

/--
We show that the forgetful functor `CommGroup ⥤ Group` creates limits.

All we need to do is notice that the limit point has a `comm_group` instance available,
and then reuse the existing limit.
-/
@[to_additive "We show that the forgetful functor `AddCommGroup ⥤ AddGroup` creates limits.

All we need to do is notice that the limit point has an `add_comm_group` instance available, and
then reuse the existing limit."]
instance forget₂.creates_limit (F : J ⥤ CommGroup.{max v u}) :
  creates_limit F (forget₂ CommGroup Group.{max v u}) :=
creates_limit_of_reflects_iso (λ c' t,
{ lifted_cone :=
  { X := CommGroup.of (types.limit_cone (F ⋙ forget CommGroup)).X,
    π :=
    { app := Mon.limit_π_monoid_hom
        (F ⋙ forget₂ CommGroup Group.{max v u} ⋙ forget₂ Group Mon.{max v u}),
      naturality' := (Mon.has_limits.limit_cone _).π.naturality, } },
  valid_lift := by apply is_limit.unique_up_to_iso (Group.limit_cone_is_limit _) t,
  makes_limit := is_limit.of_faithful (forget₂ _ Group.{max v u} ⋙ forget₂ _ Mon.{max v u})
    (by apply Mon.has_limits.limit_cone_is_limit _) (λ s, _) (λ s, rfl) })

/--
A choice of limit cone for a functor into `CommGroup`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive "A choice of limit cone for a functor into `CommGroup`.
(Generally, you'll just want to use `limit F`.)"]
def limit_cone (F : J ⥤ CommGroup.{max v u}) : cone F :=
lift_limit (limit.is_limit (F ⋙ (forget₂ CommGroup Group.{max v u})))

/--
The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive "The chosen cone is a limit cone.
(Generally, you'll just wantto use `limit.cone F`.)"]
def limit_cone_is_limit (F : J ⥤ CommGroup.{max v u}) : is_limit (limit_cone F) :=
lifted_limit_is_limit _

/-- The category of commutative groups has all limits. -/
@[to_additive "The category of additive commutative groups has all limits."]
instance has_limits_of_size : has_limits_of_size.{v v} CommGroup.{max v u} :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit_of_created F (forget₂ CommGroup Group.{max v u}) } }

@[to_additive]
instance has_limits : has_limits CommGroup.{u} := CommGroup.has_limits_of_size.{u u}

/--
The forgetful functor from commutative groups to groups preserves all limits.
(That is, the underlying group could have been computed instead as limits in the category
of groups.)
-/
@[to_additive AddCommGroup.forget₂_AddGroup_preserves_limits
"The forgetful functor from additive commutative groups to groups preserves all limits.
(That is, the underlying group could have been computed instead as limits in the category
of additive groups.)"]
instance forget₂_Group_preserves_limits_of_size :
  preserves_limits_of_size.{v v} (forget₂ CommGroup Group.{max v u}) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F, by apply_instance } }

@[to_additive]
instance forget₂_Group_preserves_limits : preserves_limits (forget₂ CommGroup Group.{u}) :=
CommGroup.forget₂_Group_preserves_limits_of_size.{u u}

/--
An auxiliary declaration to speed up typechecking.
-/
@[to_additive AddCommGroup.forget₂_AddCommMon_preserves_limits_aux
  "An auxiliary declaration to speed up typechecking."]
def forget₂_CommMon_preserves_limits_aux (F : J ⥤ CommGroup.{max v u}) :
  is_limit ((forget₂ CommGroup CommMon).map_cone (limit_cone F)) :=
CommMon.limit_cone_is_limit (F ⋙ forget₂ CommGroup CommMon)

/--
The forgetful functor from commutative groups to commutative monoids preserves all limits.
(That is, the underlying commutative monoids could have been computed instead as limits
in the category of commutative monoids.)
-/
@[to_additive AddCommGroup.forget₂_AddCommMon_preserves_limits
"The forgetful functor from additive commutative groups to additive commutative monoids preserves
all limits. (That is, the underlying additive commutative monoids could have been computed instead
as limits in the category of additive commutative monoids.)"]
instance forget₂_CommMon_preserves_limits_of_size :
  preserves_limits_of_size.{v v} (forget₂ CommGroup CommMon.{max v u}) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
    (limit_cone_is_limit F) (forget₂_CommMon_preserves_limits_aux F) } }

/--
The forgetful functor from commutative groups to types preserves all limits. (That is, the
underlying types could have been computed instead as limits in the category of types.)
-/
@[to_additive AddCommGroup.forget_preserves_limits
"The forgetful functor from additive commutative groups to types preserves all limits. (That is,
the underlying types could have been computed instead as limits in the category of types.)"]
instance forget_preserves_limits_of_size :
  preserves_limits_of_size.{v v} (forget CommGroup.{max v u}) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, limits.comp_preserves_limit (forget₂ CommGroup Group) (forget Group) } }

-- Verify we can form limits indexed over smaller categories.
example (f : ℕ → AddCommGroup) : has_product f := by apply_instance

end CommGroup

namespace AddCommGroup

/--
The categorical kernel of a morphism in `AddCommGroup`
agrees with the usual group-theoretical kernel.
-/
def kernel_iso_ker {G H : AddCommGroup.{u}} (f : G ⟶ H) :
  kernel f ≅ AddCommGroup.of f.ker :=
{ hom :=
  { to_fun := λ g, ⟨kernel.ι f g,
    begin
      -- TODO where is this `has_coe_t_aux.coe` coming from? can we prevent it appearing?
      change (kernel.ι f) g ∈ f.ker,
      simp [add_monoid_hom.mem_ker],
    end⟩,
    map_zero' := by { ext, simp, },
    map_add' := λ g g', by { ext, simp, }, },
  inv := kernel.lift f (add_subgroup.subtype f.ker) (by tidy),
  hom_inv_id' := by { apply equalizer.hom_ext _, ext, simp, },
  inv_hom_id' :=
  begin
    apply AddCommGroup.ext,
    simp only [add_monoid_hom.coe_mk, coe_id, coe_comp],
    rintro ⟨x, mem⟩,
    simp,
  end, }.

@[simp]
lemma kernel_iso_ker_hom_comp_subtype {G H : AddCommGroup} (f : G ⟶ H) :
  (kernel_iso_ker f).hom ≫ add_subgroup.subtype f.ker = kernel.ι f :=
by ext; refl

@[simp]
lemma kernel_iso_ker_inv_comp_ι {G H : AddCommGroup} (f : G ⟶ H) :
  (kernel_iso_ker f).inv ≫ kernel.ι f = add_subgroup.subtype f.ker :=
begin
  ext,
  simp [kernel_iso_ker],
end

/--
The categorical kernel inclusion for `f : G ⟶ H`, as an object over `G`,
agrees with the `subtype` map.
-/
@[simps]
def kernel_iso_ker_over {G H : AddCommGroup.{u}} (f : G ⟶ H) :
  over.mk (kernel.ι f) ≅ @over.mk _ _ G (AddCommGroup.of f.ker) (add_subgroup.subtype f.ker) :=
over.iso_mk (kernel_iso_ker f) (by simp)

end AddCommGroup

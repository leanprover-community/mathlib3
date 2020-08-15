/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.group.pi
import algebra.category.Mon.basic
import category_theory.limits.types
import category_theory.limits.creates
import tactic.transport

/-!
# The category of (commutative) (additive) monoids has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/

open category_theory
open category_theory.limits

universe u

noncomputable theory

namespace Mon

variables {J : Type u} [small_category J]

-- FIXME: to_additive by default transports this to `AddMon.monoid_obj`
@[to_additive AddMon.add_monoid_obj]
instance monoid_obj (F : J ⥤ Mon) (j) :
  monoid ((F ⋙ forget Mon).obj j) :=
by { change monoid (F.obj j), apply_instance }

/--
The flat sections of a functor into `Mon` form a submonoid of all sections.
-/
@[to_additive AddMon.sections_add_submonoid
  "The flat sections of a functor into `AddMon` form an additive submonoid of all sections."]
def sections_submonoid (F : J ⥤ Mon) :
  submonoid (Π j, F.obj j) :=
{ carrier := (F ⋙ forget Mon).sections,
  one_mem' := λ j j' f, by simp,
  mul_mem' := λ a b ah bh j j' f,
  begin
    simp only [forget_map_eq_coe, functor.comp_map, monoid_hom.map_mul, pi.mul_apply],
    dsimp [functor.sections] at ah bh,
    rw [ah f, bh f],
  end }

@[to_additive AddMon.limit_add_monoid]
instance limit_monoid (F : J ⥤ Mon) :
  monoid (limit (F ⋙ forget Mon)) :=
begin
  haveI : monoid ((F ⋙ forget Mon).sections) := (sections_submonoid F).to_monoid,
  transport using (types.limit_equiv_sections (F ⋙ forget Mon)).symm,
end

@[simp, to_additive]
lemma map_one (F : J ⥤ Mon) (j : J) : limit.π (F ⋙ forget Mon) j 1 = 1 :=
by { erw types.limit_equiv_sections_symm_apply, refl }

@[simp, to_additive]
lemma map_mul (F : J ⥤ Mon) (j : J) (x y) :
  limit.π (F ⋙ forget Mon) j (x * y) =
    limit.π (F ⋙ forget Mon) j x * limit.π (F ⋙ forget Mon) j y :=
by { erw types.limit_equiv_sections_symm_apply, refl }

/-- `limit.π (F ⋙ forget Mon) j` as a `monoid_hom`. -/
@[to_additive AddMon.limit_π_add_monoid_hom
  "`limit.π (F ⋙ forget AddMon) j` as an `add_monoid_hom`."]
def limit_π_monoid_hom (F : J ⥤ Mon) (j) :
  limit (F ⋙ forget Mon) →* (F ⋙ forget Mon).obj j :=
{ to_fun := limit.π (F ⋙ forget Mon) j,
  map_one' := by simp,
  map_mul' := λ x y, by simp }

namespace has_limits
-- The next two definitions are used in the construction of `has_limits Mon`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `Mon`.
(Internal use only; use the limits API.)
-/
@[to_additive AddMon.has_limits.limit "(Internal use only; use the limits API.)"]
def limit_cone (F : J ⥤ Mon) : cone F :=
{ X := Mon.of (limit (F ⋙ forget _)),
  π :=
  { app := limit_π_monoid_hom F,
    naturality' := λ j j' f,
      monoid_hom.coe_inj ((limit.cone (F ⋙ forget _)).π.naturality f) } }

@[simps, to_additive]
def forget_map_cone_limit_cone_iso (F : J ⥤ Mon) :
  (forget Mon).map_cone (limit_cone F) ≅ limit.cone (F ⋙ forget Mon) :=
{ hom := { hom := 𝟙 _, },
  inv := { hom := 𝟙 _, } }

@[to_additive]
def is_limit_forget_map_cone_limit_cone (F : J ⥤ Mon) :
  is_limit ((forget Mon).map_cone (limit_cone F)) :=
is_limit.of_iso_limit (limit.is_limit _) (forget_map_cone_limit_cone_iso F).symm

/--
Witness that the limit cone in `Mon` is a limit cone.
(Internal use only; use the limits API.)
-/
@[to_additive AddMon.has_limits.limit_is_limit "(Internal use only; use the limits API.)"]
def limit_cone_is_limit (F : J ⥤ Mon) : is_limit (limit_cone F) :=
begin
  refine is_limit.of_faithful
    (forget Mon) (is_limit_forget_map_cone_limit_cone F)
    (λ s, ⟨_, _, _⟩) (λ s, rfl); tidy,
end

end has_limits

open has_limits

/-- The category of monoids has all limits. -/
@[to_additive AddMon.has_limits]
instance has_limits : has_limits Mon :=
{ has_limits_of_shape := λ J 𝒥,
  { has_limit := λ F, by exactI has_limit.mk
    { cone     := limit_cone F,
      is_limit := limit_cone_is_limit F } } }

@[to_additive]
def limit_iso_Mon_of_limit_forget (F : J ⥤ Mon) : limit F ≅ Mon.of (limit (F ⋙ forget Mon)) :=
sorry

/--
The forgetful functor from monoids to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
@[to_additive AddMon.forget_preserves_limits]
instance forget_preserves_limits : preserves_limits (forget Mon) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit_cone_is_limit F) (is_limit_forget_map_cone_limit_cone F) } }

end Mon

namespace CommMon

variables {J : Type u} [small_category J]

@[to_additive AddCommMon.add_comm_monoid_obj]
instance comm_monoid_obj (F : J ⥤ CommMon) (j) :
  comm_monoid ((F ⋙ forget CommMon).obj j) :=
by { change comm_monoid (F.obj j), apply_instance }

@[to_additive AddCommMon.limit_add_comm_monoid]
instance limit_comm_monoid (F : J ⥤ CommMon) :
  comm_monoid (limit (F ⋙ forget CommMon)) :=
begin
  haveI : comm_monoid ((F ⋙ forget CommMon).sections) :=
    @submonoid.to_comm_monoid (Π j, F.obj j) _
      (Mon.sections_submonoid (F ⋙ forget₂ CommMon Mon)),
  transport using (types.limit_equiv_sections (F ⋙ forget CommMon)).symm,
end

@[simps, to_additive]
def lifted_cone (F : J ⥤ CommMon) : cone F :=
{ X := CommMon.of (limit (F ⋙ forget CommMon)),
  π :=
  { app := Mon.limit_π_monoid_hom (F ⋙ forget₂ CommMon Mon),
    naturality' := (Mon.has_limits.limit_cone (F ⋙ forget₂ _ _)).π.naturality, } }

@[to_additive]
def is_limit_forget₂_map_cone_lifted_cone (F : J ⥤ CommMon) :
  is_limit ((forget₂ CommMon Mon).map_cone (lifted_cone F)) :=
{ lift := λ s, limit.lift (F ⋙ forget₂ CommMon Mon) s ≫ (Mon.limit_iso_Mon_of_limit_forget _).hom,
  fac' := sorry,
  uniq' := sorry, }

/--
We show that the forgetful functor `CommMon ⥤ Mon` creates limits.

All we need to do is notice that the limit point has a `comm_monoid` instance available,
and then reuse the existing limit.
-/
@[to_additive AddCommMon.creates_limit]
instance (F : J ⥤ CommMon) : creates_limit F (forget₂ CommMon Mon) :=
creates_limit_of_reflects_iso (λ c' t,
{ lifted_cone := lifted_cone F,
  valid_lift := is_limit.unique_up_to_iso (is_limit_forget₂_map_cone_lifted_cone F) t,
  makes_limit := is_limit.of_faithful (forget₂ CommMon Mon) (is_limit_forget₂_map_cone_lifted_cone F)
    (λ s, _) (λ s, rfl) })

/-- The category of commutative monoids has all limits. -/
@[to_additive AddCommMon.has_limits]
instance has_limits : has_limits CommMon :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit_of_created F (forget₂ CommMon Mon) } }

/--
The forgetful functor from commutative monoids to monoids preserves all limits.
(That is, the underlying monoid could have been computed instead as limits in the category of monoids.)
-/
@[to_additive AddCommMon.forget₂_AddMon_preserves_limits]
instance forget₂_Mon_preserves_limits : preserves_limits (forget₂ CommMon Mon) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F, by apply_instance } }

/--
The forgetful functor from commutative monoids to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
@[to_additive AddCommMon.forget_preserves_limits]
instance forget_preserves_limits : preserves_limits (forget CommMon) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, limits.comp_preserves_limit (forget₂ CommMon Mon) (forget Mon) } }

end CommMon

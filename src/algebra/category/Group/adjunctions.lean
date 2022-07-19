/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl
-/
import algebra.category.Group.basic
import group_theory.free_abelian_group
import algebra.category.Ring.basic
import algebra.category.Module.basic

/-!
# Adjunctions regarding the category of (abelian) groups

This file contains construction of basic adjunctions concerning the category of groups and the
category of abelian groups.

## Main definitions

* `AddCommGroup.free`: constructs the functor associating to a type `X` the free abelian group with
  generators `x : X`.
* `Group.free`: constructs the functor associating to a type `X` the free group with
  generators `x : X`.
* `abelianize`: constructs the functor which associates to a group `G` its abelianization `Gᵃᵇ`.

## Main statements

* `AddCommGroup.adj`: proves that `AddCommGroup.free` is the left adjoint of the forgetful functor
  from abelian groups to types.
* `Group.adj`: proves that `Group.free` is the left adjoint of the forgetful functor from groups to
  types.
* `abelianize_adj`: proves that `abelianize` is left adjoint to the forgetful functor from
  abelian groups to groups.
-/

noncomputable theory

universe u

open category_theory

namespace AddCommGroup

open_locale classical

/--
The free functor `Type u ⥤ AddCommGroup` sending a type `X` to the
free abelian group with generators `x : X`.
-/
def free : Type u ⥤ AddCommGroup :=
{ obj := λ α, of (free_abelian_group α),
  map := λ X Y, free_abelian_group.map,
  map_id' := λ X, add_monoid_hom.ext free_abelian_group.map_id_apply,
  map_comp' := λ X Y Z f g, add_monoid_hom.ext free_abelian_group.map_comp_apply, }

@[simp] lemma free_obj_coe {α : Type u} :
  (free.obj α : Type u) = (free_abelian_group α) := rfl

@[simp] lemma free_map_coe {α β : Type u} {f : α → β} (x : free_abelian_group α) :
  (free.map f) x = f <$> x := rfl

/--
The free-forgetful adjunction for abelian groups.
-/
def adj : free ⊣ forget AddCommGroup.{u} :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X G, free_abelian_group.lift.symm,
  hom_equiv_naturality_left_symm' :=
  by { intros, ext, refl} }

instance : is_right_adjoint (forget AddCommGroup.{u}) := ⟨_, adj⟩

/--
As an example, we now give a high-powered proof that
the monomorphisms in `AddCommGroup` are just the injective functions.

(This proof works in all universes.)
-/
example {G H : AddCommGroup.{u}} (f : G ⟶ H) [mono f] : function.injective f :=
(mono_iff_injective f).1 (show mono ((forget AddCommGroup.{u}).map f), by apply_instance)

end AddCommGroup

namespace Group

/-- The free functor `Type u ⥤ Group` sending a type `X` to the free group with generators `x : X`.
-/
def free : Type u ⥤ Group :=
{ obj := λ α, of (free_group α),
  map := λ X Y, free_group.map,
  map_id' := by { intros, ext1, refl },
  map_comp' := by { intros, ext1, refl } }

/-- The free-forgetful adjunction for groups.
-/
def adj : free ⊣ forget Group.{u} :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X G, free_group.lift.symm,
  hom_equiv_naturality_left_symm' := λ X Y G f g, by { ext1, refl } }

instance : is_right_adjoint (forget Group.{u}) := ⟨_, adj⟩

end Group

section abelianization

/-- The abelianization functor `Group ⥤ CommGroup` sending a group `G` to its abelianization `Gᵃᵇ`.
 -/
def abelianize : Group.{u} ⥤ CommGroup.{u} :=
{ obj := λ G, { α := abelianization G, str := by apply_instance },
  map := λ G H f, abelianization.lift ( { to_fun := λ x, abelianization.of (f x),
  map_one' := by simp,
  map_mul' := by simp } ),
  map_id' := by { intros, simp only [monoid_hom.mk_coe, coe_id], ext1, refl },
  map_comp' := by { intros, simp only [coe_comp], ext1, refl } }

/-- The abelianization-forgetful adjuction from `Group` to `CommGroup`.-/
def abelianize_adj : abelianize ⊣ forget₂ CommGroup.{u} Group.{u} :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ G A, abelianization.lift.symm,
  hom_equiv_naturality_left_symm' := λ G H A f g, by { ext1, refl } }

end abelianization

namespace coextension_of_scalars

/-!
We construct the coextension of scalar functor `AddCommGroup ⥤ Module R`.
-/

variables (R : Ring.{u}) (A : AddCommGroup.{u})

local notation `Hom` A := ((⟨R⟩ : Ab) ⟶ A)

instance : has_smul R $ Hom A :=
{ smul := λ r f,
  { to_fun := λ r', f (r' * r),
    map_zero' := by simp,
    map_add' := λ _ _, by simp [add_mul] } }

@[simp] lemma smul_apply (r r' : R) (f : Hom A) : (r • f) r' = f (r' * r) := rfl

instance : mul_action R $ Hom A :=
{ smul := (•),
  one_smul := λ r, fun_like.ext _ _ $ λ r', by simp,
  mul_smul := λ r r' f, fun_like.ext _ _ $ λ r'', by simp [mul_assoc], }

instance : distrib_mul_action R $ Hom A :=
{ smul_add := λ r f g, fun_like.ext _ _ $ λ r', rfl,
  smul_zero := λ r, fun_like.ext _ _ $ λ r', rfl,
  ..(_ : mul_action R $ Hom A)}

instance : module R $ Hom A :=
{ add_smul := λ r s f, fun_like.ext _ _ $ λ x, by simp [mul_add],
  zero_smul := λ f, fun_like.ext _ _ $ λ x, by simp,
  ..(_ : distrib_mul_action R $ Hom A) }

section map

/--
Given `B C : Ab` and `f : B ⟶ C`,  we get a morphism `(R ⟶ B) → (R ⟶ C)` defined by `g ↦ g ∘ f`.
-/
def map {B C : AddCommGroup.{u}} (f : B ⟶ C) : (⟨Hom B⟩ : Module R) ⟶ (⟨Hom C⟩ : Module R) :=
{ to_fun := f.comp,
  map_add' := f.comp_add,
  map_smul' := λ r g, fun_like.ext _ _ $ λ x, rfl }

variable {R}

@[simp] lemma map_apply {B C : AddCommGroup.{u}} (f : B ⟶ C) (g : Hom B) (x : R) :
  map R f g x = f (g x) := rfl

lemma map_id {B : AddCommGroup.{u}} : map R (add_monoid_hom.id B) = linear_map.id :=
fun_like.ext _ _ $ λ f, fun_like.ext _ _ $ λ x, rfl

lemma map_comp {B C D : AddCommGroup.{u}} (f : B ⟶ C) (g : C ⟶ D) :
  map R (g.comp f) = (map R g).comp (map R f) := rfl

end map

/--
coextension of scalars `Ab ⥤ Module R` by sending `A ↦ Hom(R, A)` and `f ↦ g ↦ g ∘ f`.
This functor is adjoint to `forget₂ (Module R) Ab`.
-/
@[simps] def _root_.coextension_of_scalars : AddCommGroup.{u} ⥤ Module.{u} R :=
{ obj := λ A, ⟨Hom A⟩,
  map := λ _ _ f, map R f,
  map_id' := λ X, map_id,
  map_comp' := λ _ _ _, map_comp }

namespace adj_forget

variables (M : Module.{u} R)

namespace hom_equiv

/--
If `f : M →+ A`, then there is a map `M ⟶ Hom(R, A)` given by `m ↦ r ↦ f (r • m)`
-/
def forward (f : (forget₂ (Module.{u} R) Ab.{u}).obj M ⟶ A) :
  M ⟶ (coextension_of_scalars R).obj A :=
{ to_fun := λ m,
  { to_fun := λ r, f (@has_smul.smul R M _ r m),
    map_zero' := by rw [zero_smul, map_zero],
    map_add' := λ x y, by rw [add_smul, map_add] },
  map_add' := λ x y, begin
    ext1 z,
    simp only [map_add, smul_add, add_monoid_hom.coe_mk, add_monoid_hom.add_apply],
  end,
  map_smul' := λ r x, begin
    ext1 z,
    simp only [add_monoid_hom.coe_mk, ring_hom.id_apply, smul_apply],
    rw [mul_smul],
  end }

/--
If `f : M ⟶ Hom(R, A)`, then there is `M →+ A` given by `m ↦ (f m) 1`
-/
def backward (f : M ⟶ (coextension_of_scalars R).obj A) :
  (forget₂ (Module.{u} R) Ab.{u}).obj M ⟶ A :=
{ to_fun := λ m, (f m).to_fun 1,
  map_zero' := by simp,
  map_add' := λ x y, by simp }

lemma fb (f : (forget₂ (Module.{u} R) Ab.{u}).obj M ⟶ A) :
  backward R A M (forward R A M f) = f :=
by ext; simp [backward, forward]

lemma bf (f : M ⟶ (coextension_of_scalars R).obj A) :
  forward R A M (backward R A M f) = f :=
by ext; simp [backward, forward]

end hom_equiv

/--
The unit in the adjunction `forget ⊣ coextension of scalars`
-/
@[simps] def unit : 𝟭 (Module R) ⟶ forget₂ (Module R) Ab ⋙ coextension_of_scalars R :=
{ app := λ M,
  { to_fun := λ m,
    { to_fun := λ r, @has_smul.smul R M _ r m,
      map_zero' := by rw [zero_smul],
      map_add' := λ x y, by rw [add_smul] },
    map_add' := λ x y, begin
      ext1 z,
      simp only [smul_add, add_monoid_hom.coe_mk, add_monoid_hom.add_apply],
    end,
    map_smul' := λ r m, begin
      ext1 z,
      simp only [mul_smul, add_monoid_hom.coe_mk, ring_hom.id_apply, smul_apply],
    end },
  naturality' := λ X Y f, by { ext, simp } }

/--
The counit in the adjunction `forget ⊣ coextension of scalars`
-/
@[simps] def counit : (coextension_of_scalars R ⋙ forget₂ (Module.{u} R) Ab.{u}) ⟶ 𝟭 Ab :=
{ app := λ A,
  { to_fun := λ f, f.to_fun 1,
    map_zero' := rfl,
    map_add' := λ x y, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.add_apply] },
  naturality' := λ X Y g, by { ext, simp } }

end adj_forget

/--
`foget₂ (Module R) Ab` is adjoint to coextension of scalars.
-/
def adj_forget : forget₂ (Module.{u} R) AddCommGroup.{u} ⊣ coextension_of_scalars R :=
{ hom_equiv := λ X Y,
  { to_fun := adj_forget.hom_equiv.forward R Y X,
    inv_fun := adj_forget.hom_equiv.backward R Y X,
    left_inv := adj_forget.hom_equiv.fb R Y X,
    right_inv := adj_forget.hom_equiv.bf R Y X },
  unit := adj_forget.unit R,
  counit := adj_forget.counit R,
  hom_equiv_unit' := λ M A f, by { ext m r, simp [adj_forget.hom_equiv.forward] },
  hom_equiv_counit' := λ M A f, by { ext, simp [adj_forget.hom_equiv.backward] } }

instance : is_left_adjoint (forget₂ (Module.{u} R) AddCommGroup.{u}) := ⟨_, adj_forget R⟩

instance : is_right_adjoint (coextension_of_scalars R) := ⟨_, adj_forget R⟩

end coextension_of_scalars

/-- The functor taking a monoid to its subgroup of units. -/
@[simps]
def Mon.units : Mon.{u} ⥤ Group.{u} :=
{ obj := λ R, Group.of Rˣ,
  map := λ R S f, Group.of_hom $ units.map f,
  map_id' := λ X, monoid_hom.ext (λ x, units.ext rfl),
  map_comp' := λ X Y Z f g, monoid_hom.ext (λ x, units.ext rfl) }

/-- The forgetful-units adjunction between `Group` and `Mon`. -/
def Group.forget₂_Mon_adj : forget₂ Group Mon ⊣ Mon.units.{u} :=
{ hom_equiv := λ X Y,
  { to_fun := λ f, monoid_hom.to_hom_units f,
    inv_fun := λ f, (units.coe_hom Y).comp f,
    left_inv := λ f, monoid_hom.ext $ λ _, rfl,
    right_inv := λ f, monoid_hom.ext $ λ _, units.ext rfl },
  unit :=
  { app := λ X, { ..(@to_units X _).to_monoid_hom },
    naturality' := λ X Y f, monoid_hom.ext $ λ x, units.ext rfl },
  counit :=
  { app := λ X, units.coe_hom X,
    naturality' := λ X Y f, monoid_hom.ext $ λ x, rfl },
  hom_equiv_unit' := λ X Y f, monoid_hom.ext $ λ _, units.ext rfl,
  hom_equiv_counit' := λ X Y f, monoid_hom.ext $ λ _, rfl }

instance : is_right_adjoint Mon.units.{u} :=
⟨_, Group.forget₂_Mon_adj⟩

/-- The functor taking a monoid to its subgroup of units. -/
@[simps]
def CommMon.units : CommMon.{u} ⥤ CommGroup.{u} :=
{ obj := λ R, CommGroup.of Rˣ,
  map := λ R S f, CommGroup.of_hom $ units.map f,
  map_id' := λ X, monoid_hom.ext (λ x, units.ext rfl),
  map_comp' := λ X Y Z f g, monoid_hom.ext (λ x, units.ext rfl) }

/-- The forgetful-units adjunction between `CommGroup` and `CommMon`. -/
def CommGroup.forget₂_CommMon_adj : forget₂ CommGroup CommMon ⊣ CommMon.units.{u} :=
{ hom_equiv := λ X Y,
  { to_fun := λ f, monoid_hom.to_hom_units f,
    inv_fun := λ f, (units.coe_hom Y).comp f,
    left_inv := λ f, monoid_hom.ext $ λ _, rfl,
    right_inv := λ f, monoid_hom.ext $ λ _, units.ext rfl },
  unit :=
  { app := λ X, { ..(@to_units X _).to_monoid_hom },
    naturality' := λ X Y f, monoid_hom.ext $ λ x, units.ext rfl },
  counit :=
  { app := λ X, units.coe_hom X,
    naturality' := λ X Y f, monoid_hom.ext $ λ x, rfl },
  hom_equiv_unit' := λ X Y f, monoid_hom.ext $ λ _, units.ext rfl,
  hom_equiv_counit' := λ X Y f, monoid_hom.ext $ λ _, rfl }

instance : is_right_adjoint CommMon.units.{u} :=
⟨_, CommGroup.forget₂_CommMon_adj⟩

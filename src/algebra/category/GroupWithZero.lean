/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.category.Group.basic
import category_theory.category.Bipointed

/-!
# The category of groups with zero

This file defines `GroupWithZero`, the category of groups with zero.
-/

@[to_additive] instance {F α β : Type*} [has_mul α] [has_mul β] [mul_equiv_class F α β] :
  has_coe_t F (α ≃* β) :=
⟨λ f, { to_fun := f, inv_fun := equiv_like.inv f, left_inv := equiv_like.left_inv f,
  right_inv := equiv_like.right_inv f, map_mul' := map_mul f }⟩

namespace monoid_hom
local attribute [reducible] with_zero
variables {α β γ : Type*}

variables [mul_one_class α] [mul_one_class β] [mul_one_class γ]

/-- Turn a `monoid_hom` into a `monoid_with_zero_hom` by adjoining a `0` to the domain and codomain.
-/
protected def with_zero (f : α →* β) : with_zero α →*₀ with_zero β :=
{ to_fun := option.map f,
  map_zero' := rfl,
  map_one' := _root_.congr_arg some (map_one f),
  map_mul' := λ a b, with_zero.cases_on a (by { rw zero_mul, exact (zero_mul _).symm }) $ λ a,
    with_zero.cases_on b (by { rw mul_zero, exact (mul_zero _).symm }) $ λ b,
      by { change option.map _ _ = _, exact _root_.congr_arg some (f.map_mul' _ _) } }

protected lemma with_zero_id : (monoid_hom.id α).with_zero = monoid_with_zero_hom.id _ :=
fun_like.coe_injective option.map_id

protected lemma with_zero_comp (f : β →* γ) (g : α →* β) :
  (f.comp g).with_zero = f.with_zero.comp g.with_zero :=
fun_like.coe_injective (option.map_comp_map _ _).symm

end monoid_hom

@[simp] lemma option.coe_get {α : Type*} {a : option α} (h : option.is_some a) :
  (↑(option.get h) : option α) = a :=
option.some_get _

section
local attribute [reducible] with_zero

/-- Any group is isomorphic to the units of itself adjoined with `0`. -/
@[simps] def units_with_zero_equiv (α : Type*) [group α] : (with_zero α)ˣ ≃* α :=
{ to_fun    := λ a, option.get (option.ne_none_iff_is_some.1 a.ne_zero),
  inv_fun   := λ a, ⟨a, a⁻¹, mul_inv_cancel $ option.some_ne_none _,
    inv_mul_cancel $ option.some_ne_none _⟩,
  left_inv  := λ a, units.ext $ option.some_get _,
  right_inv := λ a, rfl,
  map_mul'  := λ a b, with_zero.coe_inj.1 $
    by simp only [units.coe_mul, option.coe_get, with_zero.coe_mul] }

@[nolint check_type] lemma with_zero.none_eq_zero {α : Type*} : (none : with_zero α) = 0 := rfl

/-- Any group with zero is isomorphic to its units adjoined with `0`. -/
@[simps] def with_zero_units_equiv (α : Type*) [group_with_zero α] [decidable_eq α] :
  with_zero αˣ ≃* α :=
{ to_fun    := λ a, option.elim a 0 coe,
  inv_fun   := λ a, if h : a = 0 then 0 else units.mk0 a h,
  left_inv  := λ a, begin
    cases a,
    { simp only [option.elim, dif_pos],
      refl },
    { simp only [option.elim, units.ne_zero, units.mk0_coe, dite_eq_ite, if_false],
      refl }
  end,
  right_inv := λ a, begin
    dsimp,
    split_ifs,
    { exact h.symm },
    { refl }
  end,
  map_mul' := λ a b, with_zero.cases_on a (by { rw zero_mul, exact (zero_mul _).symm }) $ λ a,
    with_zero.cases_on b (by { rw mul_zero, exact (mul_zero _).symm }) $ λ b, rfl }

end

/-- Monoid homomorphisms from a group `α` to a monoid `β` are just monoid homomorphisms from `α` to
the units of `β`. -/
@[to_additive "Additive monoid homomorphisms from an additive group `α` to an additive monoid `β`
are just additive monoid homomorphisms from `α` to the units of `β`.", simps]
def monoid_hom_units_equiv {α β : Type*} [group α] [monoid β] : (α →* βˣ) ≃ (α →* β) :=
{ to_fun := (units.coe_hom _).comp,
  inv_fun := monoid_hom.to_hom_units,
  left_inv := λ f, monoid_hom.ext $ λ a, units.ext rfl,
  right_inv := λ f, monoid_hom.ext $ λ a, rfl }

universes u

open category_theory order

/-- The category of groups with zero. -/
def GroupWithZero := bundled group_with_zero

namespace GroupWithZero

instance : has_coe_to_sort GroupWithZero Type* := bundled.has_coe_to_sort
instance (X : GroupWithZero) : group_with_zero X := X.str

/-- Construct a bundled `GroupWithZero` from a `group_with_zero`. -/
def of (α : Type*) [group_with_zero α] : GroupWithZero := bundled.of α

instance : inhabited GroupWithZero := ⟨of (with_zero punit)⟩

instance : large_category.{u} GroupWithZero :=
{ hom := λ X Y, monoid_with_zero_hom X Y,
  id := λ X, monoid_with_zero_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, monoid_with_zero_hom.comp_id,
  comp_id' := λ X Y, monoid_with_zero_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, monoid_with_zero_hom.comp_assoc _ _ _ }

instance : concrete_category GroupWithZero :=
{ forget := ⟨coe_sort, λ X Y, coe_fn, λ X, rfl, λ X Y Z f g, rfl⟩,
  forget_faithful := ⟨λ X Y f g h, fun_like.coe_injective h⟩ }

instance has_forget_to_Bipointed : has_forget₂ GroupWithZero Bipointed :=
{ forget₂ := { obj := λ X, ⟨X, 0, 1⟩, map := λ X Y f, ⟨f, f.map_zero', f.map_one'⟩ } }

instance has_forget_to_Mon : has_forget₂ GroupWithZero Mon :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, monoid_with_zero_hom.to_monoid_hom } }

/-- Constructs an isomorphism of groups with zero from a group isomorphism between them. -/
@[simps] def iso.mk {α β : GroupWithZero.{u}} (e : α ≃* β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

end GroupWithZero

/-- `with_zero` as a functor. -/
def Group_to_GroupWithZero : Group.{u} ⥤ GroupWithZero :=
{ obj := λ X, GroupWithZero.of (with_zero X),
  map := λ X Y, monoid_hom.with_zero,
  map_id' := λ X, fun_like.coe_injective $
    by { simp only [fun_like.coe_fn_eq], exact monoid_hom.with_zero_id },
  map_comp' := λ X Y Z f g, fun_like.coe_injective $
    by { simp only [fun_like.coe_fn_eq], exact monoid_hom.with_zero_comp _ _ } }

/-- `units` as a functor. -/
@[to_additive AddMon.add_units "`add_units` as a functor."]
protected def Mon.units : Mon.{u} ⥤ Group :=
{ obj := λ X, Group.of Xˣ,
  map := λ X Y, units.map,
  map_id' := λ X, units.map_id _,
  map_comp' := λ X Y Z, units.map_comp }

/-- `units` as a functor. -/
@[to_additive AddCommMon.add_units "`add_units` as a functor."]
protected def CommMon.units : CommMon.{u} ⥤ CommGroup :=
{ obj := λ X, CommGroup.of Xˣ,
  map := λ X Y, units.map,
  map_id' := λ X, units.map_id _,
  map_comp' := λ X Y Z, units.map_comp }

/-- `Mon.units` is right adjoint to the forgetful functor. -/
@[to_additive forget_AddMon_add_units_adjunction "`AddMon.add_units` is right adjoint to the
forgetful functor."]
def forget_Mon_units_adjunction : forget₂ Group Mon ⊣ Mon.units.{u} :=
adjunction.mk_of_hom_equiv { hom_equiv := λ X Y, monoid_hom_units_equiv.symm }

/-- `CommMon.units` is right adjoint to the forgetful functor. -/
@[to_additive forget_AddMon_add_units_adjunction "`AddCommMon.add_units` is right adjoint to the
forgetful functor."]
def forget_CommMon_units_adjunction : forget₂ CommGroup CommMon ⊣ CommMon.units.{u} :=
adjunction.mk_of_hom_equiv
  { hom_equiv := λ X Y, (monoid_hom_units_equiv.symm : (X →* Y) ≃ (X →* Yˣ)) }

local attribute [reducible] with_zero

/-- The equivalence between `GroupWithZero` and `Group` induced by adding and removing `0`. -/
@[simps] noncomputable def GroupWithZero_equiv_Group : GroupWithZero ≌ Group :=
by classical; exact equivalence.mk
  (forget₂ GroupWithZero Mon ⋙ Mon.units) Group_to_GroupWithZero
  (nat_iso.of_components (λ X, GroupWithZero.iso.mk (with_zero_units_equiv X).symm) $ λ X Y f,
    monoid_with_zero_hom.ext $ λ a, begin
      change dite (f a = 0) _ _ = monoid_hom.with_zero (units.map _) (dite (a = 0) _ _),
      obtain rfl | h := eq_or_ne a 0,
      { rw [dif_pos (map_zero f), dif_pos rfl],
        refl },
      { rw [dif_neg (f.map_ne_zero.2 h), dif_neg h],
        congr,
        exact units.ext rfl }
    end)
  (nat_iso.of_components
    (λ X, mul_equiv.to_Group_iso (units_with_zero_equiv X)) $ λ X Y f, monoid_hom.ext $ λ a,
      begin
        have := (option.ne_none_iff_is_some.1 a.ne_zero),
        obtain ⟨(_ | a), _, _, _⟩ := a,
        { exact (option.ne_none_iff_is_some.2 this rfl).elim },
        { refl }
      end)

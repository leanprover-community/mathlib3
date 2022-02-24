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

section mul_one_class
variables [mul_one_class α] [mul_one_class β] [mul_one_class γ]

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

end mul_one_class

variables [monoid α] [monoid β] [monoid γ]

@[simps] protected def units (f : α →* β) : αˣ →* βˣ :=
{ to_fun := λ a, ⟨f a, f (a⁻¹ : αˣ),
    by rw [←map_mul, ←units.coe_mul, mul_inv_self, units.coe_one, map_one],
    by rw [←map_mul, ←units.coe_mul, inv_mul_self, units.coe_one, map_one]⟩,
  map_one' := units.ext f.map_one',
  map_mul' := λ a b, units.ext $ f.map_mul' _ _ }

protected lemma units_id : (monoid_hom.id α).units = monoid_hom.id _ := ext $ λ a, units.ext $ rfl

protected lemma units_comp (f : β →* γ) (g : α →* β) : (f.comp g).units = f.units.comp g.units :=
ext $ λ a, units.ext $ rfl

end monoid_hom

@[simp] lemma option.coe_get {α : Type*} {a : option α} (h : option.is_some a) :
  (↑(option.get h) : option α) = a :=
option.some_get _

section
local attribute [reducible] with_zero

/-- Any group is isomorphic to the units of itself adjoined with `0`. -/
def units_with_zero_equiv (α : Type*) [group α] : (with_zero α)ˣ ≃* α :=
{ to_fun    := λ a, option.get (option.ne_none_iff_is_some.1 a.ne_zero),
  inv_fun   := λ a, ⟨a, a⁻¹, mul_inv_cancel $ option.some_ne_none _,
    inv_mul_cancel $ option.some_ne_none _⟩,
  left_inv  := λ a, units.ext $ option.some_get _,
  right_inv := λ a, rfl,
  map_mul'  := λ a b, with_zero.coe_inj.1 $
    by simp only [units.coe_mul, option.coe_get, with_zero.coe_mul] }

@[nolint check_type] lemma with_zero.none_eq_zero {α : Type*} : (none : with_zero α) = 0 := rfl

/-- Any group with zero is isomorphic to its units adjoined with `0`. -/
def with_zero_units_equiv (α : Type*) [group_with_zero α] [decidable_eq α] : with_zero αˣ ≃* α :=
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
  map_mul'  := λ a b, with_zero.coe_inj.1 $
    by simp only [units.coe_mul, option.coe_get, with_zero.coe_mul] }

end

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

-- /-- `op` as a functor. -/
-- @[simps] def op : GroupWithZero ⥤ GroupWithZero :=
-- { obj := λ X, of Xᵐᵒᵖ, map := λ X Y, _ }

-- /-- The equivalence between `Preorder` and itself induced by `order_dual` both ways. -/
-- @[simps functor inverse] def dual_equiv : Preorder ≌ Preorder :=
-- equivalence.mk to_dual to_dual
--   (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
--   (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end GroupWithZero

/-- `with_zero` as a functor. -/
def Group_to_GroupWithZero : Group.{u} ⥤ GroupWithZero :=
{ obj := λ X, GroupWithZero.of (with_zero X),
  map := λ X Y, monoid_hom.with_zero,
  map_id' := λ X, fun_like.coe_injective $ begin
    simp only [fun_like.coe_fn_eq],
    exact monoid_hom.with_zero_id,
  end,
  map_comp' := λ X Y Z f g, fun_like.coe_injective $ begin
    simp only [fun_like.coe_fn_eq],
    exact monoid_hom.with_zero_comp _ _,
  end }

/-- `units` as a functor. -/
def Mon_to_Group : Mon.{u} ⥤ Group :=
{ obj := λ X, Group.of Xˣ,
  map := λ X Y f, monoid_hom.units f,
  map_id' := λ X, fun_like.coe_injective $
    by { simp only [fun_like.coe_fn_eq], exact monoid_hom.units_id },
  map_comp' := λ X Y Z f g, fun_like.coe_injective $
    by { simp only [fun_like.coe_fn_eq], exact monoid_hom.units_comp _ _ } }


def GroupWithZero_equiv_Group : GroupWithZero ≌ Group :=
by classical; exact equivalence.mk
  (forget₂ GroupWithZero Mon ⋙ Mon_to_Group) Group_to_GroupWithZero
  (nat_iso.of_components (λ X, GroupWithZero.iso.mk (with_zero_units_equiv X).symm) $ λ X Y f,
  monoid_with_zero_hom.ext $ λ a, begin
    unfold_projs,
    dsimp,
    sorry,
  end)
  (nat_iso.of_components (λ X, begin
    have := (units_with_zero_equiv X).to_Group_iso,
    convert this,
  end) _)

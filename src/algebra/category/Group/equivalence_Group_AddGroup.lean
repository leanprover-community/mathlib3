/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebra.category.Group.basic
import algebra.hom.equiv.type_tags

/-!
# Equivalence between `Group` and `AddGroup`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains two equivalences:
* `Group_AddGroup_equivalence` : the equivalence between `Group` and `AddGroup` by sending
  `X : Group` to `additive X` and `Y : AddGroup` to `multiplicative Y`.
* `CommGroup_AddCommGroup_equivalence` : the equivalence between `CommGroup` and `AddCommGroup` by
  sending `X : CommGroup` to `additive X` and `Y : AddCommGroup` to `multiplicative Y`.
-/

open category_theory

namespace Group

/--
The functor `Group ⥤ AddGroup` by sending `X ↦ additive X` and `f ↦ f`.
-/
@[simps] def to_AddGroup : Group ⥤ AddGroup :=
{ obj := λ X, AddGroup.of (additive X),
  map := λ X Y, monoid_hom.to_additive }

end Group

namespace CommGroup

/--
The functor `CommGroup ⥤ AddCommGroup` by sending `X ↦ additive X` and `f ↦ f`.
-/
@[simps] def to_AddCommGroup : CommGroup ⥤ AddCommGroup :=
{ obj := λ X, AddCommGroup.of (additive X),
  map := λ X Y, monoid_hom.to_additive }

end CommGroup

namespace AddGroup

/--
The functor `AddGroup ⥤ Group` by sending `X ↦ multiplicative Y` and `f ↦ f`.
-/
@[simps] def to_Group : AddGroup ⥤ Group :=
{ obj := λ X, Group.of (multiplicative X),
  map := λ X Y, add_monoid_hom.to_multiplicative }

end AddGroup

namespace AddCommGroup

/--
The functor `AddCommGroup ⥤ CommGroup` by sending `X ↦ multiplicative Y` and `f ↦ f`.
-/
@[simps] def to_CommGroup : AddCommGroup ⥤ CommGroup :=
{ obj := λ X, CommGroup.of (multiplicative X),
  map := λ X Y, add_monoid_hom.to_multiplicative }

end AddCommGroup

/--
The equivalence of categories between `Group` and `AddGroup`
-/
@[simps] def Group_AddGroup_equivalence : Group ≌ AddGroup :=
equivalence.mk Group.to_AddGroup AddGroup.to_Group
  (nat_iso.of_components
    (λ X, mul_equiv.to_Group_iso (mul_equiv.multiplicative_additive X))
    (λ X Y f, rfl))
  (nat_iso.of_components
    (λ X, add_equiv.to_AddGroup_iso (add_equiv.additive_multiplicative X))
    (λ X Y f, rfl))

/--
The equivalence of categories between `CommGroup` and `AddCommGroup`.
-/
@[simps] def CommGroup_AddCommGroup_equivalence : CommGroup ≌ AddCommGroup :=
equivalence.mk CommGroup.to_AddCommGroup AddCommGroup.to_CommGroup
  (nat_iso.of_components
    (λ X, mul_equiv.to_CommGroup_iso (mul_equiv.multiplicative_additive X))
    (λ X Y f, rfl))
  (nat_iso.of_components
    (λ X, add_equiv.to_AddCommGroup_iso (add_equiv.additive_multiplicative X))
    (λ X Y f, rfl))

/- Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Introduce Group -- the category of groups.

Currently only the basic setup.
Copied from `algebra/category/Mon/basic.lean`.
-/

import algebra.punit_instances
import category_theory.concrete_category

universes u v

open category_theory

/-- The category of groups and group morphisms. -/
@[reducible] def Group : Type (u+1) := bundled group

/-- The category of additive commutative groups and group morphisms. -/
@[reducible] def AddCommGroup : Type (u+1) := bundled add_comm_group

namespace Group

instance (G : Group) : group G := G.str

instance concrete_is_group_hom :
  concrete_category @is_group_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

def of (X : Type u) [group X] : Group := ⟨X⟩

instance hom_is_group_hom {G₁ G₂ : Group} (f : G₁ ⟶ G₂) :
  is_group_hom (f : G₁ → G₂) := f.2

instance : has_one Group := ⟨⟨punit⟩⟩

end Group

namespace AddCommGroup

instance (A : AddCommGroup) : add_comm_group A := A.str

@[reducible] def is_add_comm_group_hom {α β} [add_comm_group α] [add_comm_group β] (f : α → β) : Prop :=
is_add_group_hom f

instance concrete_is_comm_group_hom : concrete_category @is_add_comm_group_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

def of (X : Type u) [add_comm_group X] : AddCommGroup := ⟨X⟩

instance hom_is_comm_group_hom {A₁ A₂ : AddCommGroup} (f : A₁ ⟶ A₂) :
  is_add_comm_group_hom (f : A₁ → A₂) := f.2

/-- The forgetful functor from additive commutative groups to groups. -/
def forget_to_Group : AddCommGroup ⥤ Group :=
{ obj := λ A₁, ⟨multiplicative A₁⟩,
  map := λ A₁ A₂ f, ⟨f, multiplicative.is_group_hom f⟩ }

instance : faithful (forget_to_Group) := {}

instance : has_zero AddCommGroup := ⟨⟨punit⟩⟩

end AddCommGroup

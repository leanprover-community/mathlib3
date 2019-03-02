/- Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Introduce Group -- the category of groups.

Currently only the basic setup.
Copied from monoids.lean.
-/

import category_theory.concrete_category
import category_theory.fully_faithful

universes u v

open category_theory

namespace category_theory.instances

/-- The category of groups and group morphisms. -/
@[reducible] def Group : Type (u+1) := bundled group

instance (G : Group) : group G := G.str

instance concrete_is_group_hom :
  concrete_category @is_group_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

instance Group_hom_is_group_hom {G₁ G₂ : Group} (f : G₁ ⟶ G₂) :
  is_group_hom (f : G₁ → G₂) := f.2

instance : has_one Group := ⟨{ α := punit, str := by tidy }⟩

/-- The category of commutative groups and group morphisms. -/
@[reducible] def CommGroup : Type (u+1) := bundled comm_group

instance (x : CommGroup) : comm_group x := x.str

@[reducible] def is_comm_group_hom {α β} [comm_group α] [comm_group β] (f : α → β) : Prop :=
is_group_hom f

instance concrete_is_comm_group_hom : concrete_category @is_comm_group_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

instance CommGroup_hom_is_comm_group_hom {R S : CommGroup} (f : R ⟶ S) :
  is_comm_group_hom (f : R → S) := f.2

namespace CommGroup
/-- The forgetful functor from commutative groups to groups. -/
def forget_to_Group : CommGroup ⥤ Group :=
concrete_functor
  (by intros _ c; exact { ..c })
  (by introsI _ _ _ _ f i;  exact { ..i })

instance : faithful (forget_to_Group) := {}

instance : has_one CommGroup := ⟨{ α := punit, str := by tidy }⟩

end CommGroup

end category_theory.instances

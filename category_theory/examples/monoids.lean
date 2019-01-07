/- Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

Introduce Mon -- the category of monoids.

Currently only the basic setup.
-/

import category_theory.fully_faithful
import algebra.ring

universes u v

open category_theory

namespace category_theory.examples

/-- The category of monoids and monoid morphisms. -/
@[reducible] def Mon : Type (u+1) := bundled monoid

instance (x : Mon) : monoid x := x.str

instance concrete_is_monoid_hom : concrete_category @is_monoid_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

instance Mon_hom_is_monoid_hom {R S : Mon} (f : R ⟶ S) : is_monoid_hom (f : R → S) := f.2

/-- The category of commutative monoids and monoid morphisms. -/
@[reducible] def CommMon : Type (u+1) := bundled comm_monoid

instance (x : CommMon) : comm_monoid x := x.str

@[reducible] def is_comm_monoid_hom {α β} [comm_monoid α] [comm_monoid β] (f : α → β) : Prop :=
is_monoid_hom f

instance concrete_is_comm_monoid_hom : concrete_category @is_comm_monoid_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

instance CommMon_hom_is_comm_monoid_hom {R S : CommMon} (f : R ⟶ S) :
  is_comm_monoid_hom (f : R → S) := f.2

namespace CommMon
/-- The forgetful functor from commutative monoids to monoids. -/
def forget_to_Mon : CommMon ⥤ Mon :=
concrete_functor
  (by intros _ c; exact { ..c })
  (by introsI _ _ _ _ f i;  exact { ..i })

instance : faithful (forget_to_Mon) := {}

end CommMon

end category_theory.examples

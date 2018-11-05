/- Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl

Introduce CommRing -- the category of commutative rings.

Currently only the basic setup.
-/

import category_theory.examples.monoids
import category_theory.embedding
import algebra.ring

universes u v

open category_theory

namespace category_theory.examples

/-- The category of rings. -/
@[reducible] def Ring : Type (u+1) := bundled ring

instance (x : Ring) : ring x := x.str

instance concrete_is_ring_hom : concrete_category @is_ring_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

instance Ring_hom_is_ring_hom {R S : Ring} (f : R ⟶ S) : is_ring_hom (f : R → S) := f.2

/-- The category of commutative rings. -/
@[reducible] def CommRing : Type (u+1) := bundled comm_ring

instance (x : CommRing) : comm_ring x := x.str

@[reducible] def is_comm_ring_hom {α β} [comm_ring α] [comm_ring β] (f : α → β) : Prop :=
is_ring_hom f

instance concrete_is_comm_ring_hom : concrete_category @is_comm_ring_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

instance CommRing_hom_is_comm_ring_hom {R S : CommRing} (f : R ⟶ S) : is_comm_ring_hom (f : R → S) := f.2

namespace CommRing
/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
def forget_to_CommMon : CommRing ⥤ CommMon := 
concrete_functor
  (by intros _ c; exact { ..c })
  (by introsI _ _ _ _ f i;  exact { ..i })

instance : faithful (forget_to_CommMon) := {}

example : faithful (forget_to_CommMon ⋙ CommMon.forget_to_Mon) := by apply_instance
end CommRing

end category_theory.examples

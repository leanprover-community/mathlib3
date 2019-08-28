/- Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

Introduce Mon -- the category of monoids.

Currently only the basic setup.
-/

import category_theory.concrete_category algebra.group

universes u v

open category_theory

/-- The category of monoids and monoid morphisms. -/
@[reducible] def Mon : Type (u+1) := bundled monoid

/-- The category of commutative monoids and monoid morphisms. -/
@[reducible] def CommMon : Type (u+1) := bundled comm_monoid

namespace Mon

instance (x : Mon) : monoid x := x.str

instance concrete_is_monoid_hom : concrete_category @is_monoid_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

def of (X : Type u) [monoid X] : Mon := ⟨X⟩

abbreviation forget : Mon.{u} ⥤ Type u := forget

instance hom_is_monoid_hom {R S : Mon} (f : R ⟶ S) : is_monoid_hom (f : R → S) := f.2

/-- Morphisms in `Mon` are defined using `subtype is_monoid_hom`,
so we provide a canonical bijection with `R →* S`. -/
def hom_equiv_monoid_hom (R S : Mon) : (R ⟶ S) ≃ (R →* S) :=
{ to_fun := λ f, @as_monoid_hom _ _ _ _ f.val f.property,
  inv_fun := λ f, ⟨f, f.is_monoid_hom⟩,
  right_inv := λ f, by rcases f; refl,
  left_inv := λ f, by rcases f; refl }

end Mon

namespace CommMon

instance (x : CommMon) : comm_monoid x := x.str

@[reducible] def is_comm_monoid_hom {α β} [comm_monoid α] [comm_monoid β] (f : α → β) : Prop :=
is_monoid_hom f

instance concrete_is_comm_monoid_hom : concrete_category @is_comm_monoid_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

def of (X : Type u) [comm_monoid X] : CommMon := ⟨X⟩

abbreviation forget : CommMon.{u} ⥤ Type u := forget

instance hom_is_comm_monoid_hom {R S : CommMon} (f : R ⟶ S) :
  is_comm_monoid_hom (f : R → S) := f.2

/-- The forgetful functor from commutative monoids to monoids. -/
def forget_to_Mon : CommMon ⥤ Mon :=
concrete_functor
  (by intros _ c; exact { ..c })
  (by introsI _ _ _ _ f i;  exact { ..i })

instance : faithful (forget_to_Mon) := {}

end CommMon

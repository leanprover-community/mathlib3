/- Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl

Introduce CommRing -- the category of commutative rings.

Currently only the basic setup.
-/

import category_theory.examples.monoids
import category_theory.fully_faithful
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

-- Here we don't use the `concrete` machinery,
-- because it would require introducing a useless synonym for `is_ring_hom`.
instance : category CommRing :=
{ hom := λ R S, { f : R → S // is_ring_hom f },
  id := λ R, ⟨ id, by resetI; apply_instance ⟩,
  comp := λ R S T g h, ⟨ h.1 ∘ g.1, begin haveI := g.2, haveI := h.2, apply_instance end ⟩ }

instance CommRing_hom_coe {R S : CommRing} : has_coe_to_fun (R ⟶ S) :=
{ F := λ f, R → S,
  coe := λ f, f.1 }

@[simp] lemma CommRing_hom_coe_app {R S : CommRing} (f : R ⟶ S) (r : R) : f r = f.val r := rfl

instance CommRing_hom_is_ring_hom {R S : CommRing} (f : R ⟶ S) : is_ring_hom (f : R → S) := f.2

namespace CommRing
/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
def forget_to_CommMon : CommRing ⥤ CommMon :=
{ obj := λ X, { α := X.1, str := by apply_instance },
  map := λ X Y f, ⟨ f, by apply_instance ⟩ }

instance : faithful (forget_to_CommMon) := {}

example : faithful (forget_to_CommMon ⋙ CommMon.forget_to_Mon) := by apply_instance
end CommRing

end category_theory.examples

/- Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl

Introduce CommRing -- the category of commutative rings.
-/

import category_theory.instances.monoids
import category_theory.fully_faithful
import algebra.ring
import data.int.basic

universes u v

open category_theory

namespace category_theory.instances

/-- The category of rings. -/
@[reducible] def Ring : Type (u+1) := bundled ring

instance (x : Ring) : ring x := x.str

instance concrete_is_ring_hom : concrete_category @is_ring_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

instance Ring.hom_is_ring_hom {R S : Ring} (f : R ⟶ S) : is_ring_hom (f : R → S) := f.2

/-- The category of commutative rings. -/
@[reducible] def CommRing : Type (u+1) := bundled comm_ring

instance (x : CommRing) : comm_ring x := x.str

-- Here we don't use the `concrete` machinery,
-- because it would require introducing a useless synonym for `is_ring_hom`.
instance : category CommRing :=
{ hom := λ R S, { f : R → S // is_ring_hom f },
  id := λ R, ⟨ id, by resetI; apply_instance ⟩,
  comp := λ R S T g h, ⟨ h.1 ∘ g.1, begin haveI := g.2, haveI := h.2, apply_instance end ⟩ }

namespace CommRing
variables {R S T : CommRing.{u}}

@[simp] lemma id_val : subtype.val (𝟙 R) = id := rfl
@[simp] lemma comp_val (f : R ⟶ S) (g : S ⟶ T) :
  (f ≫ g).val = g.val ∘ f.val := rfl

instance hom_coe : has_coe_to_fun (R ⟶ S) :=
{ F := λ f, R → S,
  coe := λ f, f.1 }

@[extensionality] lemma hom.ext  {f g : R ⟶ S} : (∀ x : R, f x = g x) → f = g :=
λ w, subtype.ext.2 $ funext w

@[simp] lemma hom_coe_app (val : R → S) (prop) (r : R) : (⟨val, prop⟩ : R ⟶ S) r = val r := rfl

instance hom_is_ring_hom (f : R ⟶ S) : is_ring_hom (f : R → S) := f.2

def Int : CommRing := ⟨ℤ, infer_instance⟩

def Int.cast {R : CommRing} : Int ⟶ R := { val := int.cast, property := by apply_instance }

def int.eq_cast' {R : Type u} [ring R] (f : int → R) [is_ring_hom f] : f = int.cast :=
funext $ int.eq_cast f (is_ring_hom.map_one f) (λ _ _, is_ring_hom.map_add f)

def Int.hom_unique {R : CommRing} : unique (Int ⟶ R) :=
{ default := Int.cast,
  uniq := λ f, subtype.ext.mpr $ funext $ int.eq_cast f f.2.map_one f.2.map_add }

/-- The forgetful functor commutative rings to Type. -/
def forget : CommRing.{u} ⥤ Type u :=
{ obj := λ R, R,
  map := λ _ _ f, f }

instance forget.faithful : faithful (forget) := {}

/-- The functor from commutative rings to rings. -/
def to_Ring : CommRing.{u} ⥤ Ring.{u} :=
{ obj := λ X, { α := X.1, str := by apply_instance },
  map := λ X Y f, ⟨ f, by apply_instance ⟩ }

instance to_Ring.faithful : faithful (to_Ring) := {}

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
def forget_to_CommMon : CommRing.{u} ⥤ CommMon.{u} :=
{ obj := λ X, { α := X.1, str := by apply_instance },
  map := λ X Y f, ⟨ f, by apply_instance ⟩ }

instance forget_to_CommMon.faithful : faithful (forget_to_CommMon) := {}

example : faithful (forget_to_CommMon ⋙ CommMon.forget_to_Mon) := by apply_instance

end CommRing

end category_theory.instances

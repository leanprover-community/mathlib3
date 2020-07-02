/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.simple
import category_theory.isomorphism_classes

open category_theory.limits

namespace category_theory

universes v u w
variables {C : Type u} [category.{v} C]

variables (C)
variables [has_zero_morphisms C]

/-- `is_isomorphic` defines a setoid on the simple objects. -/
def simple_is_isomorphic_setoid : setoid (Σ (X : C), simple X) :=
{ r := λ X Y, is_isomorphic X.1 Y.1,
  iseqv := ⟨λ X, ⟨iso.refl X.1⟩, λ X Y ⟨α⟩, ⟨α.symm⟩, λ X Y Z ⟨α⟩ ⟨β⟩, ⟨α.trans β⟩⟩ }

/-- The isomorphism classes of simples in a category. -/
def iso_classes_of_simples : Type (max u v) := quotient (simple_is_isomorphic_setoid C)

local attribute [instance] simple_is_isomorphic_setoid

/-- An arbitrarily chosen representative of each isomorphism class of simple object. -/
noncomputable def simples : iso_classes_of_simples C → C :=
λ X, (quotient.out X).1

lemma simples_non_isomorphic {i j} (h : i ≠ j) (f : simples C i ≅ simples C j) : false :=
begin
  apply h, clear h,
  induction i, induction j,
  { apply quotient.sound,
    apply setoid.trans (setoid.symm (quotient.mk_out _)),
    exact setoid.trans ⟨f⟩ (quotient.mk_out _), },
  { refl, },
  { refl, },
end

variables {C}

/-- The isomorphism class of a simple object. -/
def simple.iso_class (X : C) [simple X] : iso_classes_of_simples C :=
quotient.mk ⟨X, by apply_instance⟩

/-- Every simple object is isomorphic to the chosen representative from its isomorphism class. -/
noncomputable def simple.iso_to_representative (X : C) [simple X] :
  X ≅ simples C (simple.iso_class X) :=
classical.choice (setoid.symm (quotient.mk_out (⟨X, by apply_instance⟩ : Σ (X : C), simple X)))

noncomputable instance simples_simple (X : iso_classes_of_simples C) : simple (simples C X) :=
(quotient.out X).2

end category_theory

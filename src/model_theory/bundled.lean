/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.elementary_maps
import category_theory.concrete_category.bundled
/-!
# Bundled First-Order Structures
This file bundles types together with their first-order structure.

## Main Definitions
* `first_order.language.Theory.Model` is the type of nonempty models of a particular theory.
* `first_order.language.equiv_setoid` is the isomorphism equivalence relation on bundled structures.

## TODO
* Define category structures on bundled structures and models.

-/

universes u v w w'

variables {L : first_order.language.{u v}}

@[protected] instance category_theory.bundled.Structure
  {L : first_order.language.{u v}} (M : category_theory.bundled.{w} L.Structure) :
  L.Structure M :=
M.str

namespace first_order
namespace language
open_locale first_order

/-- The equivalence relation on bundled `L.Structure`s indicating that they are isomorphic. -/
instance equiv_setoid : setoid (category_theory.bundled L.Structure) :=
{ r := λ M N, nonempty (M ≃[L] N),
  iseqv := ⟨λ M, ⟨equiv.refl L M⟩, λ M N, nonempty.map equiv.symm,
    λ M N P, nonempty.map2 (λ MN NP, NP.comp MN)⟩ }

variable (T : L.Theory)

namespace Theory

/-- The type of nonempty models of a first-order theory. -/
structure Model :=
(carrier : Type w)
[struc : L.Structure carrier]
[is_model : T.model carrier]
[nonempty' : nonempty carrier]

attribute [instance] Model.struc Model.is_model Model.nonempty'

namespace Model

instance : has_coe_to_sort T.Model (Type w) := ⟨Model.carrier⟩

@[simp] lemma carrier_eq_coe (M : T.Model) : M.carrier = M := rfl

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. -/
def of (M : Type w) [L.Structure M] [M ⊨ T] [nonempty M] :
  T.Model := ⟨M⟩

@[simp]
lemma coe_of (M : Type w) [L.Structure M] [M ⊨ T] [nonempty M] : (of T M : Type w) = M := rfl

instance (M : T.Model) : nonempty M := infer_instance

section inhabited

local attribute [instance] trivial_unit_structure

instance : inhabited (Model (∅ : L.Theory)) :=
⟨Model.of _ unit⟩

end inhabited

variable {T}

/-- Maps a bundled model along a bijection. -/
def equiv_induced {M : Model.{u v w} T} {N : Type w'} (e : M ≃ N) :
  Model.{u v w'} T :=
{ carrier := N,
  struc := e.induced_Structure,
  is_model := @equiv.Theory_model L M N _ e.induced_Structure T e.induced_Structure_equiv _,
  nonempty' := e.symm.nonempty }

/-- Shrinks a small model to a particular universe. -/
noncomputable def shrink (M : Model.{u v w} T) [small.{w'} M] :
  Model.{u v w'} T := equiv_induced (equiv_shrink M)

/-- Lifts a model to a particular universe. -/
def ulift (M : Model.{u v w} T) : Model.{u v (max w w')} T :=
  equiv_induced (equiv.ulift.symm : M ≃ _)

/-- The reduct of any model of `φ.on_Theory T` is a model of `T`. -/
@[simps] def reduct {L' : language} (φ : L →ᴸ L') (M : (φ.on_Theory T).Model) :
  T.Model :=
{ carrier := M,
  struc := φ.reduct M,
  nonempty' := M.nonempty',
  is_model := (@Lhom.on_Theory_model L L' M (φ.reduct M) _ φ _ T).1 M.is_model, }

instance left_Structure {L' : language} {T : (L.sum L').Theory} (M : T.Model) :
  L.Structure M :=
(Lhom.sum_inl : L →ᴸ L.sum L').reduct M

instance right_Structure {L' : language} {T : (L.sum L').Theory} (M : T.Model) :
  L'.Structure M :=
(Lhom.sum_inr : L' →ᴸ L.sum L').reduct M

end Model

variables {T}

/-- Bundles `M ⊨ T` as a `T.Model`. -/
def model.bundled {M : Type w} [LM : L.Structure M] [ne : nonempty M] (h : M ⊨ T) :
  T.Model :=
@Model.of L T M LM h ne

@[simp]
lemma coe_of {M : Type w} [L.Structure M] [nonempty M] (h : M ⊨ T) :
  (h.bundled : Type w) = M := rfl

end Theory

/-- An elementary substructure of a bundled model as a bundled model. -/
def elementary_substructure.to_Model {M : T.Model} (S : L.elementary_substructure M) : T.Model :=
Theory.Model.of T S

instance {M : T.Model} (S : L.elementary_substructure M) [h : small S] :
  small (S.to_Model T) :=
h

end language
end first_order

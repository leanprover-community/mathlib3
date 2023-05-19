/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.elementary_maps
import category_theory.concrete_category.bundled
/-!
# Bundled First-Order Structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
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

open_locale first_order cardinal

namespace equiv

variables (L) {M : Type w} [L.Structure M] {N : Type w'} (g : M ≃ N)

/-- A type bundled with the structure induced by an equivalence. -/
@[simps] def bundled_induced  :
  category_theory.bundled.{w'} L.Structure :=
⟨N, g.induced_Structure⟩

/-- An equivalence of types as a first-order equivalence to the bundled structure on the codomain.
-/
@[simp] def bundled_induced_equiv :
  M ≃[L] g.bundled_induced L :=
g.induced_Structure_equiv

end equiv

namespace first_order
namespace language

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

local attribute [instance] inhabited.trivial_structure

instance : inhabited (Model.{u v w} (∅ : L.Theory)) :=
⟨Model.of _ punit⟩

end inhabited

variable {T}

/-- Maps a bundled model along a bijection. -/
def equiv_induced {M : Model.{u v w} T} {N : Type w'} (e : M ≃ N) :
  Model.{u v w'} T :=
{ carrier := N,
  struc := e.induced_Structure,
  is_model := @equiv.Theory_model L M N _ e.induced_Structure T e.induced_Structure_equiv _,
  nonempty' := e.symm.nonempty }

instance of_small (M : Type w) [nonempty M] [L.Structure M] [M ⊨ T] [h : small.{w'} M] :
  small.{w'} (Model.of T M) := h

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

/-- When `φ` is injective, `default_expansion` expands a model of `T` to a model of `φ.on_Theory T`
  arbitrarily. -/
@[simps] noncomputable def default_expansion {L' : language} {φ : L →ᴸ L'} (h : φ.injective)
  [∀ n (f : L'.functions n), decidable (f ∈ set.range (λ (f : L.functions n), φ.on_function f))]
  [∀ n (r : L'.relations n), decidable (r ∈ set.range (λ (r : L.relations n), φ.on_relation r))]
  (M : T.Model) [inhabited M] :
  (φ.on_Theory T).Model :=
{ carrier := M,
  struc := φ.default_expansion M,
  nonempty' := M.nonempty',
  is_model := (@Lhom.on_Theory_model L L' M _ (φ.default_expansion M) φ
    (h.is_expansion_on_default M) T).2 M.is_model, }

instance left_Structure {L' : language} {T : (L.sum L').Theory} (M : T.Model) :
  L.Structure M :=
(Lhom.sum_inl : L →ᴸ L.sum L').reduct M

instance right_Structure {L' : language} {T : (L.sum L').Theory} (M : T.Model) :
  L'.Structure M :=
(Lhom.sum_inr : L' →ᴸ L.sum L').reduct M

/-- A model of a theory is also a model of any subtheory. -/
@[simps] def subtheory_Model (M : T.Model) {T' : L.Theory} (h : T' ⊆ T) :
  T'.Model :=
{ carrier := M,
  is_model := ⟨λ φ hφ, realize_sentence_of_mem T (h hφ)⟩ }

instance subtheory_Model_models (M : T.Model) {T' : L.Theory} (h : T' ⊆ T) :
  M.subtheory_Model h ⊨ T :=
M.is_model

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

/-- A structure that is elementarily equivalent to a model, bundled as a model. -/
def elementarily_equivalent.to_Model {M : T.Model} {N : Type*} [LN : L.Structure N] (h : M ≅[L] N) :
  T.Model :=
{ carrier := N,
  struc := LN,
  nonempty' := h.nonempty,
  is_model := h.Theory_model }

/-- An elementary substructure of a bundled model as a bundled model. -/
def elementary_substructure.to_Model {M : T.Model} (S : L.elementary_substructure M) : T.Model :=
S.elementarily_equivalent.symm.to_Model T

instance {M : T.Model} (S : L.elementary_substructure M) [h : small S] :
  small (S.to_Model T) :=
h

end language
end first_order

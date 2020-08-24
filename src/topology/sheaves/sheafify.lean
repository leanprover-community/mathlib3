/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.local_predicate
import topology.sheaves.stalks

/-!
# Sheafification of `Type` valued presheaves
-/

universes v

noncomputable theory

open Top
open opposite
open topological_space

variables {X : Top.{v}} (F : presheaf (Type v) X)

namespace Top.presheaf

namespace sheafify

/--
The prelocal predicate on functions into the stalks, asserting that the function is equal to a germ.
-/
def is_germ : prelocal_predicate (λ x, F.stalk x) :=
{ pred := λ U f, ∃ (g : F.obj (op U)), ∀ x : U, f x = F.germ x g,
  res := λ V U i f ⟨g, p⟩, ⟨F.map i.op g, λ x, (p (i x)).trans (F.germ_res_apply _ _ _).symm⟩, }

/--
The local predicate on functions into the stalks,
asserting that the function is locally equal to a germ.
-/
def is_locally_germ : local_predicate (λ x, F.stalk x) := (is_germ F).sheafify

end sheafify

/--
The sheafification of a `Type` valued presheaf, defined as the functions into the stalks which
are locally equal to germs.
-/
def sheafify : sheaf (Type v) X :=
subsheaf_to_Types (sheafify.is_locally_germ F)

/--
The morphism from a presheaf to its sheafification.
-/
def to_sheafify : F ⟶ F.sheafify.presheaf :=
{ app := λ U f, ⟨λ x, F.germ x f, prelocal_predicate.sheafify_of ⟨f, λ x, rfl⟩⟩, }

def foo (x : X) : F.sheafify.presheaf.stalk x ⟶ F.stalk x :=
stalk_to_fiber _ x

lemma stalk_to_fiber_surjective (x : X) : function.surjective (foo F x) :=
begin
  apply stalk_to_fiber_surjective,
  intro t,
  induction t,
  { rcases t with ⟨U, s⟩,
    revert s,
    rw [(show U = op (unop U), from rfl)],
    generalize : unop U = V, clear U,
    intro s,
    use V,
    cases V,
    fsplit,
    { exact λ y, F.germ y s, },
    { fsplit,
      { apply prelocal_predicate.sheafify_of, exact ⟨s, λ x, rfl⟩, },
      { exact quot.sound ⟨𝟙 _, by { dsimp, erw category_theory.functor.map_id, refl, }⟩, }, }, },
  { refl, },
end

lemma stalk_to_fiber_injective (x : X) : function.injective (foo F x) :=
begin
  apply stalk_to_fiber_injective,
  intros,
  rcases hU ⟨x, U.2⟩ with ⟨U', mU, iU, gU, wU⟩,
  rcases hV ⟨x, V.2⟩ with ⟨V', mV, iV, gV, wV⟩,
  have wUx := wU ⟨x, mU⟩,
  dsimp at wUx, erw wUx at e, clear wUx,
  have wVx := wV ⟨x, mV⟩,
  dsimp at wVx, erw wVx at e, clear wVx,
  rcases F.germ_eq x mU mV gU gV e with ⟨W, mW, iU', iV', e'⟩,
  use ⟨W ⊓ (U' ⊓ V'), ⟨mW, mU, mV⟩⟩,
  fsplit,
  change W ⊓ (U' ⊓ V') ⟶ U.val,
  exact (opens.inf_le_right _ _) ≫ (opens.inf_le_left _ _) ≫ iU,
  fsplit,
  change W ⊓ (U' ⊓ V') ⟶ V.val,
  exact (opens.inf_le_right _ _) ≫ (opens.inf_le_right _ _) ≫ iV,
  intro w,
  dsimp,
  specialize wU ⟨w.1, w.2.2.1⟩,
  dsimp at wU,
  specialize wV ⟨w.1, w.2.2.2⟩,
  dsimp at wV,
  erw [wU, ←F.germ_res_apply iU' ⟨w, w.2.1⟩ gU, e', F.germ_res_apply, ←wV],
  refl,
end

def sheafify_stalk_iso (x : X) : F.stalk x ≅ F.sheafify.presheaf.stalk x :=
(equiv.of_bijective _ ⟨stalk_to_fiber_injective _ _, stalk_to_fiber_surjective _ _⟩).to_iso.symm

-- TODO functoriality

end Top.presheaf

/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.local_predicate
import topology.sheaves.stalks

/-!
# Sheafification of `Type` valued presheaves

We construct the sheafification of a `Type` valued presheaf,
as the subsheaf of dependent functions into the stalks
consisting of functions which are locally germs.

We show that the stalks of the sheafification are isomorphic to the original stalks,
via `stalk_to_fiber` which evaluates a germ of a dependent function at a point.

We construct a morphism `to_sheafify` from a presheaf to (the underlying presheaf of)
its sheafification, given by sending a section to its collection of germs.

## Future work
Show that the map induced on stalks by `to_sheafify` is the inverse of `stalk_to_fiber`.

Show sheafification is a functor from presheaves to sheaves,
and that it is the left adjoint of the forgetful functor,
following <https://stacks.math.columbia.edu/tag/007X>.
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
The morphism from a presheaf to its sheafification,
sending each section to its germs.
(This forms the unit of the adjunction.)
-/
def to_sheafify : F ⟶ F.sheafify.1 :=
{ app := λ U f, ⟨λ x, F.germ x f, prelocal_predicate.sheafify_of ⟨f, λ x, rfl⟩⟩,
  naturality' := λ U U' f, by { ext x ⟨u, m⟩, exact germ_res_apply F f.unop ⟨u, m⟩ x } }

/--
The natural morphism from the stalk of the sheafification to the original stalk.
In `sheafify_stalk_iso` we show this is an isomorphism.
-/
def stalk_to_fiber (x : X) : F.sheafify.1.stalk x ⟶ F.stalk x :=
stalk_to_fiber (sheafify.is_locally_germ F) x

lemma stalk_to_fiber_surjective (x : X) : function.surjective (F.stalk_to_fiber x) :=
begin
  apply stalk_to_fiber_surjective,
  intro t,
  obtain ⟨U, m, s, rfl⟩ := F.germ_exist _ t,
  { use ⟨U, m⟩,
    fsplit,
    { exact λ y, F.germ y s, },
    { exact ⟨prelocal_predicate.sheafify_of ⟨s, (λ _, rfl)⟩, rfl⟩, }, },
end

lemma stalk_to_fiber_injective (x : X) : function.injective (F.stalk_to_fiber x) :=
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
  dsimp at e',
  use ⟨W ⊓ (U' ⊓ V'), ⟨mW, mU, mV⟩⟩,
  refine ⟨_, _, _⟩,
  { change W ⊓ (U' ⊓ V') ⟶ U.val,
    exact (opens.inf_le_right _ _) ≫ (opens.inf_le_left _ _) ≫ iU, },
  { change W ⊓ (U' ⊓ V') ⟶ V.val,
    exact (opens.inf_le_right _ _) ≫ (opens.inf_le_right _ _) ≫ iV, },
  { intro w,
    dsimp,
    specialize wU ⟨w.1, w.2.2.1⟩,
    dsimp at wU,
    specialize wV ⟨w.1, w.2.2.2⟩,
    dsimp at wV,
    erw [wU, ←F.germ_res iU' ⟨w, w.2.1⟩, wV, ←F.germ_res iV' ⟨w, w.2.1⟩,
      category_theory.types_comp_apply, category_theory.types_comp_apply, e'] },
end

/--
The isomorphism betweeen a stalk of the sheafification and the original stalk.
-/
def sheafify_stalk_iso (x : X) : F.sheafify.1.stalk x ≅ F.stalk x :=
(equiv.of_bijective _ ⟨stalk_to_fiber_injective _ _, stalk_to_fiber_surjective _ _⟩).to_iso

-- PROJECT functoriality, and that sheafification is the left adjoint of the forgetful functor.

variables {F} {G : presheaf (Type v) X}

def sheafify_map (T : F ⟶ G) : F.sheafify ⟶ G.sheafify :=
{ app := λ U f,
    ⟨λ x, (stalk_functor _ x.1).map T (f.1 x),
     λ x, begin
      obtain ⟨V, hxV, ι, ⟨f', hf'⟩⟩ := f.2 x,
        -- notice that ι : V ⟶ unop U, I'm not sure why the API is mixing
        -- (opens X) and (opens X)ᵒᵖ here...
      refine ⟨V, hxV, ι, _⟩,
      exact ⟨T.app _ f', λ x',
      begin
        simp only [subtype.val_eq_coe] at ⊢ hf', rw hf',
        exact stalk_functor_map_germ_apply V x' T f',
      end⟩,
    end⟩,
  naturality' := λ U V res, begin
    ext f x,
    simp only [category_theory.types_comp_apply, subtype.coe_mk],
    change _ = (stalk_functor (Type v) x.val).map T _,
    congr,
  end, }

lemma sheafify_id (F : X.presheaf (Type v)) :
  sheafify_map (𝟙 F) = 𝟙 F.sheafify :=
begin
  ext U f x,
  unfold sheafify_map, simp,
end

lemma sheafify_comp {F G H : X.presheaf (Type v)} (T1 : F ⟶ G) (T2 : G ⟶ H) :
  sheafify_map (T1 ≫ T2) = sheafify_map T1 ≫ sheafify_map T2 :=
begin
  ext U f x,
  unfold sheafify_map, simp,
end

def sheafification : presheaf (Type v) X ⥤ sheaf (Type v) X :=
{ obj := λ F : presheaf (Type v) X, F.sheafify,
  map := λ F G T, sheafify_map T,
  map_id' := sheafify_id,
  map_comp' := λ _ _ _ T1 T2, sheafify_comp T1 T2,
}


end Top.presheaf

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
  res := λ V U i f ⟨g, p⟩, ⟨F.map i.op g, λ x, (p (i x)).trans (F.germ_res _ _ _).symm⟩, }

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
begin
  -- Pick some representative of `f`,
  fapply quot.lift,
  { rintro ⟨U, ⟨g, p⟩⟩,
    specialize p ⟨x, (unop U).2⟩,
    -- `p` consists of evidence that on some open set `V`, `g` is at each point the germ of some `s`.
    choose V m i s p using p,
    -- We use the germ of `s` at `x`.
    exact F.germ ⟨x, m⟩ s, },
  { rintro ⟨Ua, ⟨ga, pa⟩⟩ ⟨Ub, ⟨gb, pb⟩⟩ ⟨i, h⟩,
    injection h with h',
    specialize pa ⟨x, (unop Ua).2⟩,
    specialize pb ⟨x, (unop Ub).2⟩,
    choose Va ma ia sa pa using pa,
    choose Vb mb ib sb pb using pb,
    dsimp at i h,
    dsimp,
    let V := Va ⊓ Vb,
    let m : x ∈ V := ⟨ma, mb⟩,
    let s : F.obj (op V) := F.map (opens.inf_le_left _ _).op sa,
    transitivity F.germ ⟨x, m⟩ s,
    sorry,
    sorry, },
end

-- TODO check the stalks are correct
def sheafify_stalk_iso (x : X) : F.stalk x ≅ F.sheafify.presheaf.stalk x :=
{ hom := (stalk_functor (Type v) x).map (F.to_sheafify),
  inv := sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

-- TODO functoriality

end Top.presheaf

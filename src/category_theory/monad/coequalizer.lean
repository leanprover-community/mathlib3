/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes.reflexive
import category_theory.limits.shapes.split_coequalizer
import category_theory.monad.algebra

/-!
# Special coequalizers associated to a monad

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Associated to a monad `T : C ⥤ C` we have important coequalizer constructions:
Any algebra is a coequalizer (in the category of algebras) of free algebras. Furthermore, this
coequalizer is reflexive.
In `C`, this cofork diagram is a split coequalizer (in particular, it is still a coequalizer).
This split coequalizer is known as the Beck coequalizer (as it features heavily in Beck's
monadicity theorem).
-/
universes v₁ u₁

namespace category_theory
namespace monad
open limits

variables {C : Type u₁}
variables [category.{v₁} C]
variables {T : monad C} (X : algebra T)

/-!
Show that any algebra is a coequalizer of free algebras.
-/

/-- The top map in the coequalizer diagram we will construct. -/
@[simps]
def free_coequalizer.top_map : (monad.free T).obj (T.obj X.A) ⟶ (monad.free T).obj X.A :=
(monad.free T).map X.a

/-- The bottom map in the coequalizer diagram we will construct. -/
@[simps]
def free_coequalizer.bottom_map : (monad.free T).obj (T.obj X.A) ⟶ (monad.free T).obj X.A :=
{ f := T.μ.app X.A,
  h' := T.assoc X.A }

/-- The cofork map in the coequalizer diagram we will construct. -/
@[simps]
def free_coequalizer.π : (monad.free T).obj X.A ⟶ X :=
{ f := X.a,
  h' := X.assoc.symm }

lemma free_coequalizer.condition :
  free_coequalizer.top_map X ≫ free_coequalizer.π X =
  free_coequalizer.bottom_map X ≫ free_coequalizer.π X :=
algebra.hom.ext _ _ X.assoc.symm

instance : is_reflexive_pair (free_coequalizer.top_map X) (free_coequalizer.bottom_map X) :=
begin
  apply is_reflexive_pair.mk' _ _ _,
  apply (free T).map (T.η.app X.A),
  { ext,
    dsimp,
    rw [← functor.map_comp, X.unit, functor.map_id] },
  { ext,
    apply monad.right_unit }
end

/--
Construct the Beck cofork in the category of algebras. This cofork is reflexive as well as a
coequalizer.
-/
@[simps]
def beck_algebra_cofork : cofork (free_coequalizer.top_map X) (free_coequalizer.bottom_map X) :=
cofork.of_π _ (free_coequalizer.condition X)

/--
The cofork constructed is a colimit. This shows that any algebra is a (reflexive) coequalizer of
free algebras.
-/
def beck_algebra_coequalizer : is_colimit (beck_algebra_cofork X) :=
cofork.is_colimit.mk' _ $ λ s,
begin
  have h₁ : (T : C ⥤ C).map X.a ≫ s.π.f = T.μ.app X.A ≫ s.π.f :=
    congr_arg monad.algebra.hom.f s.condition,
  have h₂ : (T : C ⥤ C).map s.π.f ≫ s.X.a = T.μ.app X.A ≫ s.π.f := s.π.h,
  refine ⟨⟨T.η.app _ ≫ s.π.f, _⟩, _, _⟩,
  { dsimp,
    rw [functor.map_comp, category.assoc, h₂, monad.right_unit_assoc,
        (show X.a ≫ _ ≫ _ = _, from T.η.naturality_assoc _ _), h₁, monad.left_unit_assoc] },
  { ext,
    simpa [← T.η.naturality_assoc, T.left_unit_assoc] using T.η.app ((T : C ⥤ C).obj X.A) ≫= h₁ },
  { intros m hm,
    ext,
    dsimp only,
    rw ← hm,
    apply (X.unit_assoc _).symm }
end

/-- The Beck cofork is a split coequalizer. -/
def beck_split_coequalizer : is_split_coequalizer (T.map X.a) (T.μ.app _) X.a :=
⟨T.η.app _, T.η.app _, X.assoc.symm, X.unit, T.left_unit _, (T.η.naturality _).symm⟩

/-- This is the Beck cofork. It is a split coequalizer, in particular a coequalizer. -/
@[simps X]
def beck_cofork : cofork (T.map X.a) (T.μ.app _) :=
(beck_split_coequalizer X).as_cofork

@[simp] lemma beck_cofork_π : (beck_cofork X).π = X.a := rfl

/-- The Beck cofork is a coequalizer. -/
def beck_coequalizer : is_colimit (beck_cofork X) :=
(beck_split_coequalizer X).is_coequalizer

@[simp] lemma beck_coequalizer_desc (s : cofork (T.to_functor.map X.a) (T.μ.app X.A)) :
  (beck_coequalizer X).desc s = T.η.app _ ≫ s.π := rfl

end monad
end category_theory

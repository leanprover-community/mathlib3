/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebraic_geometry.Spec

/-!
# The category of schemes

A scheme is a locally ringed space such that every point is contained in some open set
where there is an isomorphism of presheaves between the restriction to that open set,
and the structure sheaf of `Spec R`, for some commutative ring `R`.

A morphism of schemes is just a morphism of the underlying locally ringed spaces.

-/

noncomputable theory

open topological_space
open category_theory
open Top
open opposite

namespace algebraic_geometry

set_option profiler true

/--
We define `Scheme` as a `X : LocallyRingedSpace`,
along with a proof that every point has an open neighbourhood `U`
so that that the restriction of `X` to `U` is isomorphic,
as a space with a presheaf of commutative rings,
to `Spec.PresheafedSpace R` for some `R : CommRing`.

(Note we're not asking in the definition that this is an isomorphism as locally ringed spaces,
although that is a consequence.)
-/
structure Scheme extends X : LocallyRingedSpace :=
(local_affine : ∀ x : X, ∃ (U : open_nhds x) (R : CommRing),
  nonempty (X.to_PresheafedSpace.restrict _ U.open_embedding ≅ Spec.to_PresheafedSpace.obj (op R)))

-- PROJECT
-- In fact, we can make the isomorphism `i` above an isomorphism in `LocallyRingedSpace`.
-- However this is a consequence of the above definition, and not necessary for defining schemes.
-- We haven't done this yet because we haven't shown that you can restrict a `LocallyRingedSpace`
-- along an open embedding.
-- We can do this already for `SheafedSpace` (as above), but we need to know that
-- the stalks of the restriction are still local rings, which we follow if we knew that
-- the stalks didn't change.
-- This will follow if we define cofinal functors, and show precomposing with a cofinal functor
-- doesn't change colimits, because open neighbourhoods of `x` within `U` are cofinal in
-- all open neighbourhoods of `x`.

namespace Scheme

/--
Every `Scheme` is a `LocallyRingedSpace`.
-/
-- (This parent projection is apparently not automatically generated because
-- we used the `extends X : LocallyRingedSpace` syntax.)
def to_LocallyRingedSpace (S : Scheme) : LocallyRingedSpace := { ..S }

/--
Schemes are a full subcategory of locally ringed spaces.
-/
instance : category Scheme :=
induced_category.category Scheme.to_LocallyRingedSpace

/--
`Spec R` as a `Scheme`.
-/
def Spec_obj (R : CommRing) : Scheme :=
{ local_affine := λ x, ⟨⟨⊤, trivial⟩, R, ⟨(Spec.to_PresheafedSpace.obj (op R)).restrict_top_iso⟩⟩,
  .. Spec.LocallyRingedSpace_obj R }

def Spec_map {R S : CommRing} (f : R ⟶ S) :
  Spec_obj S ⟶ Spec_obj R :=
Spec.LocallyRingedSpace_map f

def Spec : CommRingᵒᵖ ⥤ Scheme :=
{ obj := λ R, Spec_obj (unop R),
  map := λ R S f, Spec_map f.unop,
  map_id' := sorry,
  map_comp' := sorry }

/--
The empty scheme, as `Spec 0`.
-/
def empty : Scheme :=
Spec_obj (CommRing.of punit)

instance : has_emptyc Scheme := ⟨empty⟩

instance : inhabited Scheme := ⟨∅⟩

/--
The global sections, notated Gamma.
-/
def Γ : Schemeᵒᵖ ⥤ CommRing :=
(induced_functor Scheme.to_LocallyRingedSpace).op ⋙ LocallyRingedSpace.Γ

lemma Γ_def : Γ = (induced_functor Scheme.to_LocallyRingedSpace).op ⋙ LocallyRingedSpace.Γ := rfl

@[simp] lemma Γ_obj (X : Schemeᵒᵖ) : Γ.obj X = (unop X).presheaf.obj (op ⊤) := rfl

lemma Γ_obj_op (X : Scheme) : Γ.obj (op X) = X.presheaf.obj (op ⊤) := rfl

@[simp] lemma Γ_map {X Y : Schemeᵒᵖ} (f : X ⟶ Y) :
  Γ.map f = f.unop.1.c.app (op ⊤) ≫ (unop Y).presheaf.map (opens.le_map_top _ _).op := rfl

lemma Γ_map_op {X Y : Scheme} (f : X ⟶ Y) :
  Γ.map f.op = f.1.c.app (op ⊤) ≫ X.presheaf.map (opens.le_map_top _ _).op := rfl

-- PROJECTS:
-- 1. Construct `Spec ≫ Γ ≅ functor.id _`.
-- 2. Adjunction between `Γ` and `Spec`.
--

end Scheme

end algebraic_geometry

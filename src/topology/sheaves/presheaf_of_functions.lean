/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.presheaf
import topology.category.TopCommRing
import topology.algebra.continuous_functions

universes v u

open category_theory
open topological_space
open opposite

namespace Top

variables {X Y : Top.{v}}

-- TODO move these instances

instance opens_hom_has_coe_to_fun {U V : opens X} : has_coe_to_fun (U ⟶ V) :=
{ F := λ f, U → V,
  coe := λ f x, ⟨x, f.down.down x.2⟩ }

lemma opens.hom_open_embedding {U V : opens X} (i : U ⟶ V) : open_embedding i :=
{ inj := set.inclusion_injective i.down.down,
  induced := (@induced_compose _ _ _ _ i coe).symm,
  open_range :=
  begin
    have := set.range_inclusion i.down.down,
    erw this,
    simp,
    apply continuous_subtype_val,
    exact U.property,
  end, }

instance opens_op_hom_has_coe_to_fun {U V : (opens X)ᵒᵖ} : has_coe_to_fun (U ⟶ V) :=
{ F := λ f, (unop V) → (unop U),
  coe := λ f x, ⟨x, f.unop.down.down x.2⟩ }

variables (X Y)

/--
The presheaf of dependently typed functions on `X`, with fibres given by a type family `f`.
There is no requirement that the functions are continuous, here.
-/
def presheaf_to_Types (f : X → Type v) : X.presheaf (Type v) :=
{ obj := λ U, Π x : (unop U), f x,
  map := λ U V i g, λ (x : unop V), g (i x) }

def presheaf_to_Type (T : Type v) : X.presheaf (Type v) :=
-- (opens.to_Top X ⋙ forget Top).op ⋙ (yoneda.obj T)
{ obj := λ U, (unop U) → T,
  map := λ U V i g, λ (x : unop V), g (i x) }

@[simp] lemma presheaf_to_Type_map
  {T : Type v} {U V : (opens X)ᵒᵖ} {i : U ⟶ V} {f} :
  (presheaf_to_Type X T).map i f = f ∘ i :=
rfl

@[simp] lemma presheaf_to_Type_map_apply
  {T : Type v} {U V : (opens X)ᵒᵖ} {i : U ⟶ V} {f} {x} {mem} :
  (presheaf_to_Type X T).map i f ⟨x, mem⟩ = f ⟨x, i.unop.down.down mem⟩ :=
rfl

/-- The presheaf of continuous functions on `X` with values in fixed target topological space `T`. -/
def presheaf_to_Top (T : Top.{v}) : X.presheaf (Type v) :=
(opens.to_Top X).op ⋙ (yoneda.obj T)

-- TODO is this actually useful? I wish I knew how to write this with the coercion.
@[simp] lemma presheaf_to_Top_map_apply
  {T : Top.{v}} {U V : (opens X)ᵒᵖ} {i : U ⟶ V} {f} {x} {mem} :
  (((presheaf_to_Top X T).map i f).to_fun) ⟨x, mem⟩ = f.to_fun ⟨x, i.unop.down.down mem⟩ :=
rfl

/-- The (bundled) commutative ring of continuous functions from a topological space
to a topological commutative ring, with pointwise multiplication. -/
-- TODO upgrade the result to TopCommRing?
def continuous_functions (X : Top.{v}ᵒᵖ) (R : TopCommRing.{v}) : CommRing.{v} :=
CommRing.of (unop X ⟶ (forget₂ TopCommRing Top).obj R)

namespace continuous_functions

/-- Pulling back functions into a topological ring along a continuous map is a ring homomorphism. -/
def pullback {X Y : Topᵒᵖ} (f : X ⟶ Y) (R : TopCommRing) :
  continuous_functions X R ⟶ continuous_functions Y R :=
{ to_fun := λ g, f.unop ≫ g,
  map_one' := rfl,
  map_zero' := rfl,
  map_add' := by tidy,
  map_mul' := by tidy }

/-- A homomorphism of topological rings can be postcomposed with functions from a source space `X`;
this is a ring homomorphism (with respect to the pointwise ring operations on functions). -/
def map (X : Top.{u}ᵒᵖ) {R S : TopCommRing.{u}} (φ : R ⟶ S) :
  continuous_functions X R ⟶ continuous_functions X S :=
{ to_fun := λ g, g ≫ ((forget₂ TopCommRing Top).map φ),
  map_one' := by ext; exact φ.1.map_one,
  map_zero' := by ext; exact φ.1.map_zero,
  map_add' := by intros; ext; apply φ.1.map_add,
  map_mul' := by intros; ext; apply φ.1.map_mul }
end continuous_functions

/-- An upgraded version of the Yoneda embedding, observing that the continuous maps
from `X : Top` to `R : TopCommRing` form a commutative ring, functorial in both `X` and `R`. -/
def CommRing_yoneda : TopCommRing.{u} ⥤ (Top.{u}ᵒᵖ ⥤ CommRing.{u}) :=
{ obj := λ R,
  { obj := λ X, continuous_functions X R,
    map := λ X Y f, continuous_functions.pullback f R },
  map := λ R S φ,
  { app := λ X, continuous_functions.map X φ } }

/-- The presheaf (of commutative rings), consisting of functions on an open set `U ⊆ X` with
values in some topological commutative ring `T`. -/
def presheaf_to_TopCommRing (T : TopCommRing.{v}) :
  X.presheaf CommRing.{v} :=
(opens.to_Top X).op ⋙ (CommRing_yoneda.obj T)

/-- The presheaf (of commutative rings) of real valued functions. -/
noncomputable def presheaf_ℝ (Y : Top) : Y.presheaf CommRing :=
presheaf_to_TopCommRing Y (TopCommRing.of ℝ)

/-- The presheaf (of commutative rings) of complex valued functions. -/
noncomputable def presheaf_ℂ (Y : Top) : Y.presheaf CommRing :=
presheaf_to_TopCommRing Y (TopCommRing.of ℂ)

end Top

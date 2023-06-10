/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro
-/
import category_theory.concrete_category.bundled_hom
import category_theory.elementwise
import topology.continuous_function.basic

/-!
# Category instance for topological spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We introduce the bundled category `Top` of topological spaces together with the functors `discrete`
and `trivial` from the category of types to `Top` which equip a type with the corresponding
discrete, resp. trivial, topology. For a proof that these functors are left, resp. right adjoint
to the forgetful functor, see `topology.category.Top.adjunctions`.
-/

open category_theory
open topological_space

universe u

/-- The category of topological spaces and continuous maps. -/
def Top : Type (u+1) := bundled topological_space

namespace Top

instance bundled_hom : bundled_hom @continuous_map :=
⟨@continuous_map.to_fun, @continuous_map.id, @continuous_map.comp, @continuous_map.coe_injective⟩

attribute [derive [large_category, concrete_category]] Top

instance : has_coe_to_sort Top Type* := bundled.has_coe_to_sort

instance topological_space_unbundled (x : Top) : topological_space x := x.str

@[simp] lemma id_app (X : Top.{u}) (x : X) :
  (𝟙 X : X → X) x = x := rfl

@[simp] lemma comp_app {X Y Z : Top.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g : X → Z) x = g (f x) := rfl

/-- Construct a bundled `Top` from the underlying type and the typeclass. -/
def of (X : Type u) [topological_space X] : Top := ⟨X⟩

instance (X : Top) : topological_space X := X.str

@[simp] lemma coe_of (X : Type u) [topological_space X] : (of X : Type u) = X := rfl

instance : inhabited Top := ⟨Top.of empty⟩

/-- The discrete topology on any type. -/
def discrete : Type u ⥤ Top.{u} :=
{ obj := λ X, ⟨X, ⊥⟩,
  map := λ X Y f, { to_fun := f, continuous_to_fun := continuous_bot } }

instance {X : Type u} : discrete_topology (discrete.obj X) := ⟨rfl⟩

/-- The trivial topology on any type. -/
def trivial : Type u ⥤ Top.{u} :=
{ obj := λ X, ⟨X, ⊤⟩,
  map := λ X Y f, { to_fun := f, continuous_to_fun := continuous_top } }

/-- Any homeomorphisms induces an isomorphism in `Top`. -/
@[simps] def iso_of_homeo {X Y : Top.{u}} (f : X ≃ₜ Y) : X ≅ Y :=
{ hom := ⟨f⟩,
  inv := ⟨f.symm⟩ }

/-- Any isomorphism in `Top` induces a homeomorphism. -/
@[simps] def homeo_of_iso {X Y : Top.{u}} (f : X ≅ Y) : X ≃ₜ Y :=
{ to_fun := f.hom,
  inv_fun := f.inv,
  left_inv := λ x, by simp,
  right_inv := λ x, by simp,
  continuous_to_fun := f.hom.continuous,
  continuous_inv_fun := f.inv.continuous }

@[simp] lemma of_iso_of_homeo {X Y : Top.{u}} (f : X ≃ₜ Y) : homeo_of_iso (iso_of_homeo f) = f :=
by { ext, refl }

@[simp] lemma of_homeo_of_iso {X Y : Top.{u}} (f : X ≅ Y) : iso_of_homeo (homeo_of_iso f) = f :=
by { ext, refl }

@[simp]
lemma open_embedding_iff_comp_is_iso {X Y Z : Top} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso g] :
  open_embedding (f ≫ g) ↔ open_embedding f :=
(Top.homeo_of_iso (as_iso g)).open_embedding.of_comp_iff f

@[simp]
lemma open_embedding_iff_is_iso_comp {X Y Z : Top} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso f] :
  open_embedding (f ≫ g) ↔ open_embedding g :=
begin
  split,
  { intro h,
    convert h.comp (Top.homeo_of_iso (as_iso f).symm).open_embedding,
    exact congr_arg _ (is_iso.inv_hom_id_assoc f g).symm },
  { exact λ h, h.comp (Top.homeo_of_iso (as_iso f)).open_embedding }
end

end Top

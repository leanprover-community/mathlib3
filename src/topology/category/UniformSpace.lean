/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Patrick Massot, Scott Morrison
-/

import category_theory.concrete_category.unbundled_hom
import category_theory.full_subcategory
import category_theory.monad.limits
import topology.uniform_space.completion
import topology.category.Top.basic

/-!
# The category of uniform spaces

We construct the category of uniform spaces, show that the complete separated uniform spaces
form a reflective subcategory, and hence possess all limits that uniform spaces do.

TODO: show that uniform spaces actually have all limits!
-/

universes u

open category_theory

/-- A (bundled) uniform spaces. -/
def UniformSpace : Type (u+1) := bundled uniform_space

namespace UniformSpace
local attribute [reducible] UniformSpace

-- Setup instances while `UniformSpace` is reducible:
instance : unbundled_hom @uniform_continuous := ⟨@uniform_continuous_id, @uniform_continuous.comp⟩
instance : concrete_category UniformSpace.{u} := infer_instance
instance (X : UniformSpace) : uniform_space X := X.str
instance : has_coe_to_sort UniformSpace.{u} := infer_instance
instance (X Y : UniformSpace.{u}) : has_coe_to_fun (X ⟶ Y) := concrete_category.has_coe_to_fun

/-- Construct a bundled `UniformSpace` from the underlying type and the typeclass. -/
def of (α : Type u) [uniform_space α] : UniformSpace := ⟨α⟩

@[extensionality] lemma hom_ext {X Y : UniformSpace} {f g : X ⟶ Y} (h : ∀ x : X, f x = g x) : f = g :=
subtype.eq (funext h)

/-- The forgetful functor from uniform spaces to topological spaces. -/
instance has_forget_to_Top : has_forget₂ UniformSpace.{u} Top.{u} :=
unbundled_hom.mk_has_forget₂
  @uniform_space.to_topological_space
  @uniform_continuous.continuous

instance uniform_space_forget (X) : uniform_space ((forget₂ UniformSpace Top).obj X) := X.str

end UniformSpace

/-- A (bundled) complete separated uniform space. -/
structure CpltSepUniformSpace :=
(α : Type u)
[is_uniform_space : uniform_space α]
[is_complete_space : complete_space α]
[is_separated : separated α]

namespace CpltSepUniformSpace

attribute [instance] is_uniform_space is_complete_space is_separated

/-- Construct a bundled `UniformSpace` from the underlying type and the appropriate typeclasses. -/
def of (X : Type u) [uniform_space X] [complete_space X] [separated X] : CpltSepUniformSpace := ⟨X⟩

/-- The category instance on `CpltSepUniformSpace`. -/
instance concrete_category : concrete_category CpltSepUniformSpace :=
induced_category.concrete_category (λ X, UniformSpace.of X.α)

instance has_forget_to_UniformSpace : has_forget₂ CpltSepUniformSpace UniformSpace :=
induced_category.has_forget₂ (λ X, UniformSpace.of X.α)

instance : has_coe_to_sort CpltSepUniformSpace := concrete_category.has_coe_to_sort CpltSepUniformSpace

instance complete_space_forget (X) : complete_space ((forget₂ CpltSepUniformSpace UniformSpace).obj X) := X.is_complete_space
instance separated_forget (X) : separated ((forget₂ CpltSepUniformSpace UniformSpace).obj X) := X.is_separated

end CpltSepUniformSpace

namespace UniformSpace
local notation `U` := (forget₂ CpltSepUniformSpace UniformSpace).obj

open uniform_space
open CpltSepUniformSpace

/-- The functor turning uniform spaces into complete separated uniform spaces. -/
noncomputable def completion_functor : UniformSpace ⥤ CpltSepUniformSpace :=
{ obj := λ X, CpltSepUniformSpace.of (completion X),
  map := λ X Y f, ⟨completion.map f.1, completion.uniform_continuous_map⟩,
  map_comp' := λ X Y Z f g,
  begin
    apply subtype.eq,
    dsimp,
    rw ←completion.map_comp g.property f.property,
    refl,
  end }.

/-- The inclusion of any uniform spaces into its completion. -/
def completion_hom (X : UniformSpace) :
  X ⟶ U (completion_functor.obj X) :=
{ val := (coe : X → completion X),
  property := completion.uniform_continuous_coe X }

@[simp] lemma completion_hom_val (X : UniformSpace) (x) :
  (completion_hom X) x = (x : completion X) := rfl

/-- The mate of a morphism from a `UniformSpace` to a `CpltSepUniformSpace`. -/
noncomputable def extension_hom {X : UniformSpace} {Y : CpltSepUniformSpace}
  (f : X ⟶ U Y) :
  completion_functor.obj X ⟶ Y :=
{ val := completion.extension f,
  property := completion.uniform_continuous_extension }

@[simp] lemma extension_hom_val {X : UniformSpace} {Y : CpltSepUniformSpace}
  (f : X ⟶ U Y) (x) :
    (extension_hom f) x = completion.extension f x := rfl.

@[simp] lemma extension_comp_coe {X : UniformSpace} {Y : CpltSepUniformSpace}
  (f : U (CpltSepUniformSpace.of (completion X)) ⟶ U Y) :
    extension_hom (completion_hom X ≫ f) = f :=
by { apply subtype.eq, funext x, exact congr_fun (completion.extension_comp_coe f.property) x }

/-- The completion functor is left adjoint to the forgetful functor. -/
noncomputable def adj : completion_functor.{u} ⊣ forget₂ CpltSepUniformSpace UniformSpace :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f, completion_hom X ≫ f,
    inv_fun := λ f, extension_hom f,
    left_inv := λ f, by { dsimp, erw extension_comp_coe },
    right_inv := λ f, by { ext, exact completion.extension_coe f.property x, } },
  hom_equiv_naturality_left_symm' := λ X X' Y f g,
  begin
    ext, dsimp,
    erw [coe_comp, ←completion.extension_map g.property f.property],
    refl,
  end }

noncomputable instance : is_right_adjoint (forget₂ CpltSepUniformSpace UniformSpace) :=
⟨completion_functor, adj⟩
noncomputable instance : reflective (forget₂ CpltSepUniformSpace UniformSpace) := {}

open category_theory.limits

-- TODO Once someone defines `has_limits UniformSpace`, turn this into an instance.
noncomputable example [has_limits.{u} UniformSpace.{u}] : has_limits.{u} CpltSepUniformSpace.{u} :=
has_limits_of_reflective $ forget₂ CpltSepUniformSpace UniformSpace

end UniformSpace

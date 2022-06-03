/-
Copyright (c) 2019 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer, Markus Himmel
-/
import algebra.category.Group.basic
import category_theory.limits.shapes.kernels
import category_theory.linear
import category_theory.elementwise
import linear_algebra.basic
import category_theory.conj

/-!
# The category of `R`-modules

`Module.{v} R` is the category of bundled `R`-modules with carrier in the universe `v`. We show
that it is preadditive and show that being an isomorphism, monomorphism and epimorphism is
equivalent to being a linear equivalence, an injective linear map and a surjective linear map,
respectively.

## Implementation details

To construct an object in the category of `R`-modules from a type `M` with an instance of the
`module` typeclass, write `of R M`. There is a coercion in the other direction.

Similarly, there is a coercion from morphisms in `Module R` to linear maps.

Unfortunately, Lean is not smart enough to see that, given an object `M : Module R`, the expression
`of R M`, where we coerce `M` to the carrier type, is definitionally equal to `M` itself.
This means that to go the other direction, i.e., from linear maps/equivalences to (iso)morphisms
in the category of `R`-modules, we have to take care not to inadvertently end up with an
`of R M` where `M` is already an object. Hence, given `f : M →ₗ[R] N`,
* if `M N : Module R`, simply use `f`;
* if `M : Module R` and `N` is an unbundled `R`-module, use `↿f` or `as_hom_left f`;
* if `M` is an unbundled `R`-module and `N : Module R`, use `↾f` or `as_hom_right f`;
* if `M` and `N` are unbundled `R`-modules, use `↟f` or `as_hom f`.

Similarly, given `f : M ≃ₗ[R] N`, use `to_Module_iso`, `to_Module_iso'_left`, `to_Module_iso'_right`
or `to_Module_iso'`, respectively.

The arrow notations are localized, so you may have to `open_locale Module` to use them. Note that
the notation for `as_hom_left` clashes with the notation used to promote functions between types to
morphisms in the category `Type`, so to avoid confusion, it is probably a good idea to avoid having
the locales `Module` and `category_theory.Type` open at the same time.

If you get an error when trying to apply a theorem and the `convert` tactic produces goals of the
form `M = of R M`, then you probably used an incorrect variant of `as_hom` or `to_Module_iso`.

-/

open category_theory
open category_theory.limits
open category_theory.limits.walking_parallel_pair

universes v u

variables (R : Type u) [ring R]

/-- The category of R-modules and their morphisms.

 Note that in the case of `R = ℤ`, we can not
impose here that the `ℤ`-multiplication field from the module structure is defeq to the one coming
from the `is_add_comm_group` structure (contrary to what we do for all module structures in
mathlib), which creates some difficulties down the road. -/
structure Module :=
(carrier : Type v)
[is_add_comm_group : add_comm_group carrier]
[is_module : module R carrier]

attribute [instance] Module.is_add_comm_group Module.is_module

namespace Module

instance : has_coe_to_sort (Module.{v} R) (Type v) := ⟨Module.carrier⟩

instance Module_category : category (Module.{v} R) :=
{ hom   := λ M N, M →ₗ[R] N,
  id    := λ M, 1,
  comp  := λ A B C f g, g.comp f,
  id_comp' := λ X Y f, linear_map.id_comp _,
  comp_id' := λ X Y f, linear_map.comp_id _,
  assoc' := λ W X Y Z f g h, linear_map.comp_assoc _ _ _ }

instance Module_concrete_category : concrete_category.{v} (Module.{v} R) :=
{ forget := { obj := λ R, R, map := λ R S f, (f : R → S) },
  forget_faithful := { } }

instance has_forget_to_AddCommGroup : has_forget₂ (Module R) AddCommGroup :=
{ forget₂ :=
  { obj := λ M, AddCommGroup.of M,
    map := λ M₁ M₂ f, linear_map.to_add_monoid_hom f } }

instance (M N : Module R) : linear_map_class (M ⟶ N) R M N :=
{ coe := λ f, f,
  .. linear_map.semilinear_map_class }

/-- The object in the category of R-modules associated to an R-module -/
def of (X : Type v) [add_comm_group X] [module R X] : Module R := ⟨X⟩

@[simp] lemma forget₂_obj (X : Module R) :
  (forget₂ (Module R) AddCommGroup).obj X = AddCommGroup.of X :=
rfl

@[simp] lemma forget₂_obj_Module_of (X : Type v) [add_comm_group X] [module R X] :
  (forget₂ (Module R) AddCommGroup).obj (of R X) = AddCommGroup.of X :=
rfl

@[simp] lemma forget₂_map (X Y : Module R) (f : X ⟶ Y) :
  (forget₂ (Module R) AddCommGroup).map f = linear_map.to_add_monoid_hom f :=
rfl

/-- Typecheck a `linear_map` as a morphism in `Module R`. -/
def of_hom {R : Type u} [ring R] {X Y : Type v} [add_comm_group X] [module R X] [add_comm_group Y]
  [module R Y] (f : X →ₗ[R] Y) : of R X ⟶ of R Y := f

@[simp] lemma of_hom_apply {R : Type u} [ring R]
  {X Y : Type v} [add_comm_group X] [module R X] [add_comm_group Y] [module R Y] (f : X →ₗ[R] Y)
  (x : X) : of_hom f x = f x := rfl

instance : inhabited (Module R) := ⟨of R punit⟩

instance of_unique {X : Type v} [add_comm_group X] [module R X] [i : unique X] :
  unique (of R X) := i

@[simp]
lemma coe_of (X : Type v) [add_comm_group X] [module R X] : (of R X : Type v) = X := rfl

variables {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
module. -/
@[simps]
def of_self_iso (M : Module R) : Module.of R M ≅ M :=
{ hom := 𝟙 M, inv := 𝟙 M }

lemma is_zero_of_subsingleton (M : Module R) [subsingleton M] :
  is_zero M :=
begin
  refine ⟨λ X, ⟨⟨⟨0⟩, λ f, _⟩⟩, λ X, ⟨⟨⟨0⟩, λ f, _⟩⟩⟩,
  { ext, have : x = 0 := subsingleton.elim _ _, rw [this, map_zero, map_zero], },
  { ext, apply subsingleton.elim }
end

instance : has_zero_object (Module.{v} R) :=
⟨⟨of R punit, is_zero_of_subsingleton _⟩⟩

variables {R} {M N U : Module.{v} R}

@[simp] lemma id_apply (m : M) : (𝟙 M : M → M) m = m := rfl

@[simp] lemma coe_comp (f : M ⟶ N) (g : N ⟶ U) :
  ((f ≫ g) : M → U) = g ∘ f := rfl

lemma comp_def (f : M ⟶ N) (g : N ⟶ U) : f ≫ g = g.comp f := rfl

end Module

variables {R}
variables {X₁ X₂ : Type v}

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def Module.as_hom [add_comm_group X₁] [module R X₁] [add_comm_group X₂] [module R X₂] :
  (X₁ →ₗ[R] X₂) → (Module.of R X₁ ⟶ Module.of R X₂) := id

localized "notation `↟` f : 1024 := Module.as_hom f" in Module

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def Module.as_hom_right [add_comm_group X₁] [module R X₁] {X₂ : Module.{v} R} :
  (X₁ →ₗ[R] X₂) → (Module.of R X₁ ⟶ X₂) := id

localized "notation `↾` f : 1024 := Module.as_hom_right f" in Module

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def Module.as_hom_left {X₁ : Module.{v} R} [add_comm_group X₂] [module R X₂] :
  (X₁ →ₗ[R] X₂) → (X₁ ⟶ Module.of R X₂) := id

localized "notation `↿` f : 1024 := Module.as_hom_left f" in Module

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s. -/
@[simps]
def linear_equiv.to_Module_iso
  {g₁ : add_comm_group X₁} {g₂ : add_comm_group X₂} {m₁ : module R X₁} {m₂ : module R X₂}
  (e : X₁ ≃ₗ[R] X₂) :
  Module.of R X₁ ≅ Module.of R X₂ :=
{ hom := (e : X₁ →ₗ[R] X₂),
  inv := (e.symm : X₂ →ₗ[R] X₁),
  hom_inv_id' := begin ext, exact e.left_inv x, end,
  inv_hom_id' := begin ext, exact e.right_inv x, end, }

/--
Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s.

This version is better than `linear_equiv_to_Module_iso` when applicable, because Lean can't see
`Module.of R M` is defeq to `M` when `M : Module R`. -/
@[simps]
def linear_equiv.to_Module_iso' {M N : Module.{v} R} (i : M ≃ₗ[R] N) : M ≅ N :=
{ hom := i,
  inv := i.symm,
  hom_inv_id' := linear_map.ext $ λ x, by simp,
  inv_hom_id' := linear_map.ext $ λ x, by simp }

/--
Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s.

This version is better than `linear_equiv_to_Module_iso` when applicable, because Lean can't see
`Module.of R M` is defeq to `M` when `M : Module R`. -/
@[simps]
def linear_equiv.to_Module_iso'_left {X₁ : Module.{v} R} {g₂ : add_comm_group X₂} {m₂ : module R X₂}
  (e : X₁ ≃ₗ[R] X₂) : X₁ ≅ Module.of R X₂ :=
{ hom := (e : X₁ →ₗ[R] X₂),
  inv := (e.symm : X₂ →ₗ[R] X₁),
  hom_inv_id' := linear_map.ext $ λ x, by simp,
  inv_hom_id' := linear_map.ext $ λ x, by simp }

/--
Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s.

This version is better than `linear_equiv_to_Module_iso` when applicable, because Lean can't see
`Module.of R M` is defeq to `M` when `M : Module R`. -/
@[simps]
def linear_equiv.to_Module_iso'_right {g₁ : add_comm_group X₁} {m₁ : module R X₁}
  {X₂ : Module.{v} R} (e : X₁ ≃ₗ[R] X₂) : Module.of R X₁ ≅ X₂ :=
{ hom := (e : X₁ →ₗ[R] X₂),
  inv := (e.symm : X₂ →ₗ[R] X₁),
  hom_inv_id' := linear_map.ext $ λ x, by simp,
  inv_hom_id' := linear_map.ext $ λ x, by simp }

namespace category_theory.iso

/-- Build a `linear_equiv` from an isomorphism in the category `Module R`. -/
@[simps]
def to_linear_equiv {X Y : Module R} (i : X ≅ Y) : X ≃ₗ[R] Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  map_add'  := by tidy,
  map_smul' := by tidy, }.

end category_theory.iso

/-- linear equivalences between `module`s are the same as (isomorphic to) isomorphisms
in `Module` -/
@[simps]
def linear_equiv_iso_Module_iso {X Y : Type u} [add_comm_group X] [add_comm_group Y] [module R X]
  [module R Y] :
  (X ≃ₗ[R] Y) ≅ (Module.of R X ≅ Module.of R Y) :=
{ hom := λ e, e.to_Module_iso,
  inv := λ i, i.to_linear_equiv, }

namespace Module

instance : preadditive (Module.{v} R) :=
{ add_comp' := λ P Q R f f' g,
    show (f + f') ≫ g = f ≫ g + f' ≫ g, by { ext, simp },
  comp_add' := λ P Q R f g g',
    show f ≫ (g + g') = f ≫ g + f ≫ g', by { ext, simp } }

section
variables {S : Type u} [comm_ring S]

instance : linear S (Module.{v} S) :=
{ hom_module := λ X Y, linear_map.module,
  smul_comp' := by { intros, ext, simp },
  comp_smul' := by { intros, ext, simp }, }

variables {X Y X' Y' : Module.{v} S}

lemma iso.hom_congr_eq_arrow_congr (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y) :
  iso.hom_congr i j f = linear_equiv.arrow_congr i.to_linear_equiv j.to_linear_equiv f := rfl

lemma iso.conj_eq_conj (i : X ≅ X') (f : End X) :
  iso.conj i f = linear_equiv.conj i.to_linear_equiv f := rfl

end

end Module

instance (M : Type u) [add_comm_group M] [module R M] : has_coe (submodule R M) (Module R) :=
⟨ λ N, Module.of R N ⟩

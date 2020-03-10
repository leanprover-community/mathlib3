/-
Copyright (c) 2019 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer, Markus Himmel
-/
import algebra.module
import algebra.punit_instances
import category_theory.concrete_category
import category_theory.limits.shapes.zero
import category_theory.limits.shapes.kernels
import linear_algebra.basic
open category_theory
open category_theory.limits
open category_theory.limits.walking_parallel_pair

universe u

variables (R : Type u) [ring R]

/-- The category of R-modules and their morphisms. -/
structure Module :=
(carrier : Type u)
[is_add_comm_group : add_comm_group carrier]
[is_module : module R carrier]

attribute [instance] Module.is_add_comm_group Module.is_module

namespace Module

-- TODO revisit this after #1438 merges, to check coercions and instances are handled consistently
instance : has_coe_to_sort (Module R) :=
{ S := Type u, coe := Module.carrier }

instance : concrete_category (Module.{u} R) :=
{ to_category :=
  { hom   := λ M N, M →ₗ[R] N,
    id    := λ M, 1,
    comp  := λ A B C f g, g.comp f },
  forget := { obj := λ R, R, map := λ R S f, (f : R → S) },
  forget_faithful := { } }

/-- The object in the category of R-modules associated to an R-module -/
def of (X : Type u) [add_comm_group X] [module R X] : Module R := ⟨R, X⟩

instance : inhabited (Module R) := ⟨of R punit⟩

lemma of_apply (X : Type u) [add_comm_group X] [module R X] : (of R X : Type u) = X := rfl

variables {R}

@[simps]
def of_self_iso (M : Module R) : Module.of R M ≅ M :=
{ hom := 𝟙 M, inv := 𝟙 M }

instance : subsingleton (of R punit) :=
by { rw of_apply R punit, apply_instance }

instance : has_zero_object.{u} (Module R) :=
{ zero := of R punit,
  unique_to := λ X,
  { default := (0 : punit →ₗ[R] X),
    uniq := λ _, linear_map.ext $ λ x,
      have h : x = 0, from subsingleton.elim _ _,
      by simp [h] },
  unique_from := λ X,
  { default := (0 : X →ₗ[R] punit),
    uniq := λ _, linear_map.ext $ λ x, subsingleton.elim _ _ } }

variables (M N U : Module R)

@[simp] lemma id_apply (m : M) : (𝟙 M : M → M) m = m := rfl

@[simp] lemma coe_comp (f : M ⟶ N) (g : N ⟶ U) :
  ((f ≫ g) : M → U) = g ∘ f := rfl

instance hom_is_module_hom {M₁ M₂ : Module R} (f : M₁ ⟶ M₂) :
  is_linear_map R (f : M₁ → M₂) := linear_map.is_linear _


-- TODO do this like in Group/basic.lean
@[simps]
def iso_of_linear_equiv
  {X₁ : Type u} {g₁ : add_comm_group X₁} {m₁ : module R X₁}
  {X₂ : Type u} {g₂ : add_comm_group X₂} {m₁ : module R X₂}
  (e : X₁ ≃ₗ[R] X₂) : Module.of R X₁ ≅ Module.of R X₂ :=
{ hom := (e : X₁ →ₗ[R] X₂),
  inv := (e.symm : X₂ →ₗ[R] X₁),
  hom_inv_id' := begin ext, exact e.left_inv x, end,
  inv_hom_id' := begin ext, exact e.right_inv x, end, }

section kernel
variable (f : M ⟶ N)

local attribute [instance] has_zero_object.zero_morphisms_of_zero_object

/-- The cone on the equalizer diagram of f and 0 induced by the kernel of f -/
def kernel_cone : cone (parallel_pair f 0) :=
{ X := of R f.ker,
  π :=
  { app := λ j,
    match j with
    | zero := f.ker.subtype
    | one := 0
    end,
    naturality' := λ j j' g, by { cases j; cases j'; cases g; tidy } } }

/-- The kernel of a linear map is a kernel in the categorical sense -/
def kernel_is_limit : is_limit (kernel_cone _ _ f) :=
{ lift := λ s, linear_map.cod_restrict f.ker (fork.ι s) (λ c, linear_map.mem_ker.2 $
  by { erw [←@function.comp_apply _ _ _ f (fork.ι s) c, ←coe_comp, fork.condition,
    has_zero_morphisms.comp_zero _ (fork.ι s) N], refl }),
  fac' := λ s j, linear_map.ext $ λ x,
  begin
    rw [coe_comp, function.comp_app, ←linear_map.comp_apply],
    cases j,
    { erw @linear_map.subtype_comp_cod_restrict _ _ _ _ _ _ _ _ (fork.ι s) f.ker _, refl },
    { rw [←cone_parallel_pair_right, ←cone_parallel_pair_right], refl }
  end,
  uniq' := λ s m h, linear_map.ext $ λ x, subtype.ext.2 $
    have h₁ : (m ≫ (kernel_cone _ _ f).π.app zero).to_fun = (s.π.app zero).to_fun,
    by { congr, exact h zero },
    by convert @congr_fun _ _ _ _ h₁ x }

end kernel

local attribute [instance] has_zero_object.zero_morphisms_of_zero_object

instance : has_kernels.{u} (Module R) :=
⟨λ _ _ f, ⟨kernel_cone _ _ f, kernel_is_limit _ _ f⟩⟩

end Module

instance (M : Type u) [add_comm_group M] [module R M] : has_coe (submodule R M) (Module R) :=
⟨ λ N, Module.of R N ⟩

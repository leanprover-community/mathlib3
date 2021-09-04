/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.category.Module.epi_mono

/-!
# The concrete (co)kernels in the category of modules are (co)kernels in the categorical sense.
-/

open category_theory
open category_theory.limits
open category_theory.limits.walking_parallel_pair

universes u v

namespace Module
variables {R : Type u} [ring R]

section
variables {M N : Module.{v} R} (f : M ⟶ N)

/-- The kernel cone induced by the concrete kernel. -/
def kernel_cone : kernel_fork f :=
kernel_fork.of_ι (as_hom f.ker.subtype) $ by tidy

/-- The kernel of a linear map is a kernel in the categorical sense. -/
def kernel_is_limit : is_limit (kernel_cone f) :=
fork.is_limit.mk _
  (λ s, linear_map.cod_restrict f.ker (fork.ι s) (λ c, linear_map.mem_ker.2 $
    by { rw [←@function.comp_apply _ _ _ f (fork.ι s) c, ←coe_comp, fork.condition,
      has_zero_morphisms.comp_zero (fork.ι s) N], refl }))
  (λ s, linear_map.subtype_comp_cod_restrict _ _ _)
  (λ s m h, linear_map.ext $ λ x, subtype.ext_iff_val.2 $
    have h₁ : (m ≫ (kernel_cone f).π.app zero).to_fun = (s.π.app zero).to_fun,
      by { congr, exact h zero },
    by convert @congr_fun _ _ _ _ h₁ x )

/-- The cokernel cocone induced by the projection onto the quotient. -/
def cokernel_cocone : cokernel_cofork f :=
cokernel_cofork.of_π (as_hom f.range.mkq) $ linear_map.range_mkq_comp _

/-- The projection onto the quotient is a cokernel in the categorical sense. -/
def cokernel_is_colimit : is_colimit (cokernel_cocone f) :=
cofork.is_colimit.mk _
  (λ s, f.range.liftq (cofork.π s) $ linear_map.range_le_ker_iff.2 $ cokernel_cofork.condition s)
  (λ s, f.range.liftq_mkq (cofork.π s) _)
  (λ s m h,
  begin
    haveI : epi (as_hom f.range.mkq) := (epi_iff_range_eq_top _).mpr (submodule.range_mkq _),
    apply (cancel_epi (as_hom f.range.mkq)).1,
    convert h walking_parallel_pair.one,
    exact submodule.liftq_mkq _ _ _
  end)
end

/-- The category of R-modules has kernels, given by the inclusion of the kernel submodule. -/
lemma has_kernels_Module : has_kernels (Module R) :=
⟨λ X Y f, has_limit.mk ⟨_, kernel_is_limit f⟩⟩

/-- The category or R-modules has cokernels, given by the projection onto the quotient. -/
lemma has_cokernels_Module : has_cokernels (Module R) :=
⟨λ X Y f, has_colimit.mk ⟨_, cokernel_is_colimit f⟩⟩

open_locale Module

local attribute [instance] has_kernels_Module
local attribute [instance] has_cokernels_Module

variables {G H : Module.{v} R} (f : G ⟶ H)

/--
The categorical kernel of a morphism in `Module`
agrees with the usual module-theoretical kernel.
-/
noncomputable def kernel_iso_ker {G H : Module.{v} R} (f : G ⟶ H) :
  kernel f ≅ Module.of R (f.ker) :=
limit.iso_limit_cone ⟨_, kernel_is_limit f⟩

-- We now show this isomorphism commutes with the inclusion of the kernel into the source.

@[simp, elementwise] lemma kernel_iso_ker_inv_kernel_ι :
  (kernel_iso_ker f).inv ≫ kernel.ι f = f.ker.subtype :=
limit.iso_limit_cone_inv_π _ _

@[simp, elementwise] lemma kernel_iso_ker_hom_ker_subtype :
  (kernel_iso_ker f).hom ≫ f.ker.subtype = kernel.ι f :=
is_limit.cone_point_unique_up_to_iso_inv_comp _ (limit.is_limit _) zero

/--
The categorical cokernel of a morphism in `Module`
agrees with the usual module-theoretical quotient.
-/
noncomputable def cokernel_iso_range_quotient {G H : Module.{v} R} (f : G ⟶ H) :
  cokernel f ≅ Module.of R (f.range.quotient) :=
colimit.iso_colimit_cocone ⟨_, cokernel_is_colimit f⟩

-- We now show this isomorphism commutes with the projection of target to the cokernel.

@[simp, elementwise] lemma cokernel_π_cokernel_iso_range_quotient_hom :
  cokernel.π f ≫ (cokernel_iso_range_quotient f).hom = f.range.mkq :=
by { convert colimit.iso_colimit_cocone_ι_hom _ _; refl, }

@[simp, elementwise] lemma range_mkq_cokernel_iso_range_quotient_inv :
  ↿f.range.mkq ≫ (cokernel_iso_range_quotient f).inv = cokernel.π f :=
by { convert colimit.iso_colimit_cocone_ι_inv ⟨_, cokernel_is_colimit f⟩ _; refl, }

end Module

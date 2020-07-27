/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.category.Module.basic

/-!
# The concrete (co)kernels in the category of modules are (co)kernels in the categorical sense.
-/

open category_theory
open category_theory.limits
open category_theory.limits.walking_parallel_pair

universe u

namespace Module
variables {R : Type u} [ring R]

section
variables {M N : Module R} (f : M ⟶ N)

/-- The kernel cone induced by the concrete kernel. -/
def kernel_cone : kernel_fork f :=
kernel_fork.of_ι (as_hom f.ker.subtype) $ by tidy

/-- The kernel of a linear map is a kernel in the categorical sense. -/
def kernel_is_limit : is_limit (kernel_cone f) :=
{ lift := λ s, linear_map.cod_restrict f.ker (fork.ι s) (λ c, linear_map.mem_ker.2 $
  by { rw [←@function.comp_apply _ _ _ f (fork.ι s) c, ←coe_comp, fork.condition,
    has_zero_morphisms.comp_zero (fork.ι s) N], refl }),
  fac' := λ s j, linear_map.ext $ λ x,
  begin
    rw [coe_comp, function.comp_app, ←linear_map.comp_apply],
    cases j,
    { erw @linear_map.subtype_comp_cod_restrict _ _ _ _ _ _ _ _ (fork.ι s) f.ker _ },
    { rw [←fork.app_zero_left, ←fork.app_zero_left], refl }
  end,
  uniq' := λ s m h, linear_map.ext $ λ x, subtype.ext_iff_val.2 $
    have h₁ : (m ≫ (kernel_cone f).π.app zero).to_fun = (s.π.app zero).to_fun,
    by { congr, exact h zero },
    by convert @congr_fun _ _ _ _ h₁ x }

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
    haveI : epi (as_hom f.range.mkq) := epi_of_range_eq_top _ (submodule.range_mkq _),
    apply (cancel_epi (as_hom f.range.mkq)).1,
    convert h walking_parallel_pair.one,
    exact submodule.liftq_mkq _ _ _
  end)
end

instance : has_kernels (Module R) :=
⟨λ X Y f, ⟨_, kernel_is_limit f⟩⟩

instance : has_cokernels (Module R) :=
⟨λ X Y f, ⟨_, cokernel_is_colimit f⟩⟩

end Module

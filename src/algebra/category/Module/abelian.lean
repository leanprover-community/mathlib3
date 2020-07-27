/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.category.Module.kernels
import algebra.category.Module.limits
import category_theory.abelian.basic

/-!
# The category of left R-modules is abelian.
-/

open category_theory
open category_theory.limits

noncomputable theory

universe u

namespace Module
variables {R : Type u} [ring R] {M N : Module R} (f : M ⟶ N)

/-- In the category of modules, every monomorphism is normal. -/
def normal_mono [mono f] : normal_mono f :=
{ Z := of R f.range.quotient,
  g := f.range.mkq,
  w := linear_map.range_mkq_comp _,
  is_limit :=
  begin
    refine is_kernel.iso_kernel _ _ (kernel_is_limit _) _ _,
    { exact linear_equiv.to_Module_iso' (linear_map.equiv_range_mkq_ker_of_ker_eq_bot (ker_eq_bot_of_mono f)), },
    ext, refl
  end }

/-- In the category of modules, every epimorphism is normal. -/
def normal_epi [epi f] : normal_epi f :=
{ W := of R f.ker,
  g := f.ker.subtype,
  w := linear_map.comp_ker_subtype _,
  is_colimit :=
  begin
    refine is_cokernel.cokernel_iso _ _ (cokernel_is_colimit _) _ _,
    { exact linear_equiv.to_Module_iso' (linear_map.ker_subtype_range_quotient_equiv_of_range_eq_top (range_eq_top_of_epi f)) },
    ext, refl
  end }

/-- The category of R-modules is abelian. -/
instance : abelian (Module R) :=
{ has_finite_products := by apply_instance,
  has_kernels := by apply_instance,
  has_cokernels := by apply_instance,
  normal_mono := λ X Y f m, by exactI normal_mono f,
  normal_epi := λ X Y f e, by exactI normal_epi f }

end Module

/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

-/

import ring_theory.mv_polynomial.homogeneous
import ring_theory.graded_algebra.basic

/-! # Grading

This file contains an instance of `mv_polynomial R σ` as a `ℕ`-graded algebra.

## Tags

graded algebra, polynomial
-/

namespace mv_polynomial


open mv_polynomial direct_sum
open_locale direct_sum big_operators

variables (R : Type*) [comm_ring R] (σ : Type*)

/--
For a multivariable polynomial `p`, we can decompose `p` as a direct sum of monomials
-/
noncomputable def decompose (p : mv_polynomial σ R) :
  ⨁ i, (homogeneous_submodule σ R i) :=
∑ i in finset.range (p.total_degree + 1), of (λ i, (homogeneous_submodule σ R i)) i
  ⟨(homogeneous_component i p), homogeneous_component_is_homogeneous i _⟩

lemma homogeneous_component_of_direct_sum
  (i : ℕ) (x : ⨁ i, homogeneous_submodule σ R i) :
homogeneous_component i (direct_sum.coe_add_monoid_hom _ x) = x i :=
begin
  classical,
  rw [←sum_support_of _ x, add_monoid_hom.map_sum, linear_map.map_sum],
  simp_rw [direct_sum.coe_add_monoid_hom_of],
  simp only [add_subgroup.coe_subtype, submodule.coe_sum, dfinsupp.finset_sum_apply],
  apply finset.sum_congr rfl,
  intros j hj,
  rw [← subtype.val_eq_coe, homogeneous_component_homogeneous_polynomial i j _
    (by simp only [mem_homogeneous_submodule]; convert (x j).2)],
  split_ifs,
  { rw [h, of_eq_same], refl, },
  { rw of_eq_of_ne _ _ _ _ (ne.symm h), refl },
end

lemma left_inv (x) :
  (decompose R σ) (direct_sum.coe_add_monoid_hom (λ (i : ℕ), homogeneous_submodule σ R i) x) = x :=
begin
  classical,
  rw decompose,
  simp_rw [homogeneous_component_of_direct_sum],
  conv_rhs { rw ←direct_sum.sum_support_of _ x },
  rw [show finset.range ((direct_sum.coe_add_monoid_hom _ x).total_degree + 1) = x.support ∪
      ((finset.range ((direct_sum.coe_add_monoid_hom _ x).total_degree + 1)) \ x.support), begin
      rw finset.union_sdiff_of_subset (λ a ha, _),
      simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_range] at ha ⊢,
      contrapose! ha,
      have := homogeneous_component_eq_zero _ _ ha,
      rw [homogeneous_component_of_direct_sum, ← subtype.val_eq_coe] at this,
      rw [subtype.ext_iff_val, this, subtype.val_eq_coe, submodule.coe_zero],
    end, finset.sum_union, show ∑ (j : ℕ) in finset.range
      (((direct_sum.coe_add_monoid_hom _) x).total_degree + 1) \
      dfinsupp.support x,
      (of (λ (i : ℕ), ↥(homogeneous_submodule σ R i)) j) ⟨(x j), _⟩ = 0, from _, add_zero,
    finset.sum_congr rfl (λ i hi, _)],
  { simp only [set_like.eta], },
  { rw ←finset.sum_const_zero,
    apply finset.sum_congr rfl (λ i hi, _),
    simp only [set_like.eta, not_not, finset.mem_sdiff, ne.def, dfinsupp.mem_support_to_fun,
      finset.mem_range] at hi ⊢,
    rw [hi.2, map_zero], },
  { exact disjoint_sdiff_self_right },
end

lemma right_inv (x) : direct_sum.coe_add_monoid_hom _ (decompose R σ x) = x :=
begin
  rw [decompose, add_monoid_hom.map_sum],
  conv_rhs { rw ← sum_homogeneous_component x },
  apply finset.sum_congr rfl (λ _ _, _),
  rw [direct_sum.coe_add_monoid_hom_of, ← subtype.val_eq_coe],
end

noncomputable instance graded_algebra :
  graded_algebra (λ i : ℕ, (homogeneous_submodule σ R i)) :=
{ one_mem := is_homogeneous_one σ R,
  mul_mem := λ i j x y hx hy, is_homogeneous.mul hx hy,
  decompose' := decompose R σ,
  left_inv := λ x, by apply right_inv,
  right_inv := λ x, by apply left_inv }

end mv_polynomial

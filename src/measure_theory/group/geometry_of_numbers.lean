/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import analysis.convex.measure
import measure_theory.group.fundamental_domain
import measure_theory.measure.haar_lebesgue

/-!
# Geometry of numbers

In this file we prove some of the fundamental theorems in the geometry of numbers, as studied by
Hermann Minkowski.

## Main results

* `exists_pair_mem_lattice_not_disjoint_vadd`: Blichfeldt's principle, existence of two distinct
  points in a subgroup such that the translates of a set by these two points are not disjoint when
  the covolume of the subgroup is larger than the volume of the
* `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`: Minkowski's theorem, existence of
  a non-zero lattice point inside a convex symmetric domain of large enough volume.

## TODO

* Calculate the volume of the fundamental domain of a finite index subgroup
* Voronoi diagrams
* See [Pete L. Clark, *Abstract Geometry of Numbers: Linear Forms* (arXiv)](https://arxiv.org/abs/1405.2119)
  for some more ideas.

## References

* [Pete L. Clark, *Geometry of Numbers with Applications to Number Theory*][clark_gon] p.28
-/

namespace measure_theory

open ennreal finite_dimensional measure_theory measure_theory.measure set
open_locale pointwise

variables {E L : Type*} [measurable_space E] {μ : measure E} {F s : set E}

/-- **Blichfeldt's Theorem**. If the volume of the set `s` is larger than the covolume of the
countable subgroup `L` of `E`, then there exists two distincts points `x, y ∈ L` such that `(x + s)`
and `(y + s)` are not disjoint. -/
lemma exists_pair_mem_lattice_not_disjoint_vadd [add_comm_group L] [countable L]
  [add_action L E] [measurable_space L] [has_measurable_vadd L E] [vadd_invariant_measure L E μ]
  (fund : is_add_fundamental_domain L F μ) (hS : null_measurable_set s μ) (h : μ F < μ s) :
  ∃ x y : L, x ≠ y ∧ ¬ disjoint (x +ᵥ s) (y +ᵥ s) :=
begin
  contrapose! h,
  exact ((fund.measure_eq_tsum _).trans (measure_Union₀ (pairwise.mono h $ λ i j hij,
    (hij.mono inf_le_left inf_le_left).ae_disjoint) $ λ _,
    (hS.vadd _).inter fund.null_measurable_set).symm).trans_le
    (measure_mono $ Union_subset $ λ _, inter_subset_right _ _),
end

/-- The **Minkowksi Convex Body Theorem**. If `s` is a convex symmetric domain of `E` whose volume
is large enough compared to the covolume of a lattice `L` of `E`, then it contains a non-zero
lattice point of `L`.  -/
lemma exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure [normed_add_comm_group E]
  [normed_space ℝ E] [borel_space E] [finite_dimensional ℝ E] [is_add_haar_measure μ]
  {L : add_subgroup E} [countable L] (fund : is_add_fundamental_domain L F μ)
  (h : μ F * 2 ^ finrank ℝ E < μ s) (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : convex ℝ s) :
  ∃ x ≠ 0, ((x : L) : E) ∈ s :=
begin
  have h_vol : μ F < μ ((2⁻¹ : ℝ) • s),
  { rwa [add_haar_smul_of_nonneg μ (by norm_num : 0 ≤ (2 : ℝ)⁻¹) s, ←mul_lt_mul_right
      (pow_ne_zero (finrank ℝ E) (two_ne_zero' _)) (pow_ne_top two_ne_top), mul_right_comm,
      of_real_pow (by norm_num : 0 ≤ (2 : ℝ)⁻¹), ←of_real_inv_of_pos zero_lt_two, of_real_bit0,
      of_real_one, ←mul_pow, ennreal.inv_mul_cancel two_ne_zero two_ne_top, one_pow, one_mul] },
  obtain ⟨x, y, hxy, h⟩ := exists_pair_mem_lattice_not_disjoint_vadd fund
    ((h_conv.smul _).null_measurable_set _) h_vol,
  obtain ⟨_, ⟨v, hv, rfl⟩, w, hw, hvw⟩ := not_disjoint_iff.mp h,
  refine ⟨x - y, sub_ne_zero.2 hxy, _⟩,
  rw mem_inv_smul_set_iff₀ (two_ne_zero' ℝ) at hv hw,
  simp_rw [add_subgroup.vadd_def, vadd_eq_add, add_comm _ w, ←sub_eq_sub_iff_add_eq_add,
    ←add_subgroup.coe_sub] at hvw,
  rw [←hvw, ←inv_smul_smul₀ (two_ne_zero' ℝ) (_ - _), smul_sub, sub_eq_add_neg, smul_add],
  refine h_conv hw (h_symm _ hv) _ _ _; norm_num,
end

end measure_theory

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

- `exists_pair_mem_lattice_not_disjoint_vadd_of_volume_lt_volume`: Blichfeldt's principle, existence
  of two distinct points in a subgroup such that the translates of a set by these two points are
  not disjoint when the covolume of the subgroup is larger than the volume of the set.
- `exists_nonzero_mem_lattice_of_volume_mul_two_pow_card_lt_measure`: Minkowski's theorem, existence
  of a non-zero lattice point inside a convex symmetric domain of large enough volume.

## TODO

* A finite index subgroup has given fundamental domain and covolume
* Some existence result in a metric space
* Voronoi

See https://arxiv.org/pdf/1405.2119.pdf for some more ideas.
-/

namespace measure_theory

open ennreal finite_dimensional measure_theory measure_theory.measure
open_locale pointwise

/-- Blichfeldt's theorem. If the volume of the `S` is larger than the covolume of the subgroup `L`
of `E`, then there exists two distincts points `x, y ∈ L` such that `(x + S)` and `(y + S)` are
not disjoint. -/
lemma exists_pair_mem_lattice_not_disjoint_vadd_of_volume_lt_volume
  {E : Type*} [add_comm_group E] [measurable_space E]
  {L : add_subgroup E} [countable L] [has_measurable_vadd L E]
  (μ : measure E) [vadd_invariant_measure L E μ] {F S : set E}
  (fund : is_add_fundamental_domain L F μ) (hS : null_measurable_set S μ) (h : μ F < μ S) :
  ∃ x y : L, x ≠ y ∧ ¬ disjoint (x +ᵥ S) (y +ᵥ S) :=
begin
  contrapose! h,
  rw ( _ : μ S = μ (⋃ (x : L), -x +ᵥ (S ∩ (x +ᵥ F)))),
  { refine measure_mono (set.Union_subset_iff.mpr _),
    rintros x _ ⟨_, ⟨_, v, hv, rfl⟩, rfl⟩,
    simp only [hv, neg_vadd_vadd], },
  { rw measure_Union₀,
    { simp_rw measure_vadd,
      exact is_add_fundamental_domain.measure_eq_tsum' fund S, },
    { intros x y hxy,
      refine disjoint.ae_disjoint _,
      have hx : -x +ᵥ S ∩ (x +ᵥ F) ≤ -x +ᵥ S :=
        @set.vadd_set_mono _ _ _ _ _ _ (set.inter_subset_left _ _),
      have hy : -y +ᵥ S ∩ (y +ᵥ F) ≤ -y +ᵥ S :=
        @set.vadd_set_mono _ _ _ _ _ _ (set.inter_subset_left _ _),
      exact disjoint.mono hx hy (h _ _ (neg_injective.ne hxy)), },
    { exact λ _, (hS.inter (fund.1.vadd _)).vadd _, }}
end

/-- Minkowksi's theorem. If `T` is a convex symmetric domain of `E` whose volume is large enough
compared to the covolume of the lattice `L` of `E`, then it contains a non-zero lattice point.  -/
lemma exists_ne_zero_mem_lattice_of_measure_mul_two_pow_finrank_lt_measure
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ] {L : add_subgroup E}
  [countable L] {F T : set E} (fund : is_add_fundamental_domain L F μ)
  (h : μ F * 2 ^ finrank ℝ E < μ T) (h_symm : ∀ x ∈ T, -x ∈ T) (h_conv : convex ℝ T) :
  ∃ x ≠ 0, ((x : L) : E) ∈ T :=
begin
  have h_vol : μ F < μ ((2⁻¹ : ℝ) • T),
  { rwa [add_haar_smul_of_nonneg μ (by norm_num : 0 ≤ (2 : ℝ)⁻¹) T, ← mul_lt_mul_right
      (pow_ne_zero (finrank ℝ E) (two_ne_zero' _)) (pow_ne_top two_ne_top), mul_right_comm,
      of_real_pow (by norm_num : 0 ≤ (2 : ℝ)⁻¹), ← of_real_inv_of_pos zero_lt_two, of_real_bit0,
      of_real_one, ← mul_pow, ennreal.inv_mul_cancel two_ne_zero two_ne_top, one_pow, one_mul], },
  obtain ⟨x, y, hxy, h⟩ := exists_pair_mem_lattice_not_disjoint_vadd_of_volume_lt_volume μ fund
    (null_measurable_set.const_smul_of_ne_zero (convex.null_measurable_set μ h_conv) (by norm_num))
    h_vol,
  obtain ⟨_, ⟨v, hvS, rfl⟩, w, hwS, hvw⟩ := set.not_disjoint_iff.mp h,
  refine ⟨x - y, sub_ne_zero.mpr hxy, _⟩,
  rw (_ : ((x - y : L) : E) = (2⁻¹ : ℝ) • ((2 : ℝ) • w : E) + (2⁻¹ : ℝ) • ((2 : ℝ) • -v : E)),
  { refine convex_iff_forall_pos.mp h_conv _ _ (by positivity) (by positivity) (by norm_num),
    exact (set.mem_inv_smul_set_iff₀ (ne_zero.ne (2 : ℝ)) T _).mp hwS,
    rw smul_neg,
    exact h_symm _ ((set.mem_inv_smul_set_iff₀ (ne_zero.ne (2 : ℝ)) T _).mp hvS), },
  { rw [add_subgroup.vadd_def, vadd_eq_add, add_comm] at hvw,
    simpa only [inv_smul_smul₀, ne.def, bit0_eq_zero, one_ne_zero, not_false_iff, ←sub_eq_add_neg]
      using (sub_eq_sub_iff_add_eq_add.mpr hvw).symm },
end

end measure_theory

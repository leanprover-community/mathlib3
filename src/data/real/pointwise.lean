/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Wieser
-/
import algebra.order.module
import algebra.pointwise
import data.real.basic

/-!
# Pointwise operations on sets of reals

This file relates `Inf (a • s)`/`Sup (a • s)` with `a • Inf s`/`a • Sup s` for `s : set ℝ`.

From these, it relates `⨅ i, a • f i` / `⨆ i, a • f i` with `a • (⨅ i, f i)` / `a • (⨆ i, f i)`,
and provides lemmas about distributing `*` over `⨅` and `⨆`.

# TODO

This is true more generally for conditionally complete linear order whose default value is `0`. We
don't have those yet.
-/

open set
open_locale pointwise

variables {ι : Sort*} {α : Type*} [linear_ordered_field α]

section mul_action_with_zero
variables [mul_action_with_zero α ℝ] [ordered_smul α ℝ] {a : α}

lemma real.Inf_smul_of_nonneg (ha : 0 ≤ a) (s : set ℝ) : Inf (a • s) = a • Inf s :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { rw [smul_set_empty, real.Inf_empty, smul_zero'] },
  obtain rfl | ha' := ha.eq_or_lt,
  { rw [zero_smul_set hs, zero_smul],
    exact cInf_singleton 0 },
  by_cases bdd_below s,
  { exact ((order_iso.smul_left ℝ ha').map_cInf' hs h).symm },
  { rw [real.Inf_of_not_bdd_below (mt (bdd_below_smul_iff_of_pos ha').1 h),
      real.Inf_of_not_bdd_below h, smul_zero'] }
end

lemma real.smul_infi_of_nonneg (ha : 0 ≤ a) (f : ι → ℝ) :
  a • (⨅ i, f i) = ⨅ i, a • f i :=
(real.Inf_smul_of_nonneg ha _).symm.trans $ congr_arg Inf $ (range_comp _ _).symm

lemma real.Sup_smul_of_nonneg (ha : 0 ≤ a) (s : set ℝ) : Sup (a • s) = a • Sup s :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { rw [smul_set_empty, real.Sup_empty, smul_zero'] },
  obtain rfl | ha' := ha.eq_or_lt,
  { rw [zero_smul_set hs, zero_smul],
    exact cSup_singleton 0 },
  by_cases bdd_above s,
  { exact ((order_iso.smul_left ℝ ha').map_cSup' hs h).symm },
  { rw [real.Sup_of_not_bdd_above (mt (bdd_above_smul_iff_of_pos ha').1 h),
      real.Sup_of_not_bdd_above h, smul_zero'] }
end

lemma real.smul_supr_of_nonneg (ha : 0 ≤ a) (f : ι → ℝ) :
  a • (⨆ i, f i) = ⨆ i, a • f i :=
(real.Sup_smul_of_nonneg ha _).symm.trans $ congr_arg Sup $ (range_comp _ _).symm

end mul_action_with_zero

section module
variables [module α ℝ] [ordered_smul α ℝ] {a : α}

lemma real.Inf_smul_of_nonpos (ha : a ≤ 0) (s : set ℝ) : Inf (a • s) = a • Sup s :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { rw [smul_set_empty, real.Inf_empty, real.Sup_empty, smul_zero'] },
  obtain rfl | ha' := ha.eq_or_lt,
  { rw [zero_smul_set hs, zero_smul],
    exact cInf_singleton 0 },
  by_cases bdd_above s,
  { exact ((order_iso.smul_left_dual ℝ ha').map_cSup' hs h).symm },
  { rw [real.Inf_of_not_bdd_below (mt (bdd_below_smul_iff_of_neg ha').1 h),
      real.Sup_of_not_bdd_above h, smul_zero'] }
end

lemma real.smul_supr_of_nonpos (ha : a ≤ 0) (f : ι → ℝ) :
  a • (⨆ i, f i) = ⨅ i, a • f i :=
(real.Inf_smul_of_nonpos ha _).symm.trans $ congr_arg Inf $ (range_comp _ _).symm

lemma real.Sup_smul_of_nonpos (ha : a ≤ 0) (s : set ℝ) : Sup (a • s) = a • Inf s :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { rw [smul_set_empty, real.Sup_empty, real.Inf_empty, smul_zero] },
  obtain rfl | ha' := ha.eq_or_lt,
  { rw [zero_smul_set hs, zero_smul],
    exact cSup_singleton 0 },
  by_cases bdd_below s,
  { exact ((order_iso.smul_left_dual ℝ ha').map_cInf' hs h).symm },
  { rw [real.Sup_of_not_bdd_above (mt (bdd_above_smul_iff_of_neg ha').1 h),
      real.Inf_of_not_bdd_below h, smul_zero] }
end

lemma real.smul_infi_of_nonpos (ha : a ≤ 0) (f : ι → ℝ) :
  a • (⨅ i, f i) = ⨆ i, a • f i :=
(real.Sup_smul_of_nonpos ha _).symm.trans $ congr_arg Sup $ (range_comp _ _).symm

end module

/-! ## Special cases for real multiplication -/

section mul

variables {r : ℝ}

lemma real.mul_infi_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : r * (⨅ i, f i) = ⨅ i, r * f i :=
real.smul_infi_of_nonneg ha f

lemma real.mul_supr_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : r * (⨆ i, f i) = ⨆ i, r * f i :=
real.smul_supr_of_nonneg ha f

lemma real.mul_infi_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : r * (⨅ i, f i) = ⨆ i, r * f i :=
real.smul_infi_of_nonpos ha f

lemma real.mul_supr_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : r * (⨆ i, f i) = ⨅ i, r * f i :=
real.smul_supr_of_nonpos ha f

lemma real.infi_mul_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (⨅ i, f i) * r = ⨅ i, f i * r :=
by simp only [real.mul_infi_of_nonneg ha, mul_comm]

lemma real.supr_mul_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (⨆ i, f i) * r = ⨆ i, f i * r :=
by simp only [real.mul_supr_of_nonneg ha, mul_comm]

lemma real.infi_mul_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (⨅ i, f i) * r = ⨆ i, f i * r :=
by simp only [real.mul_infi_of_nonpos ha, mul_comm]

lemma real.supr_mul_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (⨆ i, f i) * r = ⨅ i, f i * r :=
by simp only [real.mul_supr_of_nonpos ha, mul_comm]

end mul

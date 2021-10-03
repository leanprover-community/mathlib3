/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import algebra.pointwise
import algebra.module.pi

/-!
# Pointwise actions on sets in Pi types

This file contains lemmas about pointwise actions on sets in Pi types.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication, pi

-/

open_locale pointwise
open set

variables {K ι : Type*} {R : ι → Type*}

@[to_additive]
lemma smul_pi_subset [∀ i, has_scalar K (R i)] (r : K) (s : set ι) (t : Π i, set (R i)) :
  r • pi s t ⊆ pi s (r • t) :=
begin
  rintros x ⟨y, h, rfl⟩ i hi,
  exact smul_mem_smul_set (h i hi),
end

@[to_additive]
lemma smul_univ_pi [∀ i, has_scalar K (R i)] (r : K) (t : Π i, set (R i)) :
  r • pi (univ : set ι) t = pi (univ : set ι) (r • t) :=
subset.antisymm (smul_pi_subset _ _ _) $ λ x h, begin
  refine ⟨λ i, classical.some (h i $ set.mem_univ _), λ i hi, _, funext $ λ i, _⟩,
  { exact (classical.some_spec (h i _)).left, },
  { exact (classical.some_spec (h i _)).right, },
end

@[to_additive]
lemma smul_pi [group K] [∀ i, mul_action K (R i)] (r : K) (S : set ι) (t : Π i, set (R i)) :
  r • S.pi t = S.pi (r • t) :=
subset.antisymm (smul_pi_subset _ _ _) $ λ x h,
  ⟨r⁻¹ • x, λ i hiS, mem_smul_set_iff_inv_smul_mem.mp (h i hiS), smul_inv_smul _ _⟩

lemma smul_pi₀ [group_with_zero K] [∀ i, mul_action K (R i)] {r : K} (S : set ι)
  (t : Π i, set (R i)) (hr : r ≠ 0) : r • S.pi t = S.pi (r • t) :=
smul_pi (units.mk0 r hr) S t

/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import data.set.pointwise.basic
import algebra.hom.iterate
import dynamics.fixed_points.basic

/-!
# Results about pointwise operations on sets with iteration.
-/

open_locale pointwise
open set function

@[to_additive]
lemma smul_eq_self_of_preimage_zpow_eq_self {G : Type*} [comm_group G]
  {n : ℤ} {s : set G} (hs : (λ x, x^n)⁻¹' s = s)
  {g : G} {j : ℕ} (hg : g^(n^j) = 1) : g • s = s :=
begin
  suffices : ∀ {g' : G} (hg' : g'^(n^j) = 1), g' • s ⊆ s,
  { refine le_antisymm (this hg) _,
    conv_lhs { rw ← smul_inv_smul g s, },
    replace hg : (g⁻¹)^(n^j) = 1, { rw [inv_zpow, hg, inv_one], },
    simpa only [le_eq_subset, set_smul_subset_set_smul_iff] using this hg, },
  rw (is_fixed_pt.preimage_iterate hs j : ((zpow_group_hom n)^[j])⁻¹' s = s).symm,
  rintros g' hg' - ⟨y, hy, rfl⟩,
  change ((zpow_group_hom n)^[j]) (g' * y) ∈ s,
  replace hg' : ((zpow_group_hom n)^[j]) g' = 1, { simpa [zpow_group_hom], },
  rwa [monoid_hom.iterate_map_mul, hg', one_mul],
end

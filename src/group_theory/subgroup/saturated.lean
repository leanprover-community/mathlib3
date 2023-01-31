/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import group_theory.subgroup.basic

/-!
# Saturated subgroups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Tags
subgroup, subgroups

-/

namespace subgroup

variables {G : Type*} [group G]

/-- A subgroup `H` of `G` is *saturated* if for all `n : ℕ` and `g : G` with `g^n ∈ H`
we have `n = 0` or `g ∈ H`. -/
@[to_additive "An additive subgroup `H` of `G` is *saturated* if
for all `n : ℕ` and `g : G` with `n•g ∈ H` we have `n = 0` or `g ∈ H`."]
def saturated (H : subgroup G) : Prop := ∀ ⦃n g⦄, g ^ n ∈ H → n = 0 ∨ g ∈ H

@[to_additive] lemma saturated_iff_npow {H : subgroup G} :
  saturated H ↔ (∀ (n : ℕ) (g : G), g ^ n ∈ H → n = 0 ∨ g ∈ H) := iff.rfl

@[to_additive] lemma saturated_iff_zpow {H : subgroup G} :
  saturated H ↔ (∀ (n : ℤ) (g : G), g ^ n ∈ H → n = 0 ∨ g ∈ H) :=
begin
  split,
  { rintros hH ⟨n⟩ g hgn,
    { simp only [int.coe_nat_eq_zero, int.of_nat_eq_coe, zpow_coe_nat] at hgn ⊢,
      exact hH hgn },
    { suffices : g ^ (n+1) ∈ H,
      { refine (hH this).imp _ id, simp only [is_empty.forall_iff, nat.succ_ne_zero], },
      simpa only [inv_mem_iff, zpow_neg_succ_of_nat] using hgn, } },
  { intros h n g hgn,
    specialize h n g,
    simp only [int.coe_nat_eq_zero, zpow_coe_nat] at h,
    apply h hgn }
end

end subgroup

namespace add_subgroup

lemma ker_saturated {A₁ A₂ : Type*} [add_comm_group A₁] [add_comm_group A₂]
  [no_zero_smul_divisors ℕ A₂] (f : A₁ →+ A₂) :
  (f.ker).saturated :=
begin
  intros n g hg,
  simpa only [f.mem_ker, nsmul_eq_smul, f.map_nsmul, smul_eq_zero] using hg
end

end add_subgroup

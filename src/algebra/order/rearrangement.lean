/-
Copyright (c) 2021 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import algebra.order.module
import group_theory.perm.sign
import order.monovary
import tactic.abel
import algebra.big_operators.basic

/-!
# Rearrangement inequality

This file proves the rearrangement inequality.

The rearrangement inequality tells you that for two functions `f g : ι → α`, the sum
`∑ i, f i * g (σ i)` is maximized over all `σ : perm ι` when `g ∘ σ` monovaries with `f` and
minimized when `g ∘ σ` antivaries with `f`.

The case for `monotone`/`antitone` pairs of functions over a `linear_order` is not deduced in this
file because the statement can be accessed using the `monovary` API.

Note : I'm currently very unsure if this theorem should have it's own file, please feel free to
comment on this
-/

open order_dual equiv
open_locale big_operators

variables {ι ι' α β γ : Type*}

namespace finset

lemma map_perm (s : finset ι) {σ : perm ι} (hs : {x | σ x ≠ x} ⊆ s) : s.map (σ : ι ↪ ι) = s :=
begin
  ext i,
  rw mem_map,
  obtain hi | hi := eq_or_ne (σ i) i,
  { refine ⟨_, λ h, ⟨i, h, hi⟩⟩,
    rintro ⟨j, hj, h⟩,
      rwa σ.injective (hi.trans h.symm) },
  { refine iff_of_true ⟨σ⁻¹ i, hs $ λ h, hi _, perm.apply_inv_self _ _⟩ (hs hi),
    convert congr_arg σ h; exact ( perm.apply_inv_self _ _).symm }
end

@[to_additive]
lemma prod_reindex [comm_monoid α] (s : finset ι) (f : ι → α) {σ : perm ι}
  (hs : {x | σ x ≠ x} ⊆ s) :
  (∏ i in s, f (σ i)) = ∏ i in s, f i :=
begin
  convert (prod_map _ σ.to_embedding _).symm,
  exact (s.map_perm hs).symm,
end

-- TODO: `to_additive` fails this one
lemma prod_reindex' [comm_monoid α] (s : finset ι) (f : ι → ι → α) {σ : perm ι}
  (hs : {x | σ x ≠ x} ⊆ s) :
  (∏ i in s, f (σ i) i) = ∏ i in s, f i (σ⁻¹ i) :=
begin
  convert s.prod_reindex (λ i, f i (σ⁻¹ i)) hs,
  ext,
  rw perm.inv_apply_self,
end

lemma sum_reindex' [add_comm_monoid α] (s : finset ι) (f : ι → ι → α) {σ : perm ι}
  (hs : {x | σ x ≠ x} ⊆ s) :
  (∑ i in s, f (σ i) i) = ∑ i in s, f i (σ⁻¹ i) :=
begin
  convert s.sum_reindex (λ i, f i (σ⁻¹ i)) hs,
  ext,
  rw perm.inv_apply_self,
end

end finset

open finset equiv equiv.perm order_dual
open_locale big_operators

/-- **Rearrangement Inequality** : statement for a pair of functions that given a finset `s`,
`movary_on f g s` holds with the permutation applied on the right.-/
theorem monovary_on.sum_smul_comp_perm_le_sum_smul [linear_ordered_ring α]
  [linear_ordered_add_comm_group β] [module α β] [ordered_smul α β]
  {s : finset ι} {f : ι → α} {g : ι → β} (hfg : monovary_on f g s) {σ : perm ι}
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g (σ i) ≤ ∑ i in s, f i • g i :=
begin
  classical,
  revert hσ σ hfg,
  apply finset.induction_on_max_value (λ i, to_lex (g i, f i)) s,
  { simp only [le_refl, finset.sum_empty, implies_true_iff] },
  intros a s has hamax hind hfg σ hσ,
  set τ : perm ι := σ.trans (swap a (σ a)) with hτ,
  have hτs : {x | τ x ≠ x} ⊆ s,
  { intros x hx,
    simp only [ne.def, set.mem_set_of_eq, equiv.coe_trans, equiv.swap_comp_apply] at hx,
    split_ifs at hx with h₁ h₂ h₃,
    { obtain rfl | hax := eq_or_ne x a,
      { contradiction },
      { apply mem_of_mem_insert_of_ne _ hax,
        apply hσ,
        simp only [ne.def, set.mem_set_of_eq, h₁, hax.symm, not_false_iff] } },
    { exfalso,
      apply hx,
      rw [← apply_eq_iff_eq σ, h₂] },
    { rw apply_eq_iff_eq at h₂,
      apply mem_of_mem_insert_of_ne _ h₂,
      apply hσ,
      simp only [ne.def, set.mem_set_of_eq, hx, not_false_iff] } },
  specialize hind (hfg.subset _ ) hτs,
  { simp only [coe_insert, set.subset_insert] },
  replace hind := add_le_add_left hind (f a • g a),
  rw ← sum_insert has at hind,
  apply le_trans _ hind,
  obtain hσa | hσa := eq_or_ne a (σ a),
  { rw [sum_insert has, ← hσa],
    apply add_le_add_left,
    refine (sum_congr rfl $ λ x hx, _).le,
    congr,
    rw [hτ, ← hσa, swap_self, trans_refl] },
  have h1s : σ⁻¹ a ∈ s,
  { suffices : σ⁻¹ a ∈ {x | σ x ≠ x},
    { specialize hσ this,
      simp only [coe_insert, set.mem_insert_iff, mem_coe, inv_eq_iff_eq] at hσ,
      cases hσ,
      { exfalso,
        apply hσa hσ },
      { exact mem_coe.mpr hσ } },
    simp only [ne.def, apply_inv_self, set.mem_set_of_eq, eq_inv_iff_eq],
    exact (push_neg.not_eq (σ a) a).mpr (ne.symm hσa) },
  simp only [sum_insert has, ← s.sum_erase_add _ h1s, coe_fn_mk, add_comm],
  rw [← add_assoc, ← add_assoc],
  refine add_le_add _ (sum_congr rfl $ λ x hx, _).le,
  { simp only [hτ, swap_apply_left, function.comp_app, equiv.coe_trans, apply_inv_self],
    suffices : 0 ≤ (f a - f (σ⁻¹ a)) • (g a - g (σ a)),
    { rw ← sub_nonneg,
      convert this,
      simp only [smul_sub, sub_smul],
      abel },
    have h2s : σ a ∈ s,
    { suffices : σ a ∈ {x | σ x ≠ x},
      { specialize hσ this,
        simp only [coe_insert, set.mem_insert_iff, mem_coe] at hσ,
        cases hσ,
        { simp only [ne.def, set.mem_set_of_eq, apply_eq_iff_eq] at this,
          contradiction },
        { exact hσ } },
      simp only [ne.def, set.mem_set_of_eq, apply_eq_iff_eq],
      exact (push_neg.not_eq (σ a) a).mpr (ne.symm hσa) },
    apply smul_nonneg,
    { rw sub_nonneg,
      specialize hamax (σ⁻¹ a) h1s,
      rw prod.lex.le_iff at hamax,
      cases hamax,
      { apply hfg _ _ hamax,
        { simp only [h1s, coe_insert, set.mem_insert_iff, mem_coe, or_true] },
        { simp only [coe_insert, set.mem_insert_iff, true_or, eq_self_iff_true] }},
      { exact hamax.2 } },
    { rw sub_nonneg,
      specialize hamax (σ a) h2s,
      rw prod.lex.le_iff at hamax,
      cases hamax,
      { exact hamax.le },
      { exact hamax.1.le } } },
  { congr' 2,
    symmetry,
    simp only [hτ, function.comp_app, equiv.coe_trans],
    simp only [mem_erase, ne.def, eq_inv_iff_eq] at hx,
    apply swap_apply_of_ne_of_ne,
    { exact hx.1 },
    { simp only [ne.def, apply_eq_iff_eq],
      rintros rfl,
      apply has hx.2 } }
end

/-- **Rearrangement Inequality** : statement for a pair of functions that given a finset `s`,
`movary_on f g s` holds with the permutation applied on the left.-/
theorem monovary_on.sum_comp_perm_smul_le_sum_smul [linear_ordered_ring α]
  [linear_ordered_add_comm_group β] [module α β] [ordered_smul α β]
  {s : finset ι} {f : ι → α} {g : ι → β} (hfg : monovary_on f g s) {σ : perm ι}
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f (σ i) • g i ≤ ∑ i in s, f i • g i :=
begin
  convert hfg.sum_smul_comp_perm_le_sum_smul
    (show {x | σ⁻¹ x ≠ x} ⊆ s, by simp only [set_support_inv_eq, hσ]) using 1,
  exact sum_reindex' s (λ i j, f i • g j) hσ
end

/-- **Rearrangement Inequality** : statement for a pair of functions that given a finset `s`,
`antivary_on f g s` holds with the permutation applied on the right.-/
theorem antivary_on.sum_smul_le_sum_smul_comp_perm
  [linear_ordered_ring α] [linear_ordered_add_comm_group β] [module α β] [ordered_smul α β]
  {s : finset ι} {f : ι → α} {g : ι → β} (hfg : antivary_on f g s) {σ : perm ι}
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g i ≤ ∑ i in s, f i • g (σ i) :=
hfg.dual_right.sum_smul_comp_perm_le_sum_smul hσ

/-- **Rearrangement Inequality** : statement for a pair of functions that given a finset `s`,
`antivary_on f g s` holds with the permutation applied on the left.-/
theorem antivary_on.sum_smul_le_sum_comp_perm_smul [linear_ordered_ring α]
  [linear_ordered_add_comm_group β] [module α β] [ordered_smul α β]
  {s : finset ι} {f : ι → α} {g : ι → β} (hfg : antivary_on f g s) {σ : perm ι}
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g i ≤ ∑ i in s, f (σ i) • g i :=
begin
  convert hfg.sum_smul_le_sum_smul_comp_perm
    (show {x | σ⁻¹ x ≠ x} ⊆ s, by simp only [set_support_inv_eq, hσ]) using 1,
  exact sum_reindex' s (λ i j, f i • g j) hσ
end

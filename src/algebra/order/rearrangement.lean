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
  set k := σ a with hk,
  set j := σ⁻¹ a with hj,
  set p : ι → ι := λ x, if x = a then a else if x = j then k else σ x with hp,
  set q : ι → ι := λ x, if x = a then a else if x = k then j else σ⁻¹ x with hq,
  have hqpleft : function.left_inverse q p,
  { intro x,
    simp only [hp, hq],
    split_ifs with h₁ h₂ h₃ h₄ h₅,
    { rw h₁ },
    { rw [h₂, hj, eq_inv_iff_eq, ← hk, h₃] },
    { rw h₂ },
    { exfalso,
      apply h₂,
      rw [hj, eq_inv_iff_eq, h₄] },
    { exfalso,
      apply h₁,
      simp only [←inv_eq_iff_eq, inv_apply_self] at h₅,
      exact h₅ },
    { simp only [inv_apply_self] } },
  have hqpright : function.right_inverse q p,
  { intro x,
    simp only [hp, hq],
    split_ifs with h₁ h₂ h₃ h₄ h₅,
    { rw ← h₁ },
    { rw [h₂, hk, ← inv_eq_iff_eq, ← hj, h₃] },
    { rw h₂ },
    { exfalso,
      apply h₂,
      rw [hk, ← inv_eq_iff_eq, h₄] },
    { exfalso,
      apply h₁,
      simp only [←inv_eq_iff_eq, inv_apply_self] at h₅,
      exact h₅ },
    { simp only [apply_inv_self] } },
  set τ : perm ι := by use [p, q, hqpleft, hqpright] with hτ,
  have hτs : {x | τ x ≠ x} ⊆ s,
  { intros x hx,
    simp only [coe_fn_mk, hp, ne.def, set.mem_set_of_eq] at hx,
    split_ifs at hx with h₁ h₂ h₃,
    { exfalso,
      apply hx (h₁.symm) },
    { rw h₂,
      rw h₂ at h₁,
      have hjs : σ j ≠ j,
      { simp only [ne.def, apply_inv_self],
        exact (push_neg.not_eq a j).mpr (ne.symm h₁) },
      specialize hσ hjs,
      simp only [mem_insert, mem_coe] at hσ,
      cases hσ,
      { exfalso,
        apply h₁ hσ },
      { exact mem_coe.mpr hσ} },
    { specialize hσ hx,
      simp only [mem_insert, mem_coe] at hσ,
      cases hσ,
      { exfalso,
        apply h₁ hσ },
      { exact mem_coe.mpr hσ } } },
  specialize hind (hfg.subset _ ) hτs,
  { simp only [coe_insert, set.subset_insert] },
  replace hind := add_le_add_left hind (f a • g a),
  rw ← sum_insert has at hind,
  apply le_trans _ hind,
  obtain hja | hja := eq_or_ne j a,
  { rw sum_insert has,
    simp only [←hja, coe_fn_mk, coe_fn_mk, add_le_add_iff_left, apply_inv_self],
    refine (sum_congr rfl $ λ x hx, _).le,
    congr,
    simp only [hp],
    rw [hja, if_neg (ne_of_mem_of_not_mem hx has), if_neg (ne_of_mem_of_not_mem hx has)] },
  have hjs : j ∈ s,
  { suffices : j ∈ {x | σ x ≠ x},
    { specialize hσ this,
      simp only [coe_insert, set.mem_insert_iff, mem_coe] at hσ,
      cases hσ,
      { exfalso,
        apply hja hσ },
      { exact mem_coe.mpr hσ } },
    simp only [ne.def, apply_inv_self, set.mem_set_of_eq],
    exact (push_neg.not_eq a j).mpr (ne.symm hja) },
  simp only [sum_insert has, ← s.sum_erase_add _ hjs, coe_fn_mk, add_comm],
  rw [← add_assoc, ← add_assoc],
  refine add_le_add _ (sum_congr rfl $ λ x hx, _).le,
  { have hpj : p j = k,
    { simp only [hp],
      rw [if_pos rfl, if_neg hja] },
    simp only [← hk, apply_inv_self, hpj],
    suffices : 0 ≤ (f a - f j) • (g a - g k),
    { rw ← sub_nonneg,
      convert this,
      simp only [smul_sub, sub_smul],
      abel },
    have hks : k ∈ s,
    { suffices : k ∈ {x | σ x ≠ x},
      { specialize hσ this,
        simp only [coe_insert, set.mem_insert_iff, mem_coe] at hσ,
        cases hσ,
        { exfalso,
          simp only [← eq_inv_iff_eq] at hσ,
          rw ← hj at hσ,
          apply hja,
          rw hσ },
        { exact hσ } },
      simp only [ne.def, ←eq_inv_iff_eq, inv_apply_self, set.mem_set_of_eq],
      intro hka,
      apply hja,
      rw [hka, hj] },
    apply smul_nonneg,
    { rw sub_nonneg,
      specialize hamax j hjs,
      rw prod.lex.le_iff at hamax,
      cases hamax,
      { apply hfg _ _ hamax,
        { simp only [hjs, coe_insert, set.mem_insert_iff, mem_coe, or_true] },
        { simp only [coe_insert, set.mem_insert_iff, true_or, eq_self_iff_true] }},
      { exact hamax.2 } },
    { rw sub_nonneg,
      specialize hamax k hks,
      rw prod.lex.le_iff at hamax,
      cases hamax,
      { exact hamax.le },
      { exact hamax.1.le } } },
  { congr,
    simp only [hp],
    rw [if_neg (ne_of_mem_of_not_mem (mem_of_mem_erase hx) has), if_neg (ne_of_mem_erase hx)] }
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

lemma swap_extend_domain_eq_self [decidable_eq ι] (s : finset ι) (x y : s) :
  (@extend_domain s ι (swap x y) (λ x, x ∈ s) _ 1) = swap ↑x ↑y :=
begin
  ext a,
  by_cases ha : a ∈ s,
  { rw extend_domain_apply_subtype, swap, exact ha,
    simp only [coe_one, id.def, one_symm],
    obtain rfl | hax := eq_or_ne x ⟨a, ha⟩,
    { rw [swap_apply_left, swap, coe_fn_mk, swap_core, subtype.coe_mk],
      exact (if_pos rfl).symm },
    obtain rfl | hay := eq_or_ne y ⟨a, ha⟩,
    { rw [swap_apply_right, swap, coe_fn_mk, swap_core, subtype.coe_mk, if_pos rfl],
      exact (ite_eq_right_iff.2 id).symm },
    { rw swap_apply_of_ne_of_ne hax.symm hay.symm,
      exact (swap_apply_of_ne_of_ne (subtype.coe_injective.ne hax.symm) $
        subtype.coe_injective.ne hay.symm).symm } },
  { rw [extend_domain_apply_not_subtype, swap_apply_of_ne_of_ne
      (ne_of_mem_of_not_mem x.prop ha).symm (ne_of_mem_of_not_mem y.prop ha).symm],
    exact ha }
end

theorem equiv.perm.swap_induction_on'_support {ι : Type*} [decidable_eq ι] [fintype ι]
  (s : finset ι) {P : (perm ι) → Prop} (σ : perm ι) (hσ : σ.support ⊆ s ) :
  P 1 → (∀ (f : perm ι) x y, x ≠ y → x ∈ s → y ∈ s → (f.support ⊆ s → P f) →
    ((f * swap x y).support ⊆ s → P (f * swap x y))) → P σ :=
begin
  have hσ1 : ∀ x, x ∈ s ↔ σ x ∈ s,
  { intro x,
    by_cases hx : x ∈ σ.support,
    { exact ⟨λ hs, hσ $ perm.apply_mem_support.2 hx, λ hσx, hσ hx⟩ },
    { rw not_mem_support.1 hx } },
    set τ : perm s := perm.subtype_perm σ hσ1 with hτs,
    intros h1 hind,
    suffices : P (@extend_domain s ι τ (λ x, x ∈ s) _ 1),
    { convert this,
      ext x,
      by_cases hx : x ∈ s,
      { rw [hτs, extend_domain_apply_subtype],
        { simp only [subtype_perm_apply, coe_one, id.def, one_symm, subtype.coe_mk] },
        { exact hx } },
      { rw [hτs, not_mem_support.1 (λ h, hx $ hσ h), extend_domain_apply_not_subtype],
        exact hx } },
    suffices : (P ∘ λ (f : perm s), (@extend_domain s ι f (λ x, x ∈ s) _ 1)) τ, { exact this },
    apply swap_induction_on' τ,
    { simp only [extend_domain_one, function.comp_app, h1] },
    { intros π x y hxy hπ,
      specialize hind (@extend_domain s ι π (λ x, x ∈ s) _ 1) x y,
      suffices : P ((@extend_domain s ι π (λ x, x ∈ s) _ 1) * swap x y),
      { rw function.comp_apply,
        convert this,
        rw ← extend_domain_mul,
        congr,
        exact swap_extend_domain_eq_self s x y},
      apply hind,
      { simp only [ne.def, ← subtype.ext_iff, hxy, not_false_iff] },
      { exact coe_mem x },
      { exact coe_mem y },
      { intro,
        exact hπ },
      { apply subset.trans (support_mul_le _ _),
        apply union_subset,
        { intros z hz,
          rw mem_support at hz,
          by_cases hzs : z ∈ s, {exact hzs},
          exfalso,
          apply hz,
          rw extend_domain_apply_not_subtype,
          exact hzs },
        { intros z hz,
          replace hxy : (x : ι) ≠ y,
          { intro hyx,
            apply hxy,
            rw [subtype.ext_iff, hyx] },
          simp only [(support_swap hxy), mem_insert, mem_singleton] at hz,
          cases hz,
          { subst z,
            exact coe_mem x},
          { subst z,
            exact coe_mem y} } } }
end

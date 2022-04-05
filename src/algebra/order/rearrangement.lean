/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import algebra.big_operators.order
import algebra.order.module
import group_theory.perm.concrete_cycle
import order.monovary
import tactic.interval_cases

/-!
# Rearrangement inequality

This file proves the rearrangement inequality.

The rearrangement inequality tells you that for two functions `f g : ι → α`, the sum
`∑ i, f i * g (σ i)` is maximized over all `σ : perm ι` when `g ∘ σ` monovaries with `f` and
minimized when `g ∘ σ` antivaries with `f`.

## Implementation notes

In fact, we don't need much compatibility between the addition and multiplication of `α`, so we can
actually decouple them by replacing multiplication with scalar multiplication and making `f` and `g`
land in different types.
As a bonus, this makes the dual statement trivial. The multiplication versions are provided for
convenience.

The case for `monotone`/`antitone` pairs of functions over a `linear_order` is not deduced in this
file because it is easily deducible from the `monovary` API.
-/

open equiv equiv.perm finset order_dual
open_locale big_operators

variables {ι α β : Type*}

-- move to `group_theory.perm.list`
theorem list.form_perm_mem_of_apply_mem {α : Type*} [decidable_eq α] (x : α) (l : list α)
  (h : l.form_perm x ∈ l) : x ∈ l :=
begin
  cases l with y l,
  { simpa },
  induction l with z l IH generalizing x y,
  { simpa using h },
  { by_cases hx : (z :: l).form_perm x ∈ z :: l,
    { rw [list.form_perm_cons_cons, mul_apply, swap_apply_def] at h,
      split_ifs at h;
      simp [IH _ _ hx] },
    { replace hx := (function.injective.eq_iff (equiv.injective _)).mp
        (list.form_perm_apply_of_not_mem _ _ hx),
      simp only [list.form_perm_cons_cons, hx, equiv.perm.coe_mul, function.comp_app,
        list.mem_cons_iff, swap_apply_def, ite_eq_left_iff] at h,
      simp only [list.mem_cons_iff],
      obtain h | h | h := h;
      { split_ifs at h;
        cc } } }
end

-- move to `group_theory.perm.list`
theorem list.form_perm_mem_iff_mem {α : Type*} [decidable_eq α] (x : α) (l : list α) :
  x ∈ l ↔ l.form_perm x ∈ l :=
by exact ⟨λ h, l.form_perm_apply_mem_of_mem x h, λ h, l.form_perm_mem_of_apply_mem x h⟩

-- move to `group_theory.perm.list`
theorem list.form_perm_mem_of_apply_ne {α : Type*} [decidable_eq α] (x : α) (l : list α)
  (h : l.form_perm x ≠ x) : x ∈ l :=
begin
  contrapose! h,
  exact list.form_perm_apply_of_not_mem _ _ h
end

-- move to `group_theory.perm.basic`
lemma subtype_perm_support_eq (f : perm α) {p : α → Prop} (h : ∀ x, p x ↔ p (f x)) :
  {x | (subtype_perm f h) x ≠ x} = {x | f x ≠ x} :=
begin
  ext y,
  simp only [subtype_perm_apply, ne.def, set.mem_set_of_eq],
  refine ⟨λ hy, _, λ hy, _⟩,
  { contrapose! hy,
    cases subtype.coe_eq_iff.mp (eq.symm hy) with z hz,
    conv_rhs { rw hz } },
  { contrapose! hy,
    exact (subtype.coe_inj.mpr hy) }
end

/-! ### Scalar multiplication versions -/

section smul
variables [linear_ordered_ring α] [linear_ordered_add_comm_group β] [module α β]
  [ordered_smul α β] {s : finset ι} {σ : perm ι} {f : ι → α} {g : ι → β}

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` vary together. Stated by permuting the entries of `g`.  -/
lemma monovary_on.sum_smul_comp_perm_le_sum_smul (hfg : monovary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g (σ i) ≤ ∑ i in s, f i • g i :=
begin
  classical,
  revert hσ σ hfg,
  apply finset.induction_on_max_value (λ i, to_lex (g i, f i)) s,
  { simp only [le_rfl, finset.sum_empty, implies_true_iff] },
  intros a s has hamax hind σ hfg hσ,
  set τ : perm ι := σ.trans (swap a (σ a)) with hτ,
  have hτs : {x | τ x ≠ x} ⊆ s,
  { intros x hx,
    simp only [ne.def, set.mem_set_of_eq, equiv.coe_trans, equiv.swap_comp_apply] at hx,
    split_ifs at hx with h₁ h₂ h₃,
    { obtain rfl | hax := eq_or_ne x a,
      { contradiction },
      { exact mem_of_mem_insert_of_ne (hσ $ λ h, hax $ h.symm.trans h₁) hax } },
    { exact (hx $ σ.injective h₂.symm).elim },
    { exact mem_of_mem_insert_of_ne (hσ hx) (ne_of_apply_ne _ h₂) } },
  specialize hind (hfg.subset $ subset_insert _ _) hτs,
  simp_rw sum_insert has,
  refine le_trans _ (add_le_add_left hind _),
  obtain hσa | hσa := eq_or_ne a (σ a),
  { rw [←hσa, swap_self, trans_refl] at hτ,
    rw [←hσa, hτ] },
  have h1s : σ⁻¹ a ∈ s,
  { rw [ne.def, ←inv_eq_iff_eq] at hσa,
    refine mem_of_mem_insert_of_ne (hσ $ λ h, hσa _) hσa,
    rwa [apply_inv_self, eq_comm] at h },
  simp only [← s.sum_erase_add _ h1s, add_comm],
  rw [← add_assoc, ← add_assoc],
  refine add_le_add _ (sum_congr rfl $ λ x hx, _).le,
  { simp only [hτ, swap_apply_left, function.comp_app, equiv.coe_trans, apply_inv_self],
    suffices : 0 ≤ (f a - f (σ⁻¹ a)) • (g a - g (σ a)),
    { rw ← sub_nonneg,
      convert this,
      simp only [smul_sub, sub_smul],
      abel },
    refine smul_nonneg (sub_nonneg_of_le _) (sub_nonneg_of_le _),
    { specialize hamax (σ⁻¹ a) h1s,
      rw prod.lex.le_iff at hamax,
      cases hamax,
      { exact hfg (mem_insert_of_mem h1s) (mem_insert_self _ _) hamax },
      { exact hamax.2 } },
    { specialize hamax (σ a) (mem_of_mem_insert_of_ne (hσ $ σ.injective.ne hσa.symm) hσa.symm),
      rw prod.lex.le_iff at hamax,
      cases hamax,
      { exact hamax.le },
      { exact hamax.1.le } } },
  { congr' 2,
    rw [eq_comm, hτ],
    rw [mem_erase, ne.def, eq_inv_iff_eq] at hx,
    refine swap_apply_of_ne_of_ne hx.1 (σ.injective.ne _),
    rintro rfl,
    exact has hx.2 }
end

-- to put into `algebra.module.basic`
theorem finset.sum_smul_sum {R : Type*} {M : Type*} {ι : Type*} [semiring R] [add_comm_monoid M]
  [module R M] {f : ι → R} {g : ι → M} {s t : finset ι} :
(∑ i in s, f i) • (∑ i in t, g i) = ∑ p in s.product t, (f p.fst) • g p.snd :=
by { rw [sum_product, sum_smul, sum_congr rfl], intros, rw smul_sum }

lemma finset.product_self_eq_range_bUnion_perm [decidable_eq ι] (π : perm s) (hπ : π.is_cycle)
  (hπs : π.support = univ) : s.product s =
  (finset.range s.card).bUnion (λ k, s.bUnion $ λ i, {(i, (π^k).subtype_congr (equiv.refl _) i)}) :=
begin
  ext,
  obtain hs | hs := eq_or_ne s.card 0,
  { simp only [finset.card_eq_zero.mp hs, mem_product, not_mem_empty, and_self, card_empty,
      range_zero, bUnion_empty] },
  { simp only [mem_bUnion, mem_range, mem_singleton, exists_prop, mem_product],
    refine ⟨λ h, _, λ h, _⟩,
    { have hπ1 : π ⟨a.1, h.1⟩ ≠ ⟨a.1, h.1⟩,
      { simp only [← equiv.perm.mem_support, hπs, mem_univ] },
      have hπ2 : π ⟨a.2, h.2⟩ ≠ ⟨a.2, h.2⟩,
      { simp only [← equiv.perm.mem_support, hπs, mem_univ] },
      cases hπ.exists_pow_eq hπ1 hπ2 with i hi,
      replace hi : (π ^ (i % s.card)) ⟨a.fst, _⟩ = ⟨a.snd, _⟩,
      { convert hi using 2,
        convert (eq.symm pow_eq_mod_order_of),
        simp only [equiv.perm.order_of_is_cycle hπ, hπs, univ_eq_attach, card_attach] },
      refine ⟨i % s.card, _, a.1, h.1, _⟩,
      { exact nat.mod_lt _ (pos_iff_ne_zero.mpr hs) },
      { ext, refl,
        rw equiv.perm.subtype_congr.left_apply,
        { simp only [hi, subtype.coe_mk] },
        { exact h.1 } } },
    { rcases h with ⟨k, hk, b, hbs, h⟩,
      rw h,
      refine ⟨by simpa using hbs, _⟩,
      rw equiv.perm.subtype_congr.left_apply,
      simp only [coe_mem],
      exact hbs } }
end

-- to move to `group_theory.perm.cycles`
lemma is_cycle.pow_eq_pow_iff [fintype ι] [decidable_eq ι] {f : perm ι} (hf : is_cycle f)
  {a b : ℕ} : f ^ a = f ^ b ↔ ∃ (x ∈ f.support), (f ^ a) x = (f ^ b) x :=
begin
  split,
  { intro h,
    obtain ⟨x, hx, -⟩ := id hf,
    exact ⟨x, mem_support.mpr hx, by simp [h]⟩ },
  { rintro ⟨x, hx, hx'⟩,
    obtain hab | rfl | hab := lt_trichotomy a b,
    { suffices : f ^ (b - a) = 1,
      { rw [pow_sub _ (le_of_lt hab), mul_inv_eq_one] at this,
        rw this },
      rw hf.pow_eq_one_iff,
      by_cases hfa : (f ^ a) x ∈ f.support,
      { refine ⟨(f ^ a) x, hfa, _⟩,
        simp only [pow_sub _ (le_of_lt hab), equiv.perm.coe_mul, function.comp_app,
          inv_apply_self, ← hx'] },
      { have h := @equiv.perm.zpow_apply_comm _ f 1 a x,
        simp only [zpow_one, zpow_coe_nat] at h,
        rw [not_mem_support, h, function.injective.eq_iff (f ^ a).injective] at hfa,
        exfalso,
        exact (mem_support.mp hx) hfa } },
    { refl },
    { suffices : f ^ (a - b) = 1,
      { rw [pow_sub _ (le_of_lt hab), mul_inv_eq_one] at this,
        rw this },
      rw hf.pow_eq_one_iff,
      by_cases hfa : (f ^ b) x ∈ f.support,
      { refine ⟨(f ^ b) x, hfa, _⟩,
        simp only [pow_sub _ (le_of_lt hab), equiv.perm.coe_mul, function.comp_app,
          inv_apply_self, hx'] },
      { have h := @equiv.perm.zpow_apply_comm _ f 1 b x,
        simp only [zpow_one, zpow_coe_nat] at h,
        rw [not_mem_support, h, function.injective.eq_iff (f ^ b).injective] at hfa,
        exfalso,
        exact (mem_support.mp hx) hfa } } }
end

-- where to move?
lemma sum_mul_sum_eq_sum_perm [decidable_eq ι] (s : finset ι) (π : perm s) (hπ : π.is_cycle)
  (hπs : π.support = univ) : (∑ i in s, f i) • (∑ i in s, g i) =
    ∑ k in finset.range s.card, (∑ i in s, f i • g ((π^k).subtype_congr (equiv.refl _) i)) :=
begin
  rw [finset.sum_smul_sum, finset.product_self_eq_range_bUnion_perm π hπ hπs, finset.sum_bUnion _],
  { apply finset.sum_congr rfl,
    intros x hx,
    rw finset.sum_bUnion _,
    { apply finset.sum_congr rfl,
      exact λ y hy, sum_singleton },
    { rintros a ha b hb hab ⟨c, d⟩ h,
      simp only [inf_eq_inter, mem_inter, mem_singleton, prod.mk.inj_iff] at h,
      exfalso, apply hab,
      rw [← h.1.1, h.2.1] } },
    { rintros a ha b hb hab ⟨c, d⟩ h,
      simp only [inf_eq_inter, mem_inter, mem_bUnion, mem_singleton, prod.mk.inj_iff,
        exists_prop] at h,
      rcases h with ⟨⟨e, he⟩, ⟨f, hf⟩⟩,
      have h : ((π ^ a).subtype_congr (equiv.refl {a // a ∉ s})) c =
        ((π ^ b).subtype_congr (equiv.refl {a // a ∉ s})) c,
      { conv_lhs { rw [he.2.1, ← he.2.2, hf.2.2, ← hf.2.1] } },
      have hc : c ∈ s := by simp only [he.2.1, he.1],
      replace h : (π ^ a) ⟨c, hc⟩ = (π ^ b) ⟨c, hc⟩,
      { rw [equiv.perm.subtype_congr.left_apply _] at h,
        swap, exact hc,
        rw [equiv.perm.subtype_congr.left_apply _] at h,
        swap, exact hc,
        simp only [← @subtype.coe_inj ι _ _, h] },
      replace h : π ^ a = π ^ b,
      { rw is_cycle.pow_eq_pow_iff hπ,
        exact ⟨⟨c, hc⟩, by simp only [hπs, mem_univ], h⟩ },
      simp only [pow_eq_pow_iff_modeq, equiv.perm.order_of_is_cycle hπ, hπs,
        univ_eq_attach, card_attach] at h,
      exfalso,
      apply hab,
      rw [nat.modeq.eq_of_modeq_of_abs_lt h _],
      rw abs_sub_lt_iff,
      simp only [mem_coe, mem_range] at *,
      split; linarith },
end

@[simp] lemma image_set_of {α β : Type*} (p : α → Prop) (f : α → β) :
  f '' {a | p a} = {b | ∃ a, p a ∧ f a = b} :=
set.ext $ set.mem_image _ _

/-- **Chebyshev Inequality**: When `f` and `g` vary together, the scalar product of their sum is
less than the size of the set times their scalar product. -/
lemma monovary.sum_smul_sum_le_card_smul_sum [decidable_eq ι] (hfg : monovary_on f g s) :
  (∑ i in s, f i) • (∑ i in s, g i) ≤ (∑ i in s, (s.card • f i) • g i) :=
begin
  -- condition on cases of size of `s`, as we can for cycles only when `2 ≤ s.card`
  obtain hs | hs := lt_or_ge s.card 2,
  { interval_cases s.card,
    { simp only [card_eq_zero.mp h, finset.sum_empty, zero_smul] },
    { cases (card_eq_one.mp h) with a ha,
      simp only [ha, sum_singleton, card_singleton, nsmul_eq_mul, nat.cast_one, one_mul] } },
  { set π : perm s :=
    begin
      refine equiv.perm.subtype_perm (s.to_list.form_perm) _,
      simp_rw ← finset.mem_to_list,
      exact λ x, (s.to_list).form_perm_mem_iff_mem x
    end with hπ,
    have hπc : π.is_cycle,
    { replace hs : 2 ≤ s.to_list.length := by simpa using hs,
      have h := list.is_cycle_form_perm (nodup_to_list s) hs,
      rcases h with ⟨x, hx, h⟩,
      have hxs := s.mem_to_list.mp (list.form_perm_mem_of_apply_ne _ _ hx),
      refine ⟨⟨x, hxs⟩, _, λ y hy, _⟩,
      { simpa using hx },
      { replace hy : (s.to_list.form_perm) y ≠ y,
        { contrapose! hy,
          cases subtype.coe_eq_iff.mp (eq.symm hy) with z hz,
          simp only [subtype_perm_apply],
          conv_rhs { rw hz } },
        cases (h y hy) with i hi,
        use i,
        cases subtype.coe_eq_iff.mp (eq.symm hi) with z hz,
        conv_rhs { rw hz },
        rw [← subtype.coe_inj, ← of_subtype_apply_of_mem (π ^ i)],
        sorry -- what power lemmas do I want here?
         } },
    have hπs : π.support = univ,
    -- here, I tried proving `subtype_perm_support_eq` above to help but it doesn't seem to typecheck,
    -- any suggestions how this proof could go?
    { suffices h1 : {x | (s.to_list).form_perm x ≠ x} = s,
      { suffices h2 : (π.support : set s) = set.univ,
        { ext x,
          replace h2 := (set.ext_iff.mp h2) x,
          simp only [mem_coe] at h2,
          convert h2 using 1; simp },
        { simp only [coe_support_eq_set_support, hπ],
          sorry } },
      { rw list.support_form_perm_of_nodup' s.to_list (nodup_to_list s),
        { simp only [to_list_to_finset]},
        { simp only [ne.def],
          intros y hsy,
          replace hsy : s.to_list.length = 1,
          { rw list.length_eq_one,
            exact ⟨y, hsy⟩ },
          simp only [finset.length_to_list] at hsy,
          linarith } } },
    rw (sum_mul_sum_eq_sum_perm s π hπc hπs),
    have : ∑ (k : ℕ) in range s.card,
    ∑ (i : ι) in s, f i • g (((π ^ k).subtype_congr (equiv.refl _)) i) ≤
      ∑ (k : ℕ) in range s.card, ∑ (i : ι) in s, f i • g i,
    { apply finset.sum_le_sum,
      intros k hk,
      convert monovary_on.sum_smul_comp_perm_le_sum_smul hfg _,
      intros x hx,
      contrapose! hx,
      simp only [set.mem_set_of_eq, not_not],
      rw equiv.perm.subtype_congr.right_apply,
      simp only [coe_refl, id.def, subtype.coe_mk],
      contrapose! hx,
      exact mem_coe.mpr hx },
    apply le_trans this,
    apply le_of_eq,
    simp only [sum_const, card_range, mul_smul, smul_sum, smul_assoc],
    apply_instance}
end

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` vary together. Stated by permuting the entries of `f`. -/
lemma monovary_on.sum_comp_perm_smul_le_sum_smul (hfg : monovary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f (σ i) • g i ≤ ∑ i in s, f i • g i :=
begin
  convert hfg.sum_smul_comp_perm_le_sum_smul
    (show {x | σ⁻¹ x ≠ x} ⊆ s, by simp only [set_support_inv_eq, hσ]) using 1,
  exact σ.sum_comp' s (λ i j, f i • g j) hσ,
end

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `g`.-/
lemma antivary_on.sum_smul_le_sum_smul_comp_perm (hfg : antivary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g i ≤ ∑ i in s, f i • g (σ i) :=
hfg.dual_right.sum_smul_comp_perm_le_sum_smul hσ

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `f`. -/
lemma antivary_on.sum_smul_le_sum_comp_perm_smul (hfg : antivary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g i ≤ ∑ i in s, f (σ i) • g i :=
hfg.dual_right.sum_comp_perm_smul_le_sum_smul hσ

variables [fintype ι]

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` vary together. Stated by permuting the entries of `g`.  -/
lemma monovary.sum_smul_comp_perm_le_sum_smul (hfg : monovary f g) :
  ∑ i, f i • g (σ i) ≤ ∑ i, f i • g i :=
(hfg.monovary_on _).sum_smul_comp_perm_le_sum_smul $ λ i _, mem_univ _

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` vary together. Stated by permuting the entries of `f`. -/
lemma monovary.sum_comp_perm_smul_le_sum_smul (hfg : monovary f g) :
  ∑ i, f (σ i) • g i ≤ ∑ i, f i • g i :=
(hfg.monovary_on _).sum_comp_perm_smul_le_sum_smul $ λ i _, mem_univ _

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `g`.-/
lemma antivary.sum_smul_le_sum_smul_comp_perm (hfg : antivary f g) :
  ∑ i, f i • g i ≤ ∑ i, f i • g (σ i) :=
(hfg.antivary_on _).sum_smul_le_sum_smul_comp_perm $ λ i _, mem_univ _

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `f`. -/
lemma antivary.sum_smul_le_sum_comp_perm_smul (hfg : antivary f g) :
  ∑ i, f i • g i ≤ ∑ i, f (σ i) • g i :=
(hfg.antivary_on _).sum_smul_le_sum_comp_perm_smul $ λ i _, mem_univ _

end smul

/-!
### Multiplication versions

Special cases of the above when scalar multiplication is actually multiplication.
-/

section mul
variables [linear_ordered_ring α] {s : finset ι} {σ : perm ι} {f g : ι → α}

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` vary together. Stated by permuting the entries of `g`.  -/
lemma monovary_on.sum_mul_comp_perm_le_sum_mul (hfg : monovary_on f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i * g (σ i) ≤ ∑ i in s, f i * g i :=
hfg.sum_smul_comp_perm_le_sum_smul hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` vary together. Stated by permuting the entries of `f`. -/
lemma monovary_on.sum_comp_perm_mul_le_sum_mul (hfg : monovary_on f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f (σ i) * g i ≤ ∑ i in s, f i * g i :=
hfg.sum_comp_perm_smul_le_sum_smul hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `g`.-/
lemma antivary_on.sum_mul_le_sum_mul_comp_perm (hfg : antivary_on f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i * g i ≤ ∑ i in s, f i * g (σ i) :=
hfg.sum_smul_le_sum_smul_comp_perm hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `f`. -/
lemma antivary_on.sum_mul_le_sum_comp_perm_mul (hfg : antivary_on f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i * g i ≤ ∑ i in s, f (σ i) * g i :=
hfg.sum_smul_le_sum_comp_perm_smul hσ

variables [fintype ι]

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` vary together. Stated by permuting the entries of `g`.  -/
lemma monovary.sum_mul_comp_perm_le_sum_mul (hfg : monovary f g) :
  ∑ i, f i * g (σ i) ≤ ∑ i, f i * g i :=
hfg.sum_smul_comp_perm_le_sum_smul

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` vary together. Stated by permuting the entries of `f`. -/
lemma monovary.sum_comp_perm_mul_le_sum_mul (hfg : monovary f g) :
  ∑ i, f (σ i) * g i ≤ ∑ i, f i * g i :=
hfg.sum_comp_perm_smul_le_sum_smul

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `g`.-/
lemma antivary.sum_mul_le_sum_mul_comp_perm (hfg : antivary f g) :
  ∑ i, f i * g i ≤ ∑ i, f i * g (σ i) :=
hfg.sum_smul_le_sum_smul_comp_perm

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `f`. -/
lemma antivary.sum_mul_le_sum_comp_perm_mul (hfg : antivary f g) :
  ∑ i, f i * g i ≤ ∑ i, f (σ i) * g i :=
hfg.sum_smul_le_sum_comp_perm_smul

end mul

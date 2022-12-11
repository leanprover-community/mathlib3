/-
Copyright (c) 2022 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import algebra.big_operators.order
import algebra.module.big_operators
import algebra.order.rearrangement
import group_theory.perm.cycle.concrete
import tactic.interval_cases

/-!
# Chebyshev's sum inequality

This file proves the Chebyshev sum inequality.

Chebyshev's inequality states `(∑ i in s, f i) * ∑ i in s, g i ≤ s.card * ∑ i in s, f i * g i` when
`f g : ι → α` monovary, and the reverse inequality when `f` and `g` antivary.

## Implementation notes

In fact, we don't need much compatibility between the addition and multiplication of `α`, so we can
actually decouple them by replacing multiplication with scalar multiplication and making `f` and `g`
land in different types.
As a bonus, this makes the dual statement trivial. The multiplication versions are provided for
convenience.

The case for `monotone`/`antitone` pairs of functions over a `linear_order` is not deduced in this
file because it is easily deducible from the `monovary` API.
-/

section
variables {α : Type*} [add_group α] [linear_order α] {a b : α}

lemma abs_lt' : |a| < b ↔ - a < b ∧ a < b := max_lt_iff.trans and.comm

end

namespace nat
variables {a b m : ℕ}

lemma modeq.eq_of_lt_of_lt (h : a ≡ b [MOD m]) (ha : a < m) (hb : b < m) : a = b :=
h.eq_of_modeq_of_abs_lt $ abs_sub_lt_iff.2
  ⟨(sub_le_self _ $ int.coe_nat_nonneg _).trans_lt $ cast_lt.2 hb,
   (sub_le_self _ $ int.coe_nat_nonneg _).trans_lt $ cast_lt.2 ha⟩

end nat

namespace cardinal
open_locale cardinal

lemma mk_eq_aleph_0 (α : Type*) [countable α] [infinite α] : #α = ℵ₀ :=
mk_le_aleph_0.antisymm $ aleph_0_le_mk _

end cardinal

section
universes u v
variables {α : Type u} {β : Type v}

instance nonempty_equiv_of_countable [countable α] [infinite α] [countable β] [infinite β] :
  nonempty (α ≃ β) :=
(cardinal.eq.1 $ by simp_rw cardinal.mk_eq_aleph_0).map $
  λ e : ulift.{v} α ≃ ulift.{u} β, equiv.ulift.symm.trans $ e.trans equiv.ulift

end

namespace prod
variables {α β : Type*} {a a₁ a₂ : α} {b b₁ b₂ : β}

lemma mk_inj_left : (a, b₁) = (a, b₂) ↔ b₁ = b₂ := (mk.inj_left _).eq_iff
lemma mk_inj_right : (a₁, b) = (a₂, b) ↔ a₁ = a₂ := (mk.inj_right _).eq_iff

end prod

namespace list
variables {α : Type*} [decidable_eq α] {l : list α}

lemma nodup.is_cycle_on_form_perm (h : l.nodup) : l.form_perm.is_cycle_on {a | a ∈ l} :=
begin
  refine ⟨l.form_perm.bij_on (λ _, form_perm_mem_iff_mem), λ a ha b hb, _⟩,
  rw [set.mem_set_of, ←index_of_lt_length] at ha hb,
  rw [←index_of_nth_le ha, ←index_of_nth_le hb],
  refine ⟨l.index_of b - l.index_of a, _⟩,
  simp only [sub_eq_neg_add, zpow_add, zpow_neg, equiv.perm.inv_eq_iff_eq, zpow_coe_nat,
    equiv.perm.coe_mul, form_perm_pow_apply_nth_le _ h],
  rw add_comm,
end

end list

namespace int
open equiv

lemma add_left_one_is_cycle : (equiv.add_left 1 : perm ℤ).is_cycle :=
⟨0, one_ne_zero, λ n _, ⟨n, by simp [←add_left_zsmul]⟩⟩

lemma add_right_one_is_cycle : (equiv.add_right 1 : perm ℤ).is_cycle :=
⟨0, one_ne_zero, λ n _, ⟨n, by simp [←add_right_zsmul]⟩⟩

end int

namespace set
open equiv
variables {α : Type*} {σ : perm α} {s : set α} {a : α}

--TODO: Fix `set.finite_or_infinite`
lemma finite_or_infinite' (s : set α) : s.finite ∨ s.infinite := finite_or_infinite

lemma prod_self_eq_Union_perm (hσ : σ.is_cycle_on s) :
  s ×ˢ s = ⋃ n : ℤ, (λ a, (a, (σ ^ n) a)) '' s :=
begin
  ext ⟨a, b⟩,
  simp only [mem_prod, mem_Union, mem_image],
  refine ⟨λ hx, _, _⟩,
  { obtain ⟨n, rfl⟩ := hσ.2 hx.1 hx.2,
    exact ⟨_, _, hx.1, rfl⟩ },
  { rintro ⟨n, a, ha, ⟨⟩⟩,
    exact ⟨ha, (hσ.1.zpow _).maps_to ha⟩ }
end

lemma countable.exists_cycle_on (hs : s.countable) :
  ∃ f : equiv.perm α, f.is_cycle_on s ∧ {x | f x ≠ x} ⊆ s :=
begin
  classical,
  obtain hs' | hs' := s.finite_or_infinite',
  { refine ⟨hs'.to_finset.to_list.form_perm, _,
      λ x hx, by simpa using list.mem_of_form_perm_apply_ne _ _ hx⟩,
    convert hs'.to_finset.nodup_to_list.is_cycle_on_form_perm,
    simp },
  haveI := hs.to_subtype,
  haveI := hs'.to_subtype,
  obtain ⟨f⟩ : nonempty (ℤ ≃ s) := infer_instance,
  refine ⟨(equiv.add_right 1).extend_domain f, _, λ x hx, of_not_not $ λ h, hx $
    perm.extend_domain_apply_not_subtype _ _ h⟩,
  convert int.add_right_one_is_cycle.is_cycle_on.extend_domain _,
  rw [image_comp, equiv.image_eq_preimage],
  ext,
  simp,
end

end set

namespace finset
open equiv
variables {α : Type*} {σ : equiv.perm α} {s : finset α} {a : α}

lemma product_self_eq_disj_Union_perm_aux (hσ : σ.is_cycle_on s) :
  (range s.card : set ℕ).pairwise_disjoint
    (λ k, s.map ⟨λ i, (i, (σ ^ k) i), λ i j, congr_arg prod.fst⟩) :=
begin
  obtain hs | hs := (s : set α).subsingleton_or_nontrivial,
  { refine set.subsingleton.pairwise _ _,
    simp_rw [set.subsingleton, mem_coe, ←card_le_one] at ⊢ hs,
    rwa card_range },
  classical,
  rintro m hm n hn hmn,
  simp only [disjoint_left, function.on_fun, mem_map, function.embedding.coe_fn_mk, exists_prop,
    not_exists, not_and, forall_exists_index, and_imp, prod.forall, prod.mk.inj_iff],
  rintro _ _ _ - rfl rfl a ha rfl h,
  rw [hσ.pow_apply_eq_pow_apply ha] at h,
  rw [mem_coe, mem_range] at hm hn,
  exact hmn.symm (h.eq_of_lt_of_lt hn hm),
end

/--
We can partition the square `s ×ˢ s` with diagonals as such:
```
01234
40123
34012
23401
12340
```
-/
lemma product_self_eq_disj_Union_perm (hσ : σ.is_cycle_on s) :
  s ×ˢ s =
    (range s.card).disj_Union (λ k, s.map ⟨λ i, (i, (σ ^ k) i), λ i j, congr_arg prod.fst⟩)
      (product_self_eq_disj_Union_perm_aux hσ) :=
begin
  ext ⟨a, b⟩,
  simp only [mem_product, equiv.perm.coe_pow, mem_disj_Union, mem_range, mem_map,
    function.embedding.coe_fn_mk, prod.mk.inj_iff, exists_prop],
  refine ⟨λ hx, _, _⟩,
  { obtain ⟨n, hn, rfl⟩ := hσ.exists_pow_eq hx.1 hx.2,
    exact ⟨n, hn, a, hx.1, rfl, rfl⟩ },
  { rintro ⟨n, -, a, ha, rfl, rfl⟩,
    exact ⟨ha, (hσ.1.pow _).maps_to ha⟩ }
end

end finset

namespace finset
open equiv
open_locale big_operators
variables {ι α β : Type*} [semiring α] [add_comm_monoid β] [module α β]
  {s : finset ι} {σ : equiv.perm ι} {f : ι → α} {g : ι → β}

lemma sum_smul_sum_eq_sum_perm (hσ : σ.is_cycle_on s) (f : ι → α) (g : ι → β) :
  (∑ i in s, f i) • ∑ i in s, g i = ∑ k in range s.card, ∑ i in s, f i • g ((σ ^ k) i) :=
by { simp_rw [sum_smul_sum, product_self_eq_disj_Union_perm hσ, sum_disj_Union, sum_map], refl }

end finset

namespace finset
open equiv
open_locale big_operators
variables {ι α : Type*} [semiring α] {s : finset ι} {σ : equiv.perm ι}

lemma sum_mul_sum_eq_sum_perm (hσ : σ.is_cycle_on s) (f g : ι → α) :
  (∑ i in s, f i) * ∑ i in s, g i = ∑ k in range s.card, ∑ i in s, f i * g ((σ ^ k) i) :=
sum_smul_sum_eq_sum_perm hσ f g

end finset

open equiv equiv.perm finset function order_dual
open_locale big_operators

variables {ι α β : Type*}

/-! ### Scalar multiplication versions -/

section smul
variables [linear_ordered_ring α] [linear_ordered_add_comm_group β] [module α β]
  [ordered_smul α β] {s : finset ι} {σ : perm ι} {f : ι → α} {g : ι → β}

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together, the scalar product of their
sum is less than the size of the set times their scalar product. -/
lemma monovary_on.sum_smul_sum_le_card_smul_sum (hfg : monovary_on f g s) :
  (∑ i in s, f i) • ∑ i in s, g i ≤ s.card • ∑ i in s, f i • g i :=
begin
  classical,
  obtain ⟨σ, hσ, hs⟩ := s.countable_to_set.exists_cycle_on,
  rw [←card_range s.card, sum_smul_sum_eq_sum_perm hσ],
  exact sum_le_card_nsmul _ _ _ (λ n _, hfg.sum_smul_comp_perm_le_sum_smul $ λ x hx, hs $ λ h, hx $
    is_fixed_pt.pow h _),
end

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together, the scalar product of their
sum is less than the size of the set times their scalar product. -/
lemma antivary_on.card_smul_sum_le_sum_smul_sum (hfg : antivary_on f g s) :
  s.card • ∑ i in s, f i • g i ≤ (∑ i in s, f i) • ∑ i in s, g i :=
by convert hfg.dual_right.sum_smul_sum_le_card_smul_sum

variables [fintype ι]

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together, the scalar product of their
sum is less than the size of the set times their scalar product. -/
lemma monovary.sum_smul_sum_le_card_smul_sum (hfg : monovary f g) :
  (∑ i, f i) • ∑ i, g i ≤ fintype.card ι • ∑ i, f i • g i :=
(hfg.monovary_on _).sum_smul_sum_le_card_smul_sum

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together, the scalar product of their
sum is less than the size of the set times their scalar product. -/
lemma antivary.card_smul_sum_le_sum_smul_sum (hfg : antivary f g) :
  fintype.card ι • ∑ i, f i • g i ≤ (∑ i, f i) • ∑ i, g i :=
by convert (hfg.dual_right.monovary_on _).sum_smul_sum_le_card_smul_sum

end smul

/-!
### Multiplication versions

Special cases of the above when scalar multiplication is actually multiplication.
-/

section mul
variables [linear_ordered_ring α] {s : finset ι} {σ : perm ι} {f g : ι → α}

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together, the product of their sum is
less than the size of the set times their scalar product. -/
lemma monovary_on.sum_mul_sum_le_card_mul_sum (hfg : monovary_on f g s) :
  (∑ i in s, f i) * ∑ i in s, g i ≤ s.card * ∑ i in s, f i * g i :=
by { rw ←nsmul_eq_mul, exact hfg.sum_smul_sum_le_card_smul_sum }

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together, the product of their sum is
greater than the size of the set times their scalar product. -/
lemma antivary_on.card_mul_sum_le_sum_mul_sum (hfg : antivary_on f g s) :
  (s.card : α) * ∑ i in s, f i * g i ≤ (∑ i in s, f i) * ∑ i in s, g i :=
by { rw ←nsmul_eq_mul, exact hfg.card_smul_sum_le_sum_smul_sum }

/-- **Chebyshev's Sum Inequality**: The square of the sum is less than the size of the set times the
sum of the squares. -/
lemma sq_sum_le_card_mul_sum_sq : (∑ i in s, f i)^2 ≤ s.card * ∑ i in s, f i ^ 2 :=
by { simp_rw sq, exact (monovary_on_self _ _).sum_mul_sum_le_card_mul_sum }

variables [fintype ι]

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together, the product of their sum is
less than the size of the set times their scalar product. -/
lemma monovary.sum_mul_sum_le_card_mul_sum (hfg : monovary f g) :
  (∑ i, f i) * ∑ i, g i ≤ fintype.card ι * ∑ i, f i * g i :=
(hfg.monovary_on _).sum_mul_sum_le_card_mul_sum

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together, the product of their sum is
less than the size of the set times their scalar product. -/
lemma antivary.card_mul_sum_le_sum_mul_sum (hfg : antivary f g) :
  (fintype.card ι : α) * ∑ i, f i * g i ≤ (∑ i, f i) * ∑ i, g i :=
(hfg.antivary_on _).card_mul_sum_le_sum_mul_sum

end mul

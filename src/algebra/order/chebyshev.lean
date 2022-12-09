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

instance nonempty_equiv_of_countable {α β : Type*} [countable α] [infinite α] [countable β]
  [infinite β] : nonempty (α ≃ β) := sorry

namespace prod
variables {α β : Type*} {a a₁ a₂ : α} {b b₁ b₂ : β}

lemma mk_inj_left : (a, b₁) = (a, b₂) ↔ b₁ = b₂ := (mk.inj_left _).eq_iff
lemma mk_inj_right : (a₁, b) = (a₂, b) ↔ a₁ = a₂ := (mk.inj_right _).eq_iff

end prod

namespace equiv
variables {α β : Type*} (f : α ≃ β) {s : set α} {t : set β}

protected lemma bij_on' (h₁ : set.maps_to f s t) (h₂ : set.maps_to f.symm t s) : set.bij_on f s t :=
⟨h₁, f.injective.inj_on _, λ b hb, ⟨f.symm b, h₂ hb, apply_symm_apply _ _⟩⟩

protected lemma bij_on (h : ∀ a, f a ∈ t ↔ a ∈ s) : set.bij_on f s t :=
f.bij_on' (λ a, (h _).2) $ λ b hb, (h _).1 $ by rwa apply_symm_apply

end equiv

namespace list
variables {α : Type*} [decidable_eq α] {l : list α}

lemma nodup.is_cycle_on_form_perm (h : l.nodup) : l.form_perm.is_cycle_on {a | a ∈ l} :=
begin
  refine ⟨(l.form_perm).bij_on (λ _, form_perm_mem_iff_mem), _⟩,
  refine λ a ha b hb, ⟨l.index_of b - l.index_of a, _⟩,

  refine ⟨l.index_of b - l.index_of a, _⟩,
  have := l.index_of a,
  refine λ _, form_perm_apply_mem_of_mem _ _,
end

end list

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

lemma countable.exists_cycle_on (hs : s.countable) : ∃ f : equiv.perm α, f.is_cycle_on s :=
begin
  obtain hs' | hs' := s.finite_or_infinite',
  {
    classical,
    refine ⟨hs'.to_finset.to_list.form_perm, _⟩,
    convert hs'.to_finset.nodup_to_list.is_cycle_on_form_perm,
    simp },
  haveI := hs.to_subtype,
  haveI := hs'.to_subtype,
  obtain ⟨f⟩ : nonempty (s ≃ ℤ) := infer_instance,
  set π : perm ι := s.to_list.form_perm with hπ,
  have hπc : π.is_cycle_on s,
  { convert s.nodup_to_list.is_cycle_on_form_perm,
    simp_rw [mem_to_list, set_of_mem] },
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
  rintro m hm n hn hmn,
  simp only [disjoint_left, function.on_fun, mem_map,
    function.embedding.coe_fn_mk, exists_prop, not_exists, not_and, forall_exists_index, and_imp,
    prod.forall, prod.mk.inj_iff],
  rintro _ _ _ - rfl rfl a ha rfl h,
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
  { obtain ⟨n, rfl⟩ := hσ.2 hx.1 hx.2,
    sorry
    -- refine ⟨_, _, _, hx.1, rfl, rfl⟩,
    },
  { rintro ⟨n, -, a, ha, rfl, rfl⟩,
    exact ⟨ha, (hσ.1.pow _).maps_to ha⟩ }
end

lemma exists_cycle_on (s : finset α) : ∃ f : equiv.perm α, f.is_cycle_on s :=
begin
  classical,
  refine ⟨s.to_list.form_perm, _⟩,
  convert s.nodup_to_list.is_cycle_on_form_perm,
  simp_rw [mem_to_list, set_of_mem],
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
  set π : perm ι := s.to_list.form_perm with hπ,
  have hπc : π.is_cycle_on s,
  { convert s.nodup_to_list.is_cycle_on_form_perm,
    simp_rw [mem_to_list, set_of_mem] },
  rw sum_smul_sum,
  rw sum_product,
  dsimp,
  -- rw sum_mul_sum_eq_sum_perm s π hπc hπs,
  -- have : ∑ (k : ℕ) in range s.card,
  -- ∑ (i : ι) in s, f i • g (((π ^ k).subtype_congr (equiv.refl _)) i) ≤
  --   ∑ (k : ℕ) in range s.card, ∑ (i : ι) in s, f i • g i,
  -- { refine finset.sum_le_sum (λ k hk, _),
  --   convert monovary_on.sum_smul_comp_perm_le_sum_smul hfg (λ x hx, _),
  --   contrapose! hx,
  --   simp only [set.mem_set_of_eq, not_not],
  --   rw equiv.perm.subtype_congr.right_apply,
  --   simp only [coe_refl, id.def, subtype.coe_mk],
  --   contrapose! hx,
  --   exact mem_coe.mpr hx },
  -- rwa [sum_const, card_range] at this,
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

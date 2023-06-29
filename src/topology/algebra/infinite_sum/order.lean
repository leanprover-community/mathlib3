/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import algebra.order.archimedean
-- import topology.algebra.infinite_sum.basic
import .basic
import topology.algebra.order.field
import topology.algebra.order.monotone_convergence

/-!
# Infinite sum in an order

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides lemmas about the interaction of infinite sums and order operations.
-/

open finset filter function
open_locale big_operators classical

variables {ι κ α : Type*}

section preorder
variables [preorder α] [topological_space α] [order_closed_topology α]
  [t2_space α] {f : ℕ → α} {c : α}

@[to_additive] variable [comm_monoid α] 

@[to_additive tsum_le_of_sum_range_le] 
lemma tprod_le_of_prod_range_le (hf : multipliable f) (h : ∀ n, ∏ i in range n, f i ≤ c) :
  ∏' n, f n ≤ c :=
let ⟨l, hl⟩ := hf in hl.tprod_eq.symm ▸ le_of_tendsto' hl.tendsto_sum_nat h

end preorder

section ordered_comm_monoid
@[to_additive] variables [ordered_comm_monoid α] 
variables [topological_space α] [order_closed_topology α] {f g : ι → α}
  {a a₁ a₂ : α}

@[to_additive]
lemma has_prod_le (h : ∀ i, f i ≤ g i) (hf : has_prod f a₁) (hg : has_prod g a₂) : a₁ ≤ a₂ :=
le_of_tendsto_of_tendsto' hf hg $ λ s, prod_le_prod' $ λ i _, h i

@[to_additive, mono]
lemma has_prod_mono (hf : has_prod f a₁) (hg : has_prod g a₂) (h : f ≤ g) : a₁ ≤ a₂ :=
has_prod_le h hf hg

@[to_additive]
lemma has_prod_le_of_prod_le (hf : has_prod f a) (h : ∀ s, ∏ i in s, f i ≤ a₂) : a ≤ a₂ :=
le_of_tendsto' hf h

@[to_additive]
lemma le_has_prod_of_le_prod (hf : has_prod f a) (h : ∀ s, a₂ ≤ ∏ i in s, f i) : a₂ ≤ a :=
ge_of_tendsto' hf h

@[to_additive]
lemma has_prod_le_inj {g : κ → α} (e : ι → κ) (he : injective e) (hs : ∀ c ∉ set.range e, 1 ≤ g c)
  (h : ∀ i, f i ≤ g (e i)) (hf : has_prod f a₁) (hg : has_prod g a₂) : a₁ ≤ a₂ :=
have has_prod (λ c, (partial_inv e c).cases_on' 1 f) a₁,
begin
  refine (has_prod_iff_has_prod_of_ne_one_bij (e ∘ coe) (λ c₁ c₂ hc, he hc) (λ c hc, _) _).2 hf,
  { rw mem_mul_support at hc,
    cases eq : partial_inv e c with i; rw eq at hc,
    { contradiction },
    { rw [partial_inv_of_injective he] at eq,
      exact ⟨⟨i, hc⟩, eq⟩ } },
  { rintro c,
    simp [partial_inv_left he, option.cases_on'] }
end,
begin
  refine has_prod_le (λ c, _) this hg,
  obtain ⟨i, rfl⟩ | h := em (c ∈ set.range e),
  { rw [partial_inv_left he, option.cases_on'],
    exact h _ },
  { have : partial_inv e c = none := dif_neg h,
    rw [this, option.cases_on'],
    exact hs _ h }
end

@[to_additive tsum_le_tsum_of_inj]
lemma tprod_le_tprod_of_inj {g : κ → α} (e : ι → κ) (he : injective e)
  (hs : ∀ c ∉ set.range e, 1 ≤ g c) (h : ∀ i, f i ≤ g (e i)) 
  (hf : multipliable f) (hg : multipliable g) : tprod f ≤ tprod g :=
has_prod_le_inj _ he hs h hf.has_prod hg.has_prod

@[to_additive]
lemma prod_le_has_prod (s : finset ι) (hs : ∀ i ∉ s, 1 ≤ f i) (hf : has_prod f a) :
  ∏ i in s, f i ≤ a :=
ge_of_tendsto hf (eventually_at_top.2 ⟨s, λ t hst,
  prod_le_prod_of_subset_of_one_le' hst $ λ i hbt hbs, hs i hbs⟩)

@[to_additive]
lemma is_lub_has_prod (h : ∀ i, 1 ≤ f i) (hf : has_prod f a) :
  is_lub (set.range $ λ s, ∏ i in s, f i) a :=
is_lub_of_tendsto_at_top (finset.prod_mono_set_of_one_le' h) hf

@[to_additive]
lemma le_has_prod (hf : has_prod f a) (i : ι) (hb : ∀ b' ≠ i, 1 ≤ f b') : f i ≤ a :=
calc f i = ∏ i in {i}, f i : finset.prod_singleton.symm
... ≤ a : prod_le_has_prod _ (by { convert hb, simp }) hf

@[to_additive sum_le_tsum]
lemma prod_le_tprod {f : ι → α} (s : finset ι) (hs : ∀ i ∉ s, 1 ≤ f i) (hf : multipliable f) :
  ∏ i in s, f i ≤ ∏' i, f i :=
prod_le_has_prod s hs hf.has_prod

@[to_additive le_tsum]
lemma le_tprod (hf : multipliable f) (i : ι) (hb : ∀ b' ≠ i, 1 ≤ f b') : f i ≤ ∏' i, f i :=
le_has_prod (multipliable.has_prod hf) i hb

@[to_additive tsum_le_tsum]
lemma tprod_le_tprod (h : ∀ i, f i ≤ g i) (hf : multipliable f) (hg : multipliable g) :
  ∏' i, f i ≤ ∏' i, g i :=
has_prod_le h hf.has_prod hg.has_prod

@[to_additive tsum_mono, mono] 
lemma tprod_mono (hf : multipliable f) (hg : multipliable g) (h : f ≤ g) : 
  ∏' n, f n ≤ ∏' n, g n :=
tprod_le_tprod h hf hg

@[to_additive tsum_le_of_sum_le]
lemma tprod_le_of_prod_le (hf : multipliable f) (h : ∀ s, ∏ i in s, f i ≤ a₂) : ∏' i, f i ≤ a₂ :=
has_prod_le_of_prod_le hf.has_prod h

@[to_additive tsum_le_of_sum_le]
lemma tprod_le_of_prod_le' (ha₂ : 1 ≤ a₂) (h : ∀ s, ∏ i in s, f i ≤ a₂) : ∏' i, f i ≤ a₂ :=
begin
  by_cases hf : multipliable f,
  { exact tprod_le_of_prod_le hf h },
  { rw tprod_eq_one_of_not_multipliable hf,
    exact ha₂ }
end

@[to_additive has_sum.nonneg]
lemma has_prod.one_le (h : ∀ i, 1 ≤ g i) (ha : has_prod g a) : 1 ≤ a := 
has_prod_le h has_prod_one ha

@[to_additive has_sum.nonpos]
lemma has_prod.le_one (h : ∀ i, g i ≤ 1) (ha : has_prod g a) : a ≤ 1 := 
has_prod_le h ha has_prod_one

@[to_additive]
lemma tprod_one_le (h : ∀ i, 1 ≤ g i) : 1 ≤ ∏' i, g i :=
begin
  by_cases hg : multipliable g,
  { exact hg.has_prod.one_le h },
  { simp [tprod_eq_one_of_not_multipliable hg] }
end

@[to_additive tsum_nonpos]
lemma tprod_le_one (h : ∀ i, f i ≤ 1) : ∏' i, f i ≤ 1 :=
begin
  by_cases hf : multipliable f,
  { exact hf.has_prod.le_one h },
  { simp [tprod_eq_one_of_not_multipliable hf] }
end

end ordered_comm_monoid

section ordered_comm_group


variables   
  
@[to_additive] variables [ordered_comm_group α] [topological_space α] [topological_group α]  [order_closed_topology α] 

variables {f g : ι → α} {a₁ a₂ : α} {i : ι}

@[to_additive]
lemma has_prod_lt (h : f ≤ g) (hi : f i < g i) (hf : has_prod f a₁) (hg : has_prod g a₂) : a₁ < a₂ :=
have update f i 1 ≤ update g i 1 := update_le_update_iff.mpr ⟨rfl.le, λ i _, h i⟩,
have 1 / f i * a₁ ≤ 1 / g i * a₂ := has_prod_le this (hf.update i 1) (hg.update i 1),
by simpa only [one_div, mul_inv_cancel_left] using mul_lt_mul_of_lt_of_le hi this

@[to_additive, mono] 
lemma has_prod_strict_mono (hf : has_prod f a₁) (hg : has_prod g a₂) (h : f < g) : a₁ < a₂ :=
let ⟨hle, i, hi⟩ := pi.lt_def.mp h in has_prod_lt hle hi hf hg

@[to_additive tsum_lt_tsum]
lemma tprod_lt_tprod (h : f ≤ g) (hi : f i < g i) (hf : multipliable f) (hg : multipliable g) :
  ∏' n, f n < ∏' n, g n :=
has_prod_lt h hi hf.has_prod hg.has_prod

@[to_additive tsum_strict_mono, mono] 
lemma tprod_strict_mono (hf : multipliable f) (hg : multipliable g) (h : f < g) :
  ∏' n, f n < ∏' n, g n :=
let ⟨hle, i, hi⟩ := pi.lt_def.mp h in tprod_lt_tprod hle hi hf hg

@[to_additive tsum_one_lt]
lemma tprod_pos (hprod : multipliable g) (hg : ∀ i, 1 ≤ g i) (i : ι) (hi : 1 < g i) : 
  1 < ∏' i, g i :=
by { rw ←tprod_one, exact tprod_lt_tprod hg hi multipliable_one hprod }

@[to_additive]
lemma has_prod_one_iff_of_one_le (hf : ∀ i, 1 ≤ f i) : has_prod f 1 ↔ f = 1 :=
begin
  refine ⟨λ hf', _, _⟩,
  { ext i,
    refine (hf i).eq_of_not_gt (λ hi, _),
    simpa using has_prod_lt hf hi has_prod_one hf' },
  { rintro rfl,
    exact has_prod_one }
end

end ordered_comm_group

section canonically_ordered_monoid
@[to_additive] variables [canonically_ordered_monoid α] 
variables [topological_space α] [order_closed_topology α] {f : ι → α} {a : α}

@[to_additive]
lemma le_has_prod' (hf : has_prod f a) (i : ι) : f i ≤ a := le_has_prod hf i $ λ _ _, one_le _

@[to_additive le_tsum']
lemma le_tprod' (hf : multipliable f) (i : ι) : f i ≤ ∏' i, f i := le_tprod hf i $ λ _ _, one_le _

@[to_additive]
lemma has_prod_one_iff : has_prod f 1 ↔ ∀ x, f x = 1 :=
begin
  refine ⟨_, λ h, _⟩,
  { contrapose!,
    exact λ ⟨x, hx⟩ h, hx (le_one_iff_eq_one.1$ le_has_prod' h x) },
  { convert has_prod_one,
    exact funext h }
end

@[to_additive tsum_eq_one_iff]
lemma tprod_eq_one_iff (hf : multipliable f) : ∏' i, f i = 1 ↔ ∀ x, f x = 1 :=
by rw [←has_prod_one_iff, hf.has_prod_iff]

@[to_additive tsum_ne_zero_iff]
lemma tprod_ne_one_iff (hf : multipliable f) : ∏' i, f i ≠ 1 ↔ ∃ x, f x ≠ 1 :=
by rw [ne.def, tprod_eq_one_iff hf, not_forall]

@[to_additive]
lemma is_lub_has_prod' (hf : has_prod f a) : is_lub (set.range $ λ s, ∏ i in s, f i) a :=
is_lub_of_tendsto_at_top (finset.prod_mono_set' f) hf

end canonically_ordered_monoid

section linear_order

/-!
For infinite prods taking values in a linearly ordered monoid, the existence of a least upper
bound for the finite prods is a criterion for prodmability.

This criterion is useful when applied in a linearly ordered monoid which is also a complete or
conditionally complete linear order, such as `ℝ`, `ℝ≥0`, `ℝ≥0∞`, because it is then easy to check
the existence of a least upper bound.
-/

@[to_additive]
lemma has_prod_of_is_lub_of_one_le [linear_ordered_comm_monoid α] [topological_space α]
  [order_topology α] {f : ι → α} (i : α) (h : ∀ i, 1 ≤ f i)
  (hf : is_lub (set.range $ λ s, ∏ i in s, f i) i) :
  has_prod f i :=
tendsto_at_top_is_lub (finset.prod_mono_set_of_one_le' h) hf

@[to_additive]
lemma has_prod_of_is_lub [canonically_linear_ordered_monoid α] [topological_space α]
   [order_topology α] {f : ι → α} (b : α) (hf : is_lub (set.range $ λ s, ∏ i in s, f i) b) :
  has_prod f b :=
tendsto_at_top_is_lub (finset.prod_mono_set' f) hf

-- No has_abs.abs in the mul case

lemma summable_abs_iff [linear_ordered_add_comm_group α] [uniform_space α] [uniform_add_group α]
  [complete_space α] {f : ι → α} :
  summable (λ x, |f x|) ↔ summable f :=
have h1 : ∀ x : {x | 0 ≤ f x}, |f x| = f x := λ x, abs_of_nonneg x.2,
have h2 : ∀ x : {x | 0 ≤ f x}ᶜ, |f x| = -f x := λ x, abs_of_neg (not_le.1 x.2),
calc summable (λ x, |f x|) ↔
  summable (λ x : {x | 0 ≤ f x}, |f x|) ∧ summable (λ x : {x | 0 ≤ f x}ᶜ, |f x|) :
  summable_subtype_and_compl.symm
... ↔ summable (λ x : {x | 0 ≤ f x}, f x) ∧ summable (λ x : {x | 0 ≤ f x}ᶜ, -f x) :
  by simp only [h1, h2]
... ↔ _ : by simp only [summable_neg_iff, summable_subtype_and_compl]

alias summable_abs_iff ↔ summable.of_abs summable.abs

--TODO: Change the conclusion to `finite ι`
lemma finite_of_summable_const [linear_ordered_add_comm_group α] [topological_space α]
  [archimedean α] [order_closed_topology α] {b : α} (hb : 0 < b) (hf : summable (λ i : ι, b)) :
  (set.univ : set ι).finite :=
begin
  have H : ∀ s : finset ι, s.card • b ≤ ∑' i : ι, b,
  { intros s,
    simpa using sum_le_has_sum s (λ a ha, hb.le) hf.has_sum },
  obtain ⟨n, hn⟩ := archimedean.arch (∑' i : ι, b) hb,
  have : ∀ s : finset ι, s.card ≤ n,
  { intros s,
    simpa [nsmul_le_nsmul_iff hb] using (H s).trans hn },
  haveI : fintype ι := fintype_of_finset_card_le n this,
  exact set.finite_univ
end

end linear_order

lemma summable.tendsto_top_of_pos [linear_ordered_field α] [topological_space α] [order_topology α]
  {f : ℕ → α} (hf : summable f⁻¹) (hf' : ∀ n, 0 < f n) : tendsto f at_top at_top :=
begin
  rw ←inv_inv f,
  apply filter.tendsto.inv_tendsto_zero,
  apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
    (summable.tendsto_at_top_zero hf),
  rw eventually_iff_exists_mem,
  refine ⟨set.Ioi 0, Ioi_mem_at_top _, λ _ _, _⟩,
  rw [set.mem_Ioi, inv_eq_one_div, one_div, pi.inv_apply, _root_.inv_pos],
  exact hf' _,
end
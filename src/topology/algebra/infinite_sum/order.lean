/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import algebra.order.archimedean
import topology.algebra.infinite_sum.basic
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
variables [preorder α] [comm_monoid α] [topological_space α] [order_closed_topology α]
  [t2_space α] {f : ℕ → α} {c : α}

@[to_additive] lemma tprod_le_of_prod_range_le (hprod : prodable f)
  (h : ∀ n, ∏ i in finset.range n, f i ≤ c) : ∏' n, f n ≤ c :=
let ⟨l, hl⟩ := hprod in hl.tprod_eq.symm ▸ le_of_tendsto' hl.tendsto_prod_nat h

end preorder

section ordered_comm_monoid
variables [ordered_comm_monoid α] [topological_space α] [order_closed_topology α] {f g : ι → α}
  {a a₁ a₂ : α}

@[to_additive]
lemma has_prod_le (h : ∀ i, f i ≤ g i) (hf : has_prod f a₁) (hg : has_prod g a₂) : a₁ ≤ a₂ :=
le_of_tendsto_of_tendsto' hf hg $ λ s, finset.prod_le_prod'' $ λ b _, h b

@[to_additive]
lemma has_prod_mono (hf : has_prod f a₁) (hg : has_prod g a₂) (h : f ≤ g) : a₁ ≤ a₂ :=
has_prod_le h hf hg

attribute [mono] has_prod_mono has_sum_mono

@[to_additive] lemma has_prod_le_of_prod_le (hf : has_prod f a) (h : ∀ s, ∏ i in s, f i ≤ a₂) :
  a ≤ a₂ :=
le_of_tendsto' hf h

@[to_additive] lemma le_has_prod_of_le_prod (hf : has_prod f a) (h : ∀ s, a₂ ≤ ∏ i in s, f i) :
  a₂ ≤ a :=
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

@[to_additive] lemma tprod_le_tprod_of_inj {g : κ → α} (e : ι → κ) (he : injective e)
  (hs : ∀ c ∉ set.range e, 1 ≤ g c) (h : ∀ i, f i ≤ g (e i)) (hf : prodable f) (hg : prodable g) :
  tprod f ≤ tprod g :=
has_prod_le_inj _ he hs h hf.has_prod hg.has_prod

@[to_additive] lemma prod_le_has_prod (s : finset ι) (hs : ∀ i ∉ s, 1 ≤ f i) (hf : has_prod f a) :
  ∏ i in s, f i ≤ a :=
ge_of_tendsto hf $ eventually_at_top.2 ⟨s, λ t hst,
  prod_le_prod_of_subset_of_one_le' hst $ λ i hit, hs _⟩

@[to_additive] lemma is_lub_has_prod (h : ∀ i, 1 ≤ f i) (hf : has_prod f a) :
  is_lub (set.range (λ s, ∏ i in s, f i)) a :=
is_lub_of_tendsto_at_top (prod_mono_set_of_one_le' h) hf

@[to_additive] lemma le_has_prod (hf : has_prod f a) (i : ι) (hi : ∀ i' ≠ i, 1 ≤ f i') : f i ≤ a :=
calc f i = ∏ i in {i}, f i : finset.prod_singleton.symm
... ≤ a : prod_le_has_prod _ (by { convert hi, simp }) hf

@[to_additive]
lemma prod_le_tprod {f : ι → α} (s : finset ι) (hs : ∀ i ∉ s, 1 ≤ f i) (hf : prodable f) :
  ∏ i in s, f i ≤ ∏' i, f i :=
prod_le_has_prod s hs hf.has_prod

@[to_additive] lemma le_tprod (hf : prodable f) (i : ι) (hi : ∀ i' ≠ i, 1 ≤ f i') :
  f i ≤ ∏' i, f i :=
le_has_prod (prodable.has_prod hf) i hi

@[to_additive] lemma tprod_le_tprod (h : ∀ i, f i ≤ g i) (hf : prodable f) (hg : prodable g) :
  ∏' i, f i ≤ ∏' i, g i :=
has_prod_le h hf.has_prod hg.has_prod

@[to_additive] lemma tprod_mono (hf : prodable f) (hg : prodable g) (h : f ≤ g) :
  ∏' n, f n ≤ ∏' n, g n :=
tprod_le_tprod h hf hg

attribute [mono] tprod_mono tsum_mono

@[to_additive] lemma tprod_le_of_prod_le (hf : prodable f) (h : ∀ s, ∏ i in s, f i ≤ a₂) :
  ∏' i, f i ≤ a₂ :=
has_prod_le_of_prod_le hf.has_prod h

@[to_additive] lemma tprod_le_of_prod_le' (ha₂ : 1 ≤ a₂) (h : ∀ s, ∏ i in s, f i ≤ a₂) :
  ∏' i, f i ≤ a₂ :=
begin
  by_cases hf : prodable f,
  { exact tprod_le_of_prod_le hf h },
  { rw tprod_eq_one_of_not_prodable hf,
    exact ha₂ }
end

@[to_additive] lemma has_prod.one_le (h : ∀ i, 1 ≤ g i) (ha : has_prod g a) : 1 ≤ a :=
has_prod_le h has_prod_one ha

@[to_additive] lemma has_prod.le_one (h : ∀ i, g i ≤ 1) (ha : has_prod g a) : a ≤ 1 :=
has_prod_le h ha has_prod_one

@[to_additive tsum_nonneg] lemma one_le_tprod (h : ∀ i, 1 ≤ g i) : 1 ≤ ∏' i, g i :=
begin
  by_cases hg : prodable g,
  { exact hg.has_prod.one_le h },
  { simp [tprod_eq_one_of_not_prodable hg] }
end

@[to_additive] lemma tprod_le_one (h : ∀ i, f i ≤ 1) : ∏' i, f i ≤ 1 :=
begin
  by_cases hf : prodable f,
  { exact hf.has_prod.le_one h },
  { simp [tprod_eq_one_of_not_prodable hf] }
end

end ordered_comm_monoid

section ordered_comm_group
variables [ordered_comm_group α] [topological_space α] [topological_group α]
  [order_closed_topology α] {f g : ι → α} {a₁ a₂ : α}

@[to_additive] lemma has_prod_lt {i : ι} (h : ∀ (i : ι), f i ≤ g i) (hi : f i < g i)
  (hf : has_prod f a₁) (hg : has_prod g a₂) :
  a₁ < a₂ :=
have update f i 1 ≤ update g i 1 := update_le_update_iff.mpr ⟨rfl.le, λ i _, h i⟩,
have 1 / f i * a₁ ≤ 1 / g i * a₂ := has_prod_le this (hf.update i 1) (hg.update i 1),
by simpa only [one_div, mul_inv_cancel_left] using mul_lt_mul_of_lt_of_le hi this

@[to_additive]
lemma has_prod_strict_mono (hf : has_prod f a₁) (hg : has_prod g a₂) (h : f < g) : a₁ < a₂ :=
let ⟨hle, i, hi⟩ := pi.lt_def.mp h in has_prod_lt hle hi hf hg

@[to_additive] lemma tprod_lt_tprod {i : ι} (h : ∀ (i : ι), f i ≤ g i) (hi : f i < g i)
  (hf : prodable f) (hg : prodable g) :
  ∏' n, f n < ∏' n, g n :=
has_prod_lt h hi hf.has_prod hg.has_prod

@[to_additive] lemma tprod_strict_mono (hf : prodable f) (hg : prodable g) (h : f < g) :
  ∏' n, f n < ∏' n, g n :=
let ⟨hle, i, hi⟩ := pi.lt_def.mp h in tprod_lt_tprod hle hi hf hg

attribute [mono] has_prod_strict_mono has_sum_strict_mono tprod_strict_mono tsum_strict_mono

@[to_additive tsum_pos]
lemma one_lt_tprod (hg' : prodable g) (hg : ∀ i, 1 ≤ g i) (i : ι) (hi : 1 < g i) : 1 < ∏' i, g i :=
by { rw ← tprod_one, exact tprod_lt_tprod hg hi prodable_one hg' }

@[to_additive] lemma has_prod_one_iff_of_one_le (hf : ∀ i, 1 ≤ f i) : has_prod f 1 ↔ f = 1 :=
begin
  refine ⟨λ hf', _, _⟩,
  { ext i,
    refine (hf i).eq_of_not_gt (λ hi, _),
    simpa using has_prod_lt hf hi has_prod_one hf' },
  { rintro rfl,
    exact has_prod_one },
end

end ordered_comm_group

section canonically_ordered_monoid
variables [canonically_ordered_monoid α] [topological_space α] [order_closed_topology α]
  {f : ι → α} {a : α}

@[to_additive] lemma le_has_prod' (hf : has_prod f a) (i : ι) : f i ≤ a :=
le_has_prod hf i $ λ _ _, one_le _

@[to_additive] lemma le_tprod' (hf : prodable f) (i : ι) : f i ≤ ∏' i, f i :=
le_tprod hf i $ λ _ _, one_le _

@[to_additive] lemma has_prod_one_iff : has_prod f 1 ↔ ∀ x, f x = 1 :=
begin
  refine ⟨_, λ h, _⟩,
  { contrapose!,
    exact λ ⟨x, hx⟩ h, hx (le_one_iff_eq_one.1 $ le_has_prod' h x) },
  { convert has_prod_one,
    exact funext h }
end

@[to_additive] lemma tprod_eq_one_iff (hf : prodable f) : ∏' i, f i = 1 ↔ ∀ x, f x = 1 :=
by rw [←has_prod_one_iff, hf.has_prod_iff]

@[to_additive] lemma tprod_ne_one_iff (hf : prodable f) : ∏' i, f i ≠ 1 ↔ ∃ x, f x ≠ 1 :=
by rw [ne.def, tprod_eq_one_iff hf, not_forall]

@[to_additive] lemma is_lub_has_prod' (hf : has_prod f a) :
  is_lub (set.range (λ s, ∏ i in s, f i)) a :=
is_lub_of_tendsto_at_top (finset.prod_mono_set' f) hf

end canonically_ordered_monoid

section linear_order

/-!
For infinite sums taking values in a linearly ordered monoid, the existence of a least upper
bound for the finite sums is a criterion for summability.

This criterion is useful when applied in a linearly ordered monoid which is also a complete or
conditionally complete linear order, such as `ℝ`, `ℝ≥0`, `ℝ≥0∞`, because it is then easy to check
the existence of a least upper bound.
-/

@[to_additive] lemma has_prod_of_is_lub_of_one_le [linear_ordered_comm_monoid α]
  [topological_space α] [order_topology α] {f : ι → α} (a : α) (h : ∀ i, 1 ≤ f i)
  (hf : is_lub (set.range $ λ s, ∏ i in s, f i) a) :
  has_prod f a :=
tendsto_at_top_is_lub (finset.prod_mono_set_of_one_le' h) hf

@[to_additive] lemma has_prod_of_is_lub [canonically_linear_ordered_monoid α] [topological_space α]
  [order_topology α] {f : ι → α} (a : α) (hf : is_lub (set.range (λ s, ∏ i in s, f i)) a) :
  has_prod f a :=
tendsto_at_top_is_lub (finset.prod_mono_set' f) hf

lemma summable_abs_iff [linear_ordered_add_comm_group α] [uniform_space α]
  [uniform_add_group α] [complete_space α] {f : ι → α} :
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

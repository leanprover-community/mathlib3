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
variables [preorder α] [add_comm_monoid α] [topological_space α] [order_closed_topology α]
  [t2_space α] {f : ℕ → α} {c : α}

lemma tsum_le_of_sum_range_le (hf : summable f) (h : ∀ n, ∑ i in range n, f i ≤ c) :
  ∑' n, f n ≤ c :=
let ⟨l, hl⟩ := hf in hl.tsum_eq.symm ▸ le_of_tendsto' hl.tendsto_sum_nat h

end preorder

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid α] [topological_space α] [order_closed_topology α] {f g : ι → α}
  {a a₁ a₂ : α}

lemma has_sum_le (h : ∀ i, f i ≤ g i) (hf : has_sum f a₁) (hg : has_sum g a₂) : a₁ ≤ a₂ :=
le_of_tendsto_of_tendsto' hf hg $ λ s, sum_le_sum $ λ i _, h i

@[mono] lemma has_sum_mono (hf : has_sum f a₁) (hg : has_sum g a₂) (h : f ≤ g) : a₁ ≤ a₂ :=
has_sum_le h hf hg

lemma has_sum_le_of_sum_le (hf : has_sum f a) (h : ∀ s, ∑ i in s, f i ≤ a₂) : a ≤ a₂ :=
le_of_tendsto' hf h

lemma le_has_sum_of_le_sum (hf : has_sum f a) (h : ∀ s, a₂ ≤ ∑ i in s, f i) : a₂ ≤ a :=
ge_of_tendsto' hf h

lemma has_sum_le_inj {g : κ → α} (e : ι → κ) (he : injective e) (hs : ∀ c ∉ set.range e, 0 ≤ g c)
  (h : ∀ i, f i ≤ g (e i)) (hf : has_sum f a₁) (hg : has_sum g a₂) : a₁ ≤ a₂ :=
have has_sum (λ c, (partial_inv e c).cases_on' 0 f) a₁,
begin
  refine (has_sum_iff_has_sum_of_ne_zero_bij (e ∘ coe) (λ c₁ c₂ hc, he hc) (λ c hc, _) _).2 hf,
  { rw mem_support at hc,
    cases eq : partial_inv e c with i; rw eq at hc,
    { contradiction },
    { rw [partial_inv_of_injective he] at eq,
      exact ⟨⟨i, hc⟩, eq⟩ } },
  { rintro c,
    simp [partial_inv_left he, option.cases_on'] }
end,
begin
  refine has_sum_le (λ c, _) this hg,
  obtain ⟨i, rfl⟩ | h := em (c ∈ set.range e),
  { rw [partial_inv_left he, option.cases_on'],
    exact h _ },
  { have : partial_inv e c = none := dif_neg h,
    rw [this, option.cases_on'],
    exact hs _ h }
end

lemma tsum_le_tsum_of_inj {g : κ → α} (e : ι → κ) (he : injective e)
  (hs : ∀ c ∉ set.range e, 0 ≤ g c) (h : ∀ i, f i ≤ g (e i)) (hf : summable f) (hg : summable g) :
  tsum f ≤ tsum g :=
has_sum_le_inj _ he hs h hf.has_sum hg.has_sum

lemma sum_le_has_sum (s : finset ι) (hs : ∀ i ∉ s, 0 ≤ f i) (hf : has_sum f a) :
  ∑ i in s, f i ≤ a :=
ge_of_tendsto hf (eventually_at_top.2 ⟨s, λ t hst,
  sum_le_sum_of_subset_of_nonneg hst $ λ i hbt hbs, hs i hbs⟩)

lemma is_lub_has_sum (h : ∀ i, 0 ≤ f i) (hf : has_sum f a) :
  is_lub (set.range $ λ s, ∑ i in s, f i) a :=
is_lub_of_tendsto_at_top (finset.sum_mono_set_of_nonneg h) hf

lemma le_has_sum (hf : has_sum f a) (i : ι) (hb : ∀ b' ≠ i, 0 ≤ f b') : f i ≤ a :=
calc f i = ∑ i in {i}, f i : finset.sum_singleton.symm
... ≤ a : sum_le_has_sum _ (by { convert hb, simp }) hf

lemma sum_le_tsum {f : ι → α} (s : finset ι) (hs : ∀ i ∉ s, 0 ≤ f i) (hf : summable f) :
  ∑ i in s, f i ≤ ∑' i, f i :=
sum_le_has_sum s hs hf.has_sum

lemma le_tsum (hf : summable f) (i : ι) (hb : ∀ b' ≠ i, 0 ≤ f b') : f i ≤ ∑' i, f i :=
le_has_sum (summable.has_sum hf) i hb

lemma tsum_le_tsum (h : ∀ i, f i ≤ g i) (hf : summable f) (hg : summable g) :
  ∑' i, f i ≤ ∑' i, g i :=
has_sum_le h hf.has_sum hg.has_sum

@[mono] lemma tsum_mono (hf : summable f) (hg : summable g) (h : f ≤ g) :
  ∑' n, f n ≤ ∑' n, g n :=
tsum_le_tsum h hf hg

lemma tsum_le_of_sum_le (hf : summable f) (h : ∀ s, ∑ i in s, f i ≤ a₂) : ∑' i, f i ≤ a₂ :=
has_sum_le_of_sum_le hf.has_sum h

lemma tsum_le_of_sum_le' (ha₂ : 0 ≤ a₂) (h : ∀ s, ∑ i in s, f i ≤ a₂) : ∑' i, f i ≤ a₂ :=
begin
  by_cases hf : summable f,
  { exact tsum_le_of_sum_le hf h },
  { rw tsum_eq_zero_of_not_summable hf,
    exact ha₂ }
end

lemma has_sum.nonneg (h : ∀ i, 0 ≤ g i) (ha : has_sum g a) : 0 ≤ a := has_sum_le h has_sum_zero ha
lemma has_sum.nonpos (h : ∀ i, g i ≤ 0) (ha : has_sum g a) : a ≤ 0 := has_sum_le h ha has_sum_zero

lemma tsum_nonneg (h : ∀ i, 0 ≤ g i) : 0 ≤ ∑' i, g i :=
begin
  by_cases hg : summable g,
  { exact hg.has_sum.nonneg h },
  { simp [tsum_eq_zero_of_not_summable hg] }
end

lemma tsum_nonpos (h : ∀ i, f i ≤ 0) : ∑' i, f i ≤ 0 :=
begin
  by_cases hf : summable f,
  { exact hf.has_sum.nonpos h },
  { simp [tsum_eq_zero_of_not_summable hf] }
end

end ordered_add_comm_monoid

section ordered_add_comm_group
variables [ordered_add_comm_group α] [topological_space α] [topological_add_group α]
  [order_closed_topology α] {f g : ι → α} {a₁ a₂ : α} {i : ι}

lemma has_sum_lt (h : f ≤ g) (hi : f i < g i) (hf : has_sum f a₁) (hg : has_sum g a₂) : a₁ < a₂ :=
have update f i 0 ≤ update g i 0 := update_le_update_iff.mpr ⟨rfl.le, λ i _, h i⟩,
have 0 - f i + a₁ ≤ 0 - g i + a₂ := has_sum_le this (hf.update i 0) (hg.update i 0),
by simpa only [zero_sub, add_neg_cancel_left] using add_lt_add_of_lt_of_le hi this

@[mono] lemma has_sum_strict_mono (hf : has_sum f a₁) (hg : has_sum g a₂) (h : f < g) : a₁ < a₂ :=
let ⟨hle, i, hi⟩ := pi.lt_def.mp h in has_sum_lt hle hi hf hg

lemma tsum_lt_tsum (h : f ≤ g) (hi : f i < g i) (hf : summable f) (hg : summable g) :
  ∑' n, f n < ∑' n, g n :=
has_sum_lt h hi hf.has_sum hg.has_sum

@[mono] lemma tsum_strict_mono (hf : summable f) (hg : summable g) (h : f < g) :
  ∑' n, f n < ∑' n, g n :=
let ⟨hle, i, hi⟩ := pi.lt_def.mp h in tsum_lt_tsum hle hi hf hg

lemma tsum_pos (hsum : summable g) (hg : ∀ i, 0 ≤ g i) (i : ι) (hi : 0 < g i) : 0 < ∑' i, g i :=
by { rw ←tsum_zero, exact tsum_lt_tsum hg hi summable_zero hsum }

lemma has_sum_zero_iff_of_nonneg (hf : ∀ i, 0 ≤ f i) : has_sum f 0 ↔ f = 0 :=
begin
  refine ⟨λ hf', _, _⟩,
  { ext i,
    refine (hf i).eq_of_not_gt (λ hi, _),
    simpa using has_sum_lt hf hi has_sum_zero hf' },
  { rintro rfl,
    exact has_sum_zero }
end

end ordered_add_comm_group

section canonically_ordered_add_monoid
variables [canonically_ordered_add_monoid α] [topological_space α] [order_closed_topology α]
  {f : ι → α} {a : α}

lemma le_has_sum' (hf : has_sum f a) (i : ι) : f i ≤ a := le_has_sum hf i $ λ _ _, zero_le _

lemma le_tsum' (hf : summable f) (i : ι) : f i ≤ ∑' i, f i := le_tsum hf i $ λ _ _, zero_le _

lemma has_sum_zero_iff : has_sum f 0 ↔ ∀ x, f x = 0 :=
begin
  refine ⟨_, λ h, _⟩,
  { contrapose!,
    exact λ ⟨x, hx⟩ h, hx (nonpos_iff_eq_zero.1$ le_has_sum' h x) },
  { convert has_sum_zero,
    exact funext h }
end

lemma tsum_eq_zero_iff (hf : summable f) : ∑' i, f i = 0 ↔ ∀ x, f x = 0 :=
by rw [←has_sum_zero_iff, hf.has_sum_iff]

lemma tsum_ne_zero_iff (hf : summable f) : ∑' i, f i ≠ 0 ↔ ∃ x, f x ≠ 0 :=
by rw [ne.def, tsum_eq_zero_iff hf, not_forall]

lemma is_lub_has_sum' (hf : has_sum f a) : is_lub (set.range $ λ s, ∑ i in s, f i) a :=
is_lub_of_tendsto_at_top (finset.sum_mono_set f) hf

end canonically_ordered_add_monoid

section linear_order

/-!
For infinite sums taking values in a linearly ordered monoid, the existence of a least upper
bound for the finite sums is a criterion for summability.

This criterion is useful when applied in a linearly ordered monoid which is also a complete or
conditionally complete linear order, such as `ℝ`, `ℝ≥0`, `ℝ≥0∞`, because it is then easy to check
the existence of a least upper bound.
-/

lemma has_sum_of_is_lub_of_nonneg [linear_ordered_add_comm_monoid α] [topological_space α]
  [order_topology α] {f : ι → α} (i : α) (h : ∀ i, 0 ≤ f i)
  (hf : is_lub (set.range $ λ s, ∑ i in s, f i) i) :
  has_sum f i :=
tendsto_at_top_is_lub (finset.sum_mono_set_of_nonneg h) hf

lemma has_sum_of_is_lub [canonically_linear_ordered_add_monoid α] [topological_space α]
   [order_topology α] {f : ι → α} (b : α) (hf : is_lub (set.range $ λ s, ∑ i in s, f i) b) :
  has_sum f b :=
tendsto_at_top_is_lub (finset.sum_mono_set f) hf

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

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import algebra.order.archimedean
import topology.algebra.big_operators.basic
import topology.algebra.order.field
import topology.algebra.order.monotone_convergence

/-!
# Infinite sum in an order

This file provides lemmas about the interaction of infinite sums and order operations.
-/

open finset filter function
open_locale big_operators classical

variables {α β γ : Type*}

section preorder
variables [preorder α] [add_comm_monoid α] [topological_space α] [order_closed_topology α]
  [t2_space α] {f : ℕ → α} {c : α}

lemma tsum_le_of_sum_range_le (hf : summable f) (h : ∀ n, ∑ i in range n, f i ≤ c) :
  ∑' n, f n ≤ c :=
let ⟨l, hl⟩ := hf in hl.tsum_eq.symm ▸ le_of_tendsto' hl.tendsto_sum_nat h

end preorder

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid α] [topological_space α] [order_closed_topology α] {f g : β → α}
  {a a₁ a₂ : α}

lemma has_sum_le (h : ∀ b, f b ≤ g b) (hf : has_sum f a₁) (hg : has_sum g a₂) : a₁ ≤ a₂ :=
le_of_tendsto_of_tendsto' hf hg $ λ s, sum_le_sum $ λ b _, h b

@[mono] lemma has_sum_mono (hf : has_sum f a₁) (hg : has_sum g a₂) (h : f ≤ g) : a₁ ≤ a₂ :=
has_sum_le h hf hg

lemma has_sum_le_of_sum_le (hf : has_sum f a) (h : ∀ s, ∑ b in s, f b ≤ a₂) : a ≤ a₂ :=
le_of_tendsto' hf h

lemma le_has_sum_of_le_sum (hf : has_sum f a) (h : ∀ s, a₂ ≤ ∑ b in s, f b) : a₂ ≤ a :=
ge_of_tendsto' hf h

lemma has_sum_le_inj {g : γ → α} (i : β → γ) (hi : injective i) (hs : ∀ c ∉ set.range i, 0 ≤ g c)
  (h : ∀ b, f b ≤ g (i b)) (hf : has_sum f a₁) (hg : has_sum g a₂) : a₁ ≤ a₂ :=
have has_sum (λ c, (partial_inv i c).cases_on' 0 f) a₁,
begin
  refine (has_sum_iff_has_sum_of_ne_zero_bij (i ∘ coe) (λ c₁ c₂ hc, hi hc) (λ c hc, _) _).2 hf,
  { rw mem_support at hc,
    cases eq : partial_inv i c with b; rw eq at hc,
    { contradiction },
    { rw [partial_inv_of_injective hi] at eq,
      exact ⟨⟨b, hc⟩, eq⟩ } },
  { rintro c,
    simp [partial_inv_left hi, option.cases_on'] }
end,
begin
  refine has_sum_le (λ c, _) this hg,
  by_cases c ∈ set.range i,
  { rcases h with ⟨b, rfl⟩,
    rw [partial_inv_left hi, option.cases_on'],
    exact h _ },
  { have : partial_inv i c = none := dif_neg h,
    rw [this, option.cases_on'],
    exact hs _ h }
end

lemma tsum_le_tsum_of_inj {g : γ → α} (i : β → γ) (hi : injective i)
  (hs : ∀ c ∉ set.range i, 0 ≤ g c) (h : ∀ b, f b ≤ g (i b)) (hf : summable f) (hg : summable g) :
  tsum f ≤ tsum g :=
has_sum_le_inj i hi hs h hf.has_sum hg.has_sum

lemma sum_le_has_sum (s : finset β) (hs : ∀ b ∉ s, 0 ≤ f b) (hf : has_sum f a) :
  ∑ b in s, f b ≤ a :=
ge_of_tendsto hf (eventually_at_top.2 ⟨s, λ t hst,
  sum_le_sum_of_subset_of_nonneg hst $ λ b hbt hbs, hs b hbs⟩)

lemma is_lub_has_sum (h : ∀ b, 0 ≤ f b) (hf : has_sum f a) :
  is_lub (set.range (λ s, ∑ b in s, f b)) a :=
is_lub_of_tendsto_at_top (finset.sum_mono_set_of_nonneg h) hf

lemma le_has_sum (hf : has_sum f a) (b : β) (hb : ∀ b' ≠ b, 0 ≤ f b') : f b ≤ a :=
calc f b = ∑ b in {b}, f b : finset.sum_singleton.symm
... ≤ a : sum_le_has_sum _ (by { convert hb, simp }) hf

lemma sum_le_tsum {f : β → α} (s : finset β) (hs : ∀ b ∉ s, 0 ≤ f b) (hf : summable f) :
  ∑ b in s, f b ≤ ∑' b, f b :=
sum_le_has_sum s hs hf.has_sum

lemma le_tsum (hf : summable f) (b : β) (hb : ∀ b' ≠ b, 0 ≤ f b') : f b ≤ ∑' b, f b :=
le_has_sum (summable.has_sum hf) b hb

lemma tsum_le_tsum (h : ∀ b, f b ≤ g b) (hf : summable f) (hg : summable g) : ∑' b, f b ≤ ∑' b, g b :=
has_sum_le h hf.has_sum hg.has_sum

@[mono] lemma tsum_mono (hf : summable f) (hg : summable g) (h : f ≤ g) :
  ∑' n, f n ≤ ∑' n, g n :=
tsum_le_tsum h hf hg

lemma tsum_le_of_sum_le (hf : summable f) (h : ∀ s, ∑ b in s, f b ≤ a₂) : ∑' b, f b ≤ a₂ :=
has_sum_le_of_sum_le hf.has_sum h

lemma tsum_le_of_sum_le' (ha₂ : 0 ≤ a₂) (h : ∀ s, ∑ b in s, f b ≤ a₂) : ∑' b, f b ≤ a₂ :=
begin
  by_cases hf : summable f,
  { exact tsum_le_of_sum_le hf h },
  { rw tsum_eq_zero_of_not_summable hf,
    exact ha₂ }
end

lemma has_sum.nonneg (h : ∀ b, 0 ≤ g b) (ha : has_sum g a) : 0 ≤ a := has_sum_le h has_sum_zero ha
lemma has_sum.nonpos (h : ∀ b, g b ≤ 0) (ha : has_sum g a) : a ≤ 0 := has_sum_le h ha has_sum_zero

lemma tsum_nonneg (h : ∀ b, 0 ≤ g b) : 0 ≤ ∑' b, g b :=
begin
  by_cases hg : summable g,
  { exact hg.has_sum.nonneg h },
  { simp [tsum_eq_zero_of_not_summable hg] }
end

lemma tsum_nonpos (h : ∀ b, f b ≤ 0) : ∑' b, f b ≤ 0 :=
begin
  by_cases hf : summable f,
  { exact hf.has_sum.nonpos h },
  { simp [tsum_eq_zero_of_not_summable hf] }
end

end ordered_add_comm_monoid

section ordered_add_comm_group
variables [ordered_add_comm_group α] [topological_space α] [topological_add_group α]
  [order_closed_topology α] {f g : β → α} {a₁ a₂ : α} {i : β}

lemma has_sum_lt (h : f ≤ g) (hi : f i < g i) (hf : has_sum f a₁) (hg : has_sum g a₂) : a₁ < a₂ :=
have update f i 0 ≤ update g i 0 := update_le_update_iff.mpr ⟨rfl.le, λ i _, h i⟩,
have 0 - f i + a₁ ≤ 0 - g i + a₂ := has_sum_le this (hf.update i 0) (hg.update i 0),
by simpa only [zero_sub, add_neg_cancel_left] using add_lt_add_of_lt_of_le hi this

@[mono] lemma has_sum_strict_mono (hf : has_sum f a₁) (hg : has_sum g a₂) (h : f < g) : a₁ < a₂ :=
let ⟨hle, i, hi⟩ := pi.lt_def.mp h in has_sum_lt hle hi hf hg

lemma tsum_lt_tsum {i : β} (h : f ≤ g) (hi : f i < g i) (hf : summable f) (hg : summable g) :
  ∑' n, f n < ∑' n, g n :=
has_sum_lt h hi hf.has_sum hg.has_sum

@[mono] lemma tsum_strict_mono (hf : summable f) (hg : summable g) (h : f < g) :
  ∑' n, f n < ∑' n, g n :=
let ⟨hle, i, hi⟩ := pi.lt_def.mp h in tsum_lt_tsum hle hi hf hg

lemma tsum_pos (hsum : summable g) (hg : ∀ b, 0 ≤ g b) (i : β) (hi : 0 < g i) : 0 < ∑' b, g b :=
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
  {f : β → α} {a : α}

lemma le_has_sum' (hf : has_sum f a) (b : β) : f b ≤ a := le_has_sum hf b $ λ _ _, zero_le _

lemma le_tsum' (hf : summable f) (b : β) : f b ≤ ∑' b, f b := le_tsum hf b $ λ _ _, zero_le _

lemma has_sum_zero_iff : has_sum f 0 ↔ ∀ x, f x = 0 :=
begin
  refine ⟨_, λ h, _⟩,
  { contrapose!,
    exact λ ⟨x, hx⟩ h, irrefl _ (lt_of_lt_of_le (pos_iff_ne_zero.2 hx) (le_has_sum' h x)) },
  { convert has_sum_zero,
    exact funext h }
end

lemma tsum_eq_zero_iff (hf : summable f) : ∑' i, f i = 0 ↔ ∀ x, f x = 0 :=
by rw [←has_sum_zero_iff, hf.has_sum_iff]

lemma tsum_ne_zero_iff (hf : summable f) : ∑' i, f i ≠ 0 ↔ ∃ x, f x ≠ 0 :=
by rw [ne.def, tsum_eq_zero_iff hf, not_forall]

lemma is_lub_has_sum' (hf : has_sum f a) : is_lub (set.range (λ s, ∑ b in s, f b)) a :=
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
  [order_topology α] {f : β → α} (b : α) (h : ∀ b, 0 ≤ f b)
  (hf : is_lub (set.range (λ s, ∑ a in s, f a)) b) :
  has_sum f b :=
tendsto_at_top_is_lub (finset.sum_mono_set_of_nonneg h) hf

lemma has_sum_of_is_lub [canonically_linear_ordered_add_monoid α] [topological_space α]
   [order_topology α] {f : β → α} (b : α) (hf : is_lub (set.range (λ s, ∑ a in s, f a)) b) :
  has_sum f b :=
tendsto_at_top_is_lub (finset.sum_mono_set f) hf

lemma summable_abs_iff [linear_ordered_add_comm_group α] [uniform_space α]
  [uniform_add_group α] [complete_space α] {f : β → α} :
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

--TODO: Change the conclusion to `finite β`
lemma finite_of_summable_const [linear_ordered_add_comm_group α] [archimedean α]
  [topological_space α] [order_closed_topology α] {b : α} (hb : 0 < b)
  (hf : summable (λ a : β, b)) :
  set.finite (set.univ : set β) :=
begin
  have H : ∀ s : finset β, s.card • b ≤ ∑' a : β, b,
  { intros s,
    simpa using sum_le_has_sum s (λ a ha, hb.le) hf.has_sum },
  obtain ⟨n, hn⟩ := archimedean.arch (∑' a : β, b) hb,
  have : ∀ s : finset β, s.card ≤ n,
  { intros s,
    simpa [nsmul_le_nsmul_iff hb] using (H s).trans hn },
  haveI : fintype β := fintype_of_finset_card_le n this,
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

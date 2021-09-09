/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import algebra.indicator_function
import order.filter.at_top_bot

/-!
# Indicator function and filters

Properties of indicator functions involving `=ᶠ` and `≤ᶠ`.

## Tags
indicator, characteristic, filter
-/


variables {α β M E : Type*}

open set filter classical
open_locale filter classical

section has_zero
variables [has_zero M] {s t : set α} {f g : α → M} {a : α} {l : filter α}

lemma indicator_eventually_eq (hf : f =ᶠ[l ⊓ 𝓟 s] g) (hs : s =ᶠ[l] t) :
  indicator s f =ᶠ[l] indicator t g :=
(eventually_inf_principal.1 hf).mp $ hs.mem_iff.mono $ λ x hst hfg,
by_cases (λ hxs : x ∈ s, by simp only [*, hst.1 hxs, indicator_of_mem])
  (λ hxs, by simp only [indicator_of_not_mem hxs, indicator_of_not_mem (mt hst.2 hxs)])

end has_zero

section add_monoid
variables [add_monoid M] {s t : set α} {f g : α → M} {a : α} {l : filter α}

lemma indicator_union_eventually_eq (h : ∀ᶠ a in l, a ∉ s ∩ t) :
  indicator (s ∪ t) f =ᶠ[l] indicator s f + indicator t f :=
h.mono $ λ a ha, indicator_union_of_not_mem_inter ha _

end add_monoid

section order
variables [has_zero β] [preorder β] {s t : set α} {f g : α → β} {a : α} {l : filter α}

lemma indicator_eventually_le_indicator (h : f ≤ᶠ[l ⊓ 𝓟 s] g) :
  indicator s f ≤ᶠ[l] indicator s g :=
(eventually_inf_principal.1 h).mono $ assume a h,
indicator_rel_indicator (le_refl _) h

end order

lemma tendsto_indicator_of_monotone {ι} [preorder ι] [has_zero β]
  (s : ι → set α) (hs : monotone s) (f : α → β) (a : α) :
  tendsto (λi, indicator (s i) f a) at_top (pure $ indicator (⋃ i, s i) f a) :=
begin
  by_cases h : ∃i, a ∈ s i,
  { rcases h with ⟨i, hi⟩,
    refine tendsto_pure.2 ((eventually_ge_at_top i).mono $ assume n hn, _),
    rw [indicator_of_mem (hs hn hi) _, indicator_of_mem ((subset_Union _ _) hi) _] },
  { rw [not_exists] at h,
    simp only [indicator_of_not_mem (h _)],
    convert tendsto_const_pure,
    apply indicator_of_not_mem, simpa only [not_exists, mem_Union] }
end

lemma tendsto_indicator_of_antimono {ι} [preorder ι] [has_zero β]
  (s : ι → set α) (hs : ∀⦃i j⦄, i ≤ j → s j ⊆ s i) (f : α → β) (a : α) :
  tendsto (λi, indicator (s i) f a) at_top (pure $ indicator (⋂ i, s i) f a) :=
begin
  by_cases h : ∃i, a ∉ s i,
  { rcases h with ⟨i, hi⟩,
    refine tendsto_pure.2 ((eventually_ge_at_top i).mono $ assume n hn, _),
    rw [indicator_of_not_mem _ _, indicator_of_not_mem _ _],
    { simp only [mem_Inter, not_forall], exact ⟨i, hi⟩ },
    { assume h, have := hs hn h, contradiction } },
  { push_neg at h,
    simp only [indicator_of_mem, h, (mem_Inter.2 h), tendsto_const_pure] }
end

lemma tendsto_indicator_bUnion_finset {ι} [has_zero β] (s : ι → set α) (f : α → β) (a : α) :
  tendsto (λ (n : finset ι), indicator (⋃i∈n, s i) f a) at_top (pure $ indicator (Union s) f a) :=
begin
  rw Union_eq_Union_finset s,
  refine tendsto_indicator_of_monotone (λ n : finset ι, ⋃ i ∈ n, s i) _ f a,
  exact λ t₁ t₂, bUnion_subset_bUnion_left
end

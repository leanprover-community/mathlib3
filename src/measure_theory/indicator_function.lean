/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import data.indicator_function
import measure_theory.measure_space

/-!
# Indicator function

Properties of indicator functions.

## Tags
indicator, characteristic
-/

noncomputable theory
open_locale classical

open set measure_theory filter

universes u v
variables {α : Type u} {β : Type v}

section has_zero
variables [has_zero β] {s t : set α} {f g : α → β} {a : α}

lemma indicator_congr_ae [measure_space α] (h : ∀ᵐ a, a ∈ s → f a = g a) :
  ∀ᵐ a, indicator s f a = indicator s g a :=
begin
  filter_upwards [h],
  simp only [mem_set_of_eq, indicator],
  assume a ha,
  split_ifs with h₁,
  { exact ha h₁ },
  refl
end

lemma indicator_congr_of_set [measure_space α] (h : ∀ᵐ a, a ∈ s ↔ a ∈ t) :
  ∀ᵐ a, indicator s f a = indicator t f a :=
begin
  filter_upwards [h],
  simp only [mem_set_of_eq, indicator],
  assume a ha,
  split_ifs with h₁ h₂ h₂,
  { refl },
  { have := ha.1 h₁, contradiction },
  { have := ha.2 h₂, contradiction },
  refl
end

end has_zero

section has_add
variables [add_monoid β] {s t : set α} {f g : α → β} {a : α}

lemma indicator_union_ae [measure_space α] {β : Type*} [add_monoid β]
  (h : ∀ᵐ a, a ∉ s ∩ t) (f : α → β) :
  ∀ᵐ a, indicator (s ∪ t) f a = indicator s f a + indicator t f a :=
begin
  filter_upwards [h],
  simp only [mem_set_of_eq],
  assume a ha,
  exact indicator_union_of_not_mem_inter ha _
end

end has_add

section norm
variables [normed_group β] {s t : set α} {f g : α → β} {a : α}

lemma norm_indicator_le_of_subset (h : s ⊆ t) (f : α → β) (a : α) :
  ∥indicator s f a∥ ≤ ∥indicator t f a∥ :=
begin
  simp only [indicator],
  split_ifs with h₁ h₂,
  { refl },
  { exact absurd (h h₁) h₂ },
  { simp only [norm_zero, norm_nonneg] },
  refl
end

lemma norm_indicator_le_norm_self (f : α → β) (a : α) : ∥indicator s f a∥ ≤ ∥f a∥ :=
by { convert norm_indicator_le_of_subset (subset_univ s) f a, rw indicator_univ }

lemma norm_indicator_eq_indicator_norm (f : α → β) (a : α) : ∥indicator s f a∥ = indicator s (λa, ∥f a∥) a :=
by { simp only [indicator], split_ifs, { refl }, rw norm_zero }

lemma indicator_norm_le_norm_self (f : α → β) (a : α) : indicator s (λa, ∥f a∥) a ≤ ∥f a∥ :=
by { rw ← norm_indicator_eq_indicator_norm, exact norm_indicator_le_norm_self _ _ }

end norm

section order
variables [has_zero β] [preorder β] {s t : set α} {f g : α → β} {a : α}

lemma indicator_le_indicator_ae [measure_space α] (h : ∀ᵐ a, a ∈ s → f a ≤ g a) :
  ∀ᵐ a, indicator s f a ≤ indicator s g a :=
begin
  refine h.mono (λ a h, _),
  simp only [indicator],
  split_ifs with ha,
  { exact h ha },
  refl
end

end order

lemma tendsto_indicator_of_monotone {ι} [semilattice_sup ι] [has_zero β]
  (s : ι → set α) (hs : monotone s) (f : α → β) (a : α) :
  tendsto (λi, indicator (s i) f a) at_top (pure $ indicator (Union s) f a) :=
begin
  by_cases h : ∃i, a ∈ s i,
  { rcases h with ⟨i, hi⟩,
    haveI : inhabited ι := ⟨i⟩,
    simp only [tendsto_pure, eventually_at_top],
    use i, assume n hn,
    rw [indicator_of_mem (hs hn hi) _, indicator_of_mem ((subset_Union _ _) hi) _] },
  { rw [not_exists] at h,
    have : (λi, indicator (s i) f a) = λi, 0 := funext (λi, indicator_of_not_mem (h i) _),
    rw this,
    have : indicator (Union s) f a = 0,
      { apply indicator_of_not_mem, simpa only [not_exists, mem_Union] },
    rw this,
    exact tendsto_const_pure }
end

lemma tendsto_indicator_of_antimono {ι} [semilattice_sup ι] [has_zero β]
  (s : ι → set α) (hs : ∀i j, i ≤ j → s j ⊆ s i) (f : α → β) (a : α) :
  tendsto (λi, indicator (s i) f a) at_top (pure $ indicator (Inter s) f a) :=
begin
  by_cases h : ∃i, a ∉ s i,
  { rcases h with ⟨i, hi⟩,
    haveI : inhabited ι := ⟨i⟩,
    simp only [tendsto_pure, eventually_at_top],
    use i, assume n hn,
    rw [indicator_of_not_mem _ _, indicator_of_not_mem _ _],
    { simp only [mem_Inter, not_forall], exact ⟨i, hi⟩ },
    { assume h, have := hs i _ hn h, contradiction } },
  { simp only [not_exists, not_not_mem] at h,
    have : (λi, indicator (s i) f a) = λi, f a := funext (λi, indicator_of_mem (h i) _),
    rw this,
    have : indicator (Inter s) f a = f a,
      { apply indicator_of_mem, simpa only [mem_Inter] },
    rw this,
    exact tendsto_const_pure }
end

lemma tendsto_indicator_bUnion_finset {ι} [has_zero β] (s : ι → set α) (f : α → β) (a : α) :
  tendsto (λ (n : finset ι), indicator (⋃i∈n, s i) f a) at_top (pure $ indicator (Union s) f a) :=
begin
  by_cases h : ∃i, a ∈ s i,
  { simp only [tendsto_pure, eventually_at_top, ge_iff_le, finset.le_iff_subset],
    rcases h with ⟨i, hi⟩,
    use {i}, assume n hn,
    replace hn : i ∈ n := hn (finset.mem_singleton_self _),
    rw [indicator_of_mem, indicator_of_mem],
    { rw [mem_Union], use i, assumption },
    { rw [mem_Union], use i, rw [mem_Union], use hn, assumption } },
  { rw [not_exists] at h,
    have : (λ (n : finset ι), indicator (⋃ (i : ι) (H : i ∈ n), s i) f a) = λi, 0,
      { funext,
        rw indicator_of_not_mem,
        simp only [not_exists, exists_prop, mem_Union, not_and],
        intros, apply h },
    rw this,
    have : indicator (Union s) f a = 0,
      { apply indicator_of_not_mem, simpa only [not_exists, mem_Union] },
    rw this,
    exact tendsto_const_pure }
end

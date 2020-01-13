/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/

import measure_theory.measure_space
import analysis.normed_space.basic

/-!
# Indicator function

`indicator (s : set α) (f : α → β) (a : α)` is `f x` if `x ∈ s` and is `0` otherwise.

## Implementation note

In mathematics, an indicator function or a characteristic function is a function used to indicate
membership of an element in a set `s`, having the value `1` for all elements of `s` and the value  `0`
otherwise. But since it is usually used to restrict a function to a certain set `s`, we let the
indicator function take the value `f x` for some function `f`, instead of `1`. If the usual indicator
function is needed, just set `f` to be the constant function `λx, 1`.

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

/-- `indicator s f a` is `f a` if `a ∈ s`, `0` otherwise.  -/
@[reducible]
def indicator (s : set α) (f : α → β) : α → β := λ x, if x ∈ s then f x else 0

@[simp] lemma indicator_of_mem (h : a ∈ s) (f : α → β) : indicator s f a = f a := if_pos h

@[simp] lemma indicator_of_not_mem (h : a ∉ s) (f : α → β) : indicator s f a = 0 := if_neg h

lemma indicator_congr (h : ∀ a ∈ s, f a = g a) : indicator s f = indicator s g :=
funext $ λx, by { simp only [indicator], split_ifs, { exact h _ h_1 }, refl }

lemma indicator_congr_ae [measure_space α] (h : ∀ₘ a, a ∈ s → f a = g a) :
  ∀ₘ a, indicator s f a = indicator s g a :=
begin
  filter_upwards [h],
  simp only [mem_set_of_eq, indicator],
  assume a ha,
  split_ifs,
  { exact ha h_1 },
  refl
end

lemma indicator_congr_of_set [measure_space α] (h : ∀ₘ a, a ∈ s ↔ a ∈ t) :
  ∀ₘ a, indicator s f a = indicator t f a :=
begin
  filter_upwards [h],
  simp only [mem_set_of_eq, indicator],
  assume a ha,
  split_ifs,
  { refl },
  { have := ha.1 h_1, contradiction },
  { have := ha.2 h_2, contradiction },
  refl
end

@[simp] lemma indicator_univ (f : α → β) : indicator (univ : set α) f = f :=
funext $ λx, indicator_of_mem (mem_univ _) f

@[simp] lemma indicator_empty (f : α → β) : indicator (∅ : set α) f = λa, 0 :=
funext $ λx, indicator_of_not_mem (not_mem_empty _) f

variable (β)
@[simp] lemma indicator_zero (s : set α) : indicator s (λx, (0:β)) = λx, (0:β) :=
funext $ λx, by { simp only [indicator], split_ifs, refl, refl }
variable {β}

lemma indicator_indicator (s t : set α) (f : α → β) : indicator s (indicator t f) = indicator (s ∩ t) f :=
funext $ λx, by { simp only [indicator], split_ifs, repeat {simp * at * {contextual := tt}} }

-- TODO : move
lemma if_preimage (p : α → Prop) (f g : α → β) (B : set β) :
  (λa, if p a then f a else g a)⁻¹' B = p ∩ f ⁻¹' B ∪ (-p) ∩ g ⁻¹' B :=
begin
  ext,
  simp only [mem_inter_eq, mem_union_eq, mem_preimage],
  split_ifs;
  simp [mem_def, h]
end

lemma indicator_preimage (s : set α) (f : α → β) (B : set β) :
  (indicator s f)⁻¹' B = s ∩ f ⁻¹' B ∪ (-s) ∩ (λa:α, (0:β)) ⁻¹' B :=
by { rw [indicator, if_preimage], refl }

end has_zero

section has_add
variables [add_monoid β] {s t : set α} {f g : α → β} {a : α}

lemma indicator_union_of_not_mem_inter (h : a ∉ s ∩ t) (f : α → β) :
  indicator (s ∪ t) f a = indicator s f a + indicator t f a :=
by { simp only [indicator], split_ifs, repeat {simp * at * {contextual := tt}} }

lemma indicator_union_of_disjoint (h : disjoint s t) (f : α → β) :
  indicator (s ∪ t) f = λa, indicator s f a + indicator t f a :=
funext $ λa, indicator_union_of_not_mem_inter
  (by { convert not_mem_empty a, have := disjoint.eq_bot h, assumption })
  _

lemma indicator_union_ae [measure_space α] {β : Type*} [add_monoid β]
  (h : ∀ₘ a, a ∉ s ∩ t) (f : α → β) :
  ∀ₘ a, indicator (s ∪ t) f a = indicator s f a + indicator t f a :=
begin
  filter_upwards [h],
  simp only [mem_set_of_eq],
  assume a ha,
  exact indicator_union_of_not_mem_inter ha _
end

lemma indicator_add (s : set α) (f g : α → β) :
  indicator s (λa, f a + g a) = λa, indicator s f a + indicator s g a :=
by { funext, simp only [indicator], split_ifs, { refl }, rw add_zero }

lemma indicator_smul {𝕜 : Type*} [monoid 𝕜] [distrib_mul_action 𝕜 β] (s : set α) (r : 𝕜) (f : α → β) :
  indicator s (λ (x : α), r • f x) = λ (x : α), r • indicator s f x :=
by { simp only [indicator], funext, split_ifs, refl, exact (smul_zero r).symm }

lemma indicator_neg {β : Type*} [add_group β] (s : set α) (f : α → β) :
  indicator s (λa, - f a) = λa, - indicator s f a :=
by { funext, simp only [indicator], split_ifs, { refl }, rw neg_zero }

lemma indicator_sub {β : Type*} [add_group β] (s : set α) (f g : α → β) :
  indicator s (λa, f a - g a) = λa, indicator s f a - indicator s g a :=
by { funext, simp only [indicator], split_ifs, { refl }, rw sub_zero }

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

lemma norm_indicator_eq_indicator_norm (f : α → β) (a : α) :∥indicator s f a∥ = indicator s (λa, ∥f a∥) a :=
by { simp only [indicator], split_ifs, { refl }, rw norm_zero }

end norm

section order
variables [has_zero β] [preorder β] {s t : set α} {f g : α → β} {a : α}

lemma indicator_le_indicator (h : f a ≤ g a) : indicator s f a ≤ indicator s g a :=
by { simp only [indicator], split_ifs with ha, { exact h }, refl }

lemma indicator_le_indicator_of_subset (h : s ⊆ t) (hf : ∀a, 0 ≤ f a) (a : α) :
  indicator s f a ≤ indicator t f a :=
begin
  simp only [indicator],
  split_ifs,
  { refl },
  { have := h h_1, contradiction },
  { exact hf a },
  { refl }
end

lemma indicator_le_indicator_ae [measure_space α] (h : ∀ₘ a, a ∈ s → f a ≤ g a) :
  ∀ₘ a, indicator s f a ≤ indicator s g a :=
begin
  filter_upwards [h],
  simp only [mem_set_of_eq, indicator],
  assume a h,
  split_ifs with ha,
  { exact h ha },
  refl
end

end order

section tendsto
variables [has_zero β] [topological_space β]

lemma tendsto_indicator_of_monotone (s : ℕ → set α) (hs : monotone s) (f : α → β)
  (a : α) : tendsto (λi, indicator (s i) f a) at_top (nhds $ indicator (Union s) f a) :=
begin
  by_cases h : ∃i, a ∈ s i,
  { rcases h with ⟨i, hi⟩,
    refine tendsto_nhds.mpr (λ t ht hf, _),
    simp only [mem_at_top_sets, mem_preimage],
    use i, assume n hn,
    have : indicator (s n) f a = f a := indicator_of_mem (hs hn hi) _,
    rw this,
    have : indicator (Union s) f a = f a := indicator_of_mem ((subset_Union _ _) hi) _,
    rwa this at hf },
  { rw [not_exists] at h,
    have : (λi, indicator (s i) f a) = λi, 0 := funext (λi, indicator_of_not_mem (h i) _),
    rw this,
    have : indicator (Union s) f a = 0,
      { apply indicator_of_not_mem, simpa only [not_exists, mem_Union] },
    rw this,
    exact tendsto_const_nhds }
end

lemma tendsto_indicator_of_decreasing (s : ℕ → set α) (hs : ∀i j, i ≤ j → s j ⊆ s i) (f : α → β)
  (a : α) : tendsto (λi, indicator (s i) f a) at_top (nhds $ indicator (Inter s) f a) :=
begin
  by_cases h : ∃i, a ∉ s i,
  { rcases h with ⟨i, hi⟩,
    refine tendsto_nhds.mpr (λ t ht hf, _),
    simp only [mem_at_top_sets, mem_preimage],
    use i, assume n hn,
    have : indicator (s n) f a = 0 := indicator_of_not_mem _ _,
    rw this,
    have : indicator (Inter s) f a = 0 := indicator_of_not_mem _ _,
    rwa this at hf,
    { simp only [mem_Inter, not_forall], exact ⟨i, hi⟩ },
    { assume h, have := hs i _ hn h, contradiction } },
  { simp only [not_exists, not_not_mem] at h,
    have : (λi, indicator (s i) f a) = λi, f a := funext (λi, indicator_of_mem (h i) _),
    rw this,
    have : indicator (Inter s) f a = f a,
      { apply indicator_of_mem, simpa only [mem_Inter] },
    rw this,
    exact tendsto_const_nhds }
end

end tendsto

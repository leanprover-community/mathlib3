/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/

import data.set group_theory.group_action

/-!
# Indicator function

`indicator (s : set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `0` otherwise.

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

open set

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

lemma indicator_preimage (s : set α) (f : α → β) (B : set β) :
  (indicator s f)⁻¹' B = s ∩ f ⁻¹' B ∪ (-s) ∩ (λa:α, (0:β)) ⁻¹' B :=
by { rw [indicator, if_preimage] }

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

end order

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.set.image
import order.lattice
import order.max

/-!
# Directed indexed families and sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines directed indexed families and directed sets. An indexed family/set is
directed iff each pair of elements has a shared upper bound.

## Main declarations

* `directed r f`: Predicate stating that the indexed family `f` is `r`-directed.
* `directed_on r s`: Predicate stating that the set `s` is `r`-directed.
* `is_directed α r`: Prop-valued mixin stating that `α` is `r`-directed. Follows the style of the
  unbundled relation classes such as `is_total`.
-/

open function

universes u v w

variables {α : Type u} {β : Type v} {ι : Sort w} (r r' s : α → α → Prop)
local infix ` ≼ ` : 50 := r

/-- A family of elements of α is directed (with respect to a relation `≼` on α)
  if there is a member of the family `≼`-above any pair in the family.  -/
def directed (f : ι → α) := ∀ x y, ∃ z, f x ≼ f z ∧ f y ≼ f z

/-- A subset of α is directed if there is an element of the set `≼`-above any
  pair of elements in the set. -/
def directed_on (s : set α) := ∀ (x ∈ s) (y ∈ s), ∃ z ∈ s, x ≼ z ∧ y ≼ z

variables {r r'}

theorem directed_on_iff_directed {s} : @directed_on α r s ↔ directed r (coe : s → α) :=
by simp [directed, directed_on]; refine ball_congr (λ x hx, by simp; refl)

alias directed_on_iff_directed ↔ directed_on.directed_coe _

theorem directed_on_range {f : β → α} :
  directed r f ↔ directed_on r (set.range f) :=
by simp_rw [directed, directed_on, set.forall_range_iff, set.exists_range_iff]

theorem directed_on_image {s} {f : β → α} :
  directed_on r (f '' s) ↔ directed_on (f ⁻¹'o r) s :=
by simp only [directed_on, set.ball_image_iff, set.bex_image_iff, order.preimage]

lemma directed_on.mono' {s : set α} (hs : directed_on r s)
  (h : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b → r' a b) :
  directed_on r' s :=
λ x hx y hy, let ⟨z, hz, hxz, hyz⟩ := hs _ hx _ hy in ⟨z, hz, h hx hz hxz, h hy hz hyz⟩

lemma directed_on.mono {s : set α} (h : directed_on r s) (H : ∀ {a b}, r a b → r' a b) :
  directed_on r' s :=
h.mono' $ λ _ _ _ _, H

theorem directed_comp {ι} {f : ι → β} {g : β → α} :
  directed r (g ∘ f) ↔ directed (g ⁻¹'o r) f := iff.rfl

theorem directed.mono {s : α → α → Prop} {ι} {f : ι → α}
  (H : ∀ a b, r a b → s a b) (h : directed r f) : directed s f :=
λ a b, let ⟨c, h₁, h₂⟩ := h a b in ⟨c, H _ _ h₁, H _ _ h₂⟩

theorem directed.mono_comp {ι} {rb : β → β → Prop} {g : α → β} {f : ι → α}
  (hg : ∀ ⦃x y⦄, x ≼ y → rb (g x) (g y)) (hf : directed r f) :
  directed rb (g ∘ f) :=
directed_comp.2 $ hf.mono hg

/-- A monotone function on a sup-semilattice is directed. -/
lemma directed_of_sup [semilattice_sup α] {f : α → β} {r : β → β → Prop}
  (H : ∀ ⦃i j⦄, i ≤ j → r (f i) (f j)) : directed r f :=
λ a b, ⟨a ⊔ b, H le_sup_left, H le_sup_right⟩

lemma monotone.directed_le [semilattice_sup α] [preorder β] {f : α → β} :
  monotone f → directed (≤) f :=
directed_of_sup

lemma antitone.directed_ge [semilattice_sup α] [preorder β] {f : α → β} (hf : antitone f) :
  directed (≥) f :=
directed_of_sup hf

/-- A set stable by supremum is `≤`-directed. -/
lemma directed_on_of_sup_mem [semilattice_sup α] {S : set α}
  (H : ∀ ⦃i j⦄, i ∈ S → j ∈ S → i ⊔ j ∈ S) : directed_on (≤) S :=
λ a ha b hb, ⟨a ⊔ b, H ha hb, le_sup_left, le_sup_right⟩

lemma directed.extend_bot [preorder α] [order_bot α] {e : ι → β} {f : ι → α}
  (hf : directed (≤) f) (he : function.injective e) :
  directed (≤) (function.extend e f ⊥) :=
begin
  intros a b,
  rcases (em (∃ i, e i = a)).symm with ha | ⟨i, rfl⟩,
  { use b, simp [function.extend_apply' _ _ _ ha] },
  rcases (em (∃ i, e i = b)).symm with hb | ⟨j, rfl⟩,
  { use e i, simp [function.extend_apply' _ _ _ hb] },
  rcases hf i j with ⟨k, hi, hj⟩,
  use (e k),
  simp only [he.extend_apply, *, true_and]
end

/-- An antitone function on an inf-semilattice is directed. -/
lemma directed_of_inf [semilattice_inf α] {r : β → β → Prop} {f : α → β}
  (hf : ∀ a₁ a₂, a₁ ≤ a₂ → r (f a₂) (f a₁)) : directed r f :=
λ x y, ⟨x ⊓ y, hf _ _ inf_le_left, hf _ _ inf_le_right⟩

lemma monotone.directed_ge [semilattice_inf α] [preorder β] {f : α → β} (hf : monotone f) :
  directed (≥) f :=
directed_of_inf hf

lemma antitone.directed_le [semilattice_inf α] [preorder β] {f : α → β} (hf : antitone f) :
  directed (≤) f :=
directed_of_inf hf

/-- A set stable by infimum is `≥`-directed. -/
lemma directed_on_of_inf_mem [semilattice_inf α] {S : set α}
  (H : ∀ ⦃i j⦄, i ∈ S → j ∈ S → i ⊓ j ∈ S) : directed_on (≥) S :=
λ a ha b hb, ⟨a ⊓ b, H ha hb, inf_le_left, inf_le_right⟩

/-- `is_directed α r` states that for any elements `a`, `b` there exists an element `c` such that
`r a c` and `r b c`. -/
class is_directed (α : Type*) (r : α → α → Prop) : Prop :=
(directed (a b : α) : ∃ c, r a c ∧ r b c)

lemma directed_of (r : α → α → Prop) [is_directed α r] (a b : α) : ∃ c, r a c ∧ r b c :=
is_directed.directed _ _

lemma directed_id [is_directed α r] : directed r id := by convert directed_of r
lemma directed_id_iff : directed r id ↔ is_directed α r := ⟨λ h, ⟨h⟩, @directed_id _ _⟩

lemma directed_on_univ [is_directed α r] : directed_on r set.univ :=
λ a _ b _, let ⟨c, hc⟩ := directed_of r a b in ⟨c, trivial, hc⟩

lemma directed_on_univ_iff : directed_on r set.univ ↔ is_directed α r :=
⟨λ h, ⟨λ a b, let ⟨c, _, hc⟩ := h a trivial b trivial in ⟨c, hc⟩⟩, @directed_on_univ _ _⟩

@[priority 100]  -- see Note [lower instance priority]
instance is_total.to_is_directed [is_total α r] : is_directed α r :=
⟨λ a b, or.cases_on (total_of r a b) (λ h, ⟨b, h, refl _⟩) (λ h, ⟨a, refl _, h⟩)⟩

lemma is_directed_mono [is_directed α r] (h : ∀ ⦃a b⦄, r a b → s a b) : is_directed α s :=
⟨λ a b, let ⟨c, ha, hb⟩ := is_directed.directed a b in ⟨c, h ha, h hb⟩⟩

lemma exists_ge_ge [has_le α] [is_directed α (≤)] (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
directed_of (≤) a b

lemma exists_le_le [has_le α] [is_directed α (≥)] (a b : α) : ∃ c, c ≤ a ∧ c ≤ b :=
directed_of (≥) a b

instance order_dual.is_directed_ge [has_le α] [is_directed α (≤)] : is_directed αᵒᵈ (≥) :=
by assumption

instance order_dual.is_directed_le [has_le α] [is_directed α (≥)] : is_directed αᵒᵈ (≤) :=
by assumption

section preorder
variables [preorder α] {a : α}

protected lemma is_min.is_bot [is_directed α (≥)] (h : is_min a) : is_bot a :=
λ b, let ⟨c, hca, hcb⟩ := exists_le_le a b in (h hca).trans hcb

protected lemma is_max.is_top [is_directed α (≤)] (h : is_max a) : is_top a :=
h.to_dual.is_bot

lemma directed_on.is_bot_of_is_min {s : set α} (hd : directed_on (≥) s)
  {m} (hm : m ∈ s) (hmin : ∀ a ∈ s, a ≤ m → m ≤ a) : ∀ a ∈ s, m ≤ a :=
λ a as, let ⟨x, xs, xm, xa⟩ := hd m hm a as in (hmin x xs xm).trans xa

lemma directed_on.is_top_of_is_max {s : set α} (hd : directed_on (≤) s)
  {m} (hm : m ∈ s) (hmax : ∀ a ∈ s, m ≤ a → a ≤ m) : ∀ a ∈ s, a ≤ m :=
@directed_on.is_bot_of_is_min αᵒᵈ _ s hd m hm hmax

lemma is_top_or_exists_gt [is_directed α (≤)] (a : α) : is_top a ∨ (∃ b, a < b) :=
(em (is_max a)).imp is_max.is_top not_is_max_iff.mp

lemma is_bot_or_exists_lt [is_directed α (≥)] (a : α) : is_bot a ∨ (∃ b, b < a) :=
@is_top_or_exists_gt αᵒᵈ _ _ a

lemma is_bot_iff_is_min [is_directed α (≥)] : is_bot a ↔ is_min a :=
⟨is_bot.is_min, is_min.is_bot⟩

lemma is_top_iff_is_max [is_directed α (≤)] : is_top a ↔ is_max a := ⟨is_top.is_max, is_max.is_top⟩

variables (β) [partial_order β]

theorem exists_lt_of_directed_ge [is_directed β (≥)] [nontrivial β] : ∃ a b : β, a < b :=
begin
  rcases exists_pair_ne β with ⟨a, b, hne⟩,
  rcases is_bot_or_exists_lt a with ha|⟨c, hc⟩,
  exacts [⟨a, b, (ha b).lt_of_ne hne⟩, ⟨_, _, hc⟩]
end

theorem exists_lt_of_directed_le [is_directed β (≤)] [nontrivial β] : ∃ a b : β, a < b :=
let ⟨a, b, h⟩ := exists_lt_of_directed_ge βᵒᵈ in ⟨b, a, h⟩

end preorder

@[priority 100]  -- see Note [lower instance priority]
instance semilattice_sup.to_is_directed_le [semilattice_sup α] : is_directed α (≤) :=
⟨λ a b, ⟨a ⊔ b, le_sup_left, le_sup_right⟩⟩

@[priority 100]  -- see Note [lower instance priority]
instance semilattice_inf.to_is_directed_ge [semilattice_inf α] : is_directed α (≥) :=
⟨λ a b, ⟨a ⊓ b, inf_le_left, inf_le_right⟩⟩

@[priority 100]  -- see Note [lower instance priority]
instance order_top.to_is_directed_le [has_le α] [order_top α] : is_directed α (≤) :=
⟨λ a b, ⟨⊤, le_top, le_top⟩⟩

@[priority 100]  -- see Note [lower instance priority]
instance order_bot.to_is_directed_ge [has_le α] [order_bot α] : is_directed α (≥) :=
⟨λ a b, ⟨⊥, bot_le, bot_le⟩⟩

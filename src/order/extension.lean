/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import data.set.lattice
import order.zorn

/-!
# Extend a partial order to a linear order

This file constructs a linear order which is an extension of the given partial order, using Zorn's
lemma, and uses it to show the existence of a linear order on any type.
-/

universes u
open set classical
open_locale classical

def relation_ordering {α β : Type*} : partial_order (α → β → Prop) :=
{ le := λ r s, ∀ ⦃x y⦄, r x y → s x y,
  le_refl := λ r x y h, h,
  le_trans := λ r s t h₁ h₂ x y h, h₂ (h₁ h),
  le_antisymm := λ r s h₁ h₂,
  begin
    ext x y,
    exact ⟨λ h, h₁ h, λ h, h₂ h⟩,
  end }

def relation_Sup {α β : Type*} : complete_semilattice_Sup (α → β → Prop) :=
{ Sup := λ c x y, ∃ (r : α → β → Prop), r ∈ c ∧ r x y,
  le_Sup := λ c r hr x y h, ⟨r, hr, h⟩,
  Sup_le := λ c r hr x y ⟨s, hs₁, hs₂⟩, hr s hs₁ hs₂,
  ..relation_ordering }

local attribute [instance] relation_ordering

def increasing_union_preserving {α β : Type*} (p : (α → β → Prop) → Prop) : Prop :=
∀ (c : set (α → β → Prop)), (∀ r ∈ c, p r) → zorn.chain (≤) c → p (Sup c)

lemma increasing_union_preserving_is_refl {α : Type*} :
  increasing_union_preserving (is_refl α) :=
begin
  intros c hc₁ hc₂,
  rcases c.eq_empty_or_nonempty with (rfl | ⟨t, ht⟩),
  simp,

end

lemma increasing_union_preserving_is_trans {α : Type*} :
  increasing_union_preserving (is_trans α) :=
sorry

lemma increasing_union_preserving_is_antisymm {α : Type*} :
  increasing_union_preserving (is_antisymm α) :=
sorry

lemma increasing_union_preserving_and {α β : Type*} {p₁ p₂ : (α → β → Prop) → Prop}
  (hp₁ : increasing_union_preserving p₁) (hp₂ : increasing_union_preserving p₂) :
  increasing_union_preserving (λ r, p₁ r ∧ p₂ r) :=
λ c hc₁ hc₂, ⟨hp₁ _ (λ r hr, (hc₁ r hr).1) hc₂, hp₂ _ (λ r hr, (hc₁ r hr).2) hc₂⟩

lemma increasing_union_preserving_is_preorder {α : Type*} :
  increasing_union_preserving (is_preorder α) :=
begin
  convert increasing_union_preserving_and
    increasing_union_preserving_is_refl increasing_union_preserving_is_trans,
  ext r,
  split,
  { rintro ⟨t₁, t₂⟩,
    exact ⟨t₁, t₂⟩ },
  { rintro ⟨t₁, t₂⟩,
    exactI {} },
end

theorem extend_order {α : Type u} (p : (α → α → Prop) → Prop)
  (extend : ∀ s, p s → ∀ x y, ¬s x y → ¬s y x → ∃ s', p s' ∧ s ≤ s' ∧ s' x y)
  (incr_union : increasing_union_preserving p) :
  ∃ (s : α → α → Prop), is_total α s ∧ p s :=
begin
  obtain ⟨r, hr, hrm⟩ := zorn.zorn_partial_order₀ p _,
  refine ⟨r, ⟨_⟩, hr⟩,
  { intros x y,
    by_contra h,
    push_neg at h,
    obtain ⟨s, hs₁, hs₂, hs₃⟩ := extend r hr x y h.1 h.2,
    rw hrm _ hs₁ hs₂ at hs₃,
    apply h.1 hs₃ },
  { intros c hc₁ hc₂,
    refine ⟨Sup c, incr_union _ (λ r hr, hc₁ hr) hc₂, λ z, le_Sup⟩ },
end

theorem extend_partial_order {α : Type u} (r : α → α → Prop) [is_partial_order α r] :
  ∃ (s : α → α → Prop) [is_linear_order α s], ∀ x y, r x y → s x y :=
begin
  rcases extend_order (λ s, is_partial_order α s ∧ ∀ x y, r x y → s x y) _ with ⟨s, s₁, ⟨s₂, s₃⟩⟩,
  { exactI ⟨s, { total := s₁ }, s₃⟩ },
  rintro s ⟨hs, rs⟩ x y sxy syx,
  resetI,
  refine ⟨λ x' y', s x' y' ∨ (s x' x ∧ s y y'), ⟨_, λ _ _ h, or.inl (rs _ _ h)⟩, _⟩,
  { refine { refl := λ a, or.inl (refl _), trans := _, antisymm := _ },
  { rintro a b c (ab | ⟨ax, yb⟩) (bc | ⟨bx, yc⟩),
    { exact or.inl (trans ab bc) },
    { exact or.inr ⟨trans ab bx, yc⟩ },
    { exact or.inr ⟨ax, trans yb bc⟩ },
    { exact or.inr ⟨ax, yc⟩ } },
  { rintro a b (ab | ⟨ax, yb⟩) (ba | ⟨bx, ya⟩),
    { apply antisymm ab ba },
    { apply (syx (trans ya (trans ab bx))).elim },
    { apply (syx (trans yb (trans ba ax))).elim },
    { apply (syx (trans yb bx)).elim } } },
  { intros _ _ h,
    refine ⟨or.inl h, or.inr ⟨refl _, refl _⟩⟩ },
end

/--
Any partial order can be extended to a linear order.
-/
theorem extend_partial_order {α : Type u} (r : α → α → Prop) [is_partial_order α r] :
  ∃ (s : α → α → Prop) [is_linear_order α s], ∀ x y, r x y → s x y :=
begin
  let S : set (set (α × α)) :=
    λ R, is_partial_order α (λ x y, (x, y) ∈ R) ∧ ∀ (x' y' : α), r x' y' → (x', y') ∈ R,
  let R : set (α × α) := λ t, r t.1 t.2,
  have hR : R ∈ S := ⟨‹is_partial_order α r›, λ x y h, h⟩,
  have hS : ∀c ⊆ S, zorn.chain (⊆) c → c.nonempty → ∃ub ∈ S, ∀ s ∈ c, s ⊆ ub,
  { rintro c hc₁ hc₂ ⟨R', hR'⟩,
    refine ⟨⋃₀ c, ⟨_, λ x y rxy, ⟨R', hR', (hc₁ hR').2 x y rxy⟩⟩, λ s hs T hT, ⟨s, hs, hT⟩⟩,
    refine { refl := λ x, ⟨R', hR', (hc₁ hR').2 x x (refl x)⟩, trans := _, antisymm := _ },
    { rintro x y z ⟨S₁, h₁S₁, h₂S₁⟩ ⟨S₂, h₁S₂, h₂S₂⟩,
      cases hc₂.total_of_refl h₁S₁ h₁S₂,
      { refine ⟨S₂, h₁S₂, _⟩,
        have z := (hc₁ h₁S₂).1.trans,
        apply z _ _ _ (h h₂S₁) h₂S₂ },
      { refine ⟨S₁, h₁S₁, _⟩,
        have z := (hc₁ h₁S₁).1.trans,
        apply z _ _ _ h₂S₁ (h h₂S₂) } },
    { rintro x y ⟨S₁, h₁S₁, h₂S₁⟩ ⟨S₂, h₁S₂, h₂S₂⟩,
      cases hc₂.total_of_refl h₁S₁ h₁S₂,
      { have z := (hc₁ h₁S₂).1.antisymm,
        apply z x y (h h₂S₁) h₂S₂ },
      { have z := (hc₁ h₁S₁).1.antisymm,
        apply z x y h₂S₁ (h h₂S₂) } } },
  rcases zorn.zorn_subset₀ S hS _ hR with ⟨T, ⟨hT₁, TR⟩, -, hT₃⟩,
  let Tt : ∀ {a b c : α}, (a, b) ∈ T → (b, c) ∈ T → (a, c) ∈ T,
  { apply hT₁.trans },
  let Ta : ∀ {a b : α}, (a, b) ∈ T → (b, a) ∈ T → a = b,
  { apply hT₁.antisymm },
  refine ⟨λ x y, (x, y) ∈ T, { to_is_partial_order := hT₁, total := _ }, TR⟩,
  intros x y,
  by_contra h,
  push_neg at h,
  let T' : α × α → Prop := λ p, p ∈ T ∨ ((p.1, x) ∈ T ∧ (y, p.2) ∈ T),
  have T'S : T' ∈ S,
  { refine ⟨_, λ x y rxy, or.inl (TR _ _ rxy)⟩,
    refine
      { refl := λ x, or.inl (TR _ _ (refl _)),
        trans := _,
        antisymm := _ },
    { rintro a b c (ab | ⟨ax : (a,x) ∈ T, yb : (y,b) ∈ T⟩) (bc | ⟨bx : (b,x) ∈ T, yc : (y,c) ∈ T⟩),
      { exact or.inl (Tt ab bc) },
      { exact or.inr ⟨Tt ab bx, yc⟩ },
      { exact or.inr ⟨ax, Tt yb bc⟩ },
      { exact or.inr ⟨ax, yc⟩ } },
    { rintro a b (ab | ⟨ax : (a,x) ∈ T, yb : (y,b) ∈ T⟩) (ba | ⟨bx : (b,x) ∈ T, ya : (y,a) ∈ T⟩),
      { exact Ta ab ba },
      { exact (h.2 (Tt ya (Tt ab bx))).elim },
      { exact (h.2 (Tt yb (Tt ba ax))).elim },
      { exact (h.2 (Tt yb bx)).elim } } },
  rw ←hT₃ _ T'S (λ x, or.inl) at h,
  exact h.1 (or.inr ⟨TR _ _ (refl _), TR _ _ (refl _)⟩),
end

/--
There is a linear order on any type.
-/
lemma exists_linear_order {α : Type u} : ∃ (s : α → α → Prop), is_linear_order α s :=
begin
  rcases extend_partial_order (=) with ⟨s, hs₁, -⟩,
  refine ⟨s, hs₁⟩,
  exact { antisymm := λ _ _ h _, h },
end

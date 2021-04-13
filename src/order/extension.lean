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
lemma.
-/

universes u
open set classical
open_locale classical

/--
Any partial order can be extended to a linear order.
-/
theorem extend_partial_order {α : Type u} (r : α → α → Prop) [is_partial_order α r] :
  ∃ (s : α → α → Prop) [is_linear_order α s], r ≤ s :=
begin
  let S := {s | is_partial_order α s},
  have hS : ∀ c, c ⊆ S → zorn.chain (≤) c → ∀ y ∈ c, (∃ ub ∈ S, ∀ z ∈ c, z ≤ ub),
  { rintro c hc₁ hc₂ s hs,
    haveI := (hc₁ hs).1,
    refine ⟨Sup c, _, λ z hz, le_Sup hz⟩,
    refine { refl := _, trans := _, antisymm := _ }; simp_rw binary_relation_Sup_iff,
    { intro x,
      exact ⟨s, hs, refl x⟩ },
    { rintro x y z ⟨s₁, h₁s₁, h₂s₁⟩ ⟨s₂, h₁s₂, h₂s₂⟩,
      haveI : is_partial_order _ _ := hc₁ h₁s₁,
      haveI : is_partial_order _ _ := hc₁ h₁s₂,
      cases hc₂.total_of_refl h₁s₁ h₁s₂,
      { exact ⟨s₂, h₁s₂, trans (h _ _ h₂s₁) h₂s₂⟩ },
      { exact ⟨s₁, h₁s₁, trans h₂s₁ (h _ _ h₂s₂)⟩ } },
    { rintro x y ⟨s₁, h₁s₁, h₂s₁⟩ ⟨s₂, h₁s₂, h₂s₂⟩,
      haveI : is_partial_order _ _ := hc₁ h₁s₁,
      haveI : is_partial_order _ _ := hc₁ h₁s₂,
      cases hc₂.total_of_refl h₁s₁ h₁s₂,
      { exact antisymm (h _ _ h₂s₁) h₂s₂ },
      { apply antisymm h₂s₁ (h _ _ h₂s₂) } } },
  obtain ⟨s, hs₁ : is_partial_order _ _, rs, hs₂⟩ := zorn.zorn_nonempty_partial_order₀ S hS r ‹_›,
  resetI,
  refine ⟨s, { total := _ }, rs⟩,
  intros x y,
  by_contra h,
  push_neg at h,
  let s' := λ x' y', s x' y' ∨ s x' x ∧ s y y',
  rw ←hs₂ s' _ (λ _ _, or.inl) at h,
  { apply h.1 (or.inr ⟨refl _, refl _⟩) },
  { refine
      { refl := λ x, or.inl (refl _),
        trans := _,
        antisymm := _ },
    { rintro a b c (ab | ⟨ax : s a x, yb : s y b⟩) (bc | ⟨bx : s b x, yc : s y c⟩),
      { exact or.inl (trans ab bc), },
      { exact or.inr ⟨trans ab bx, yc⟩ },
      { exact or.inr ⟨ax, trans yb bc⟩ },
      { exact or.inr ⟨ax, yc⟩ } },
    { rintro a b (ab | ⟨ax : s a x, yb : s y b⟩) (ba | ⟨bx : s b x, ya : s y a⟩),
      { exact antisymm ab ba },
      { exact (h.2 (trans ya (trans ab bx))).elim },
      { exact (h.2 (trans yb (trans ba ax))).elim },
      { exact (h.2 (trans yb bx)).elim } } },
end

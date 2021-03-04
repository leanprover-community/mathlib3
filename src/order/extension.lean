/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bhavik Mehta
-/
import data.set.lattice
import order.zorn
noncomputable theory

universes u
open set classical
open_locale classical

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

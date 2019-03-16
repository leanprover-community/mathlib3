/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for discharging Presburger arithmetic goals using the Omega test.
-/

import logic.basic 

open tactic

variables {α β γ : Type} {p q r s : Prop}

lemma fun_mono_2 {p : α → β → γ} {a1 a2 : α} {b1 b2 : β} :
  a1 = a2 → b1 = b2 → (p a1 b1 = p a2 b2) :=
λ h1 h2, by rw [h1, h2]

lemma pred_mono_2 {p : α → β → Prop} {a1 a2 : α} {b1 b2 : β} :
  a1 = a2 → b1 = b2 → (p a1 b1 ↔ p a2 b2) :=
λ h1 h2, by rw [h1, h2]

lemma pred_mono_2' {c : Prop → Prop → Prop} {a1 a2 b1 b2 : Prop} :
  (a1 ↔ a2) → (b1 ↔ b2) → (c a1 b1 ↔ c a2 b2) :=
λ h1 h2, by rw [h1, h2]

lemma ite_rec {p} [hd : decidable p] {f g : α} (q : α → Prop)
  (hf : p → q f) (hg : ¬ p → q g) : q (@ite p hd α f g) := 
begin
  unfold ite, tactic.unfreeze_local_instances, 
  cases hd with h h, simp, apply hg h, simp, apply hf h
end

lemma exists_of_exists {α : Type} {p q : α → Prop} :
  (∀ a, p a → q a) → (∃ a, p a) → (∃ a, q a) :=
begin
  intros h1 h2, cases h2 with w h2, refine ⟨w,_⟩, 
  apply h1, assumption
end

lemma exists_iff_exists {α : Type} {p q : α → Prop} :
  (∀ a, p a ↔ q a) → ((∃ a, p a) ↔ ∃ a, q a) :=
begin
  intro h, constructor; intro h; 
  cases h with a ha; existsi a; 
  [{rw (h a).symm}, {rw h}]; assumption
end

lemma and_of_and : (p → q) → (r → s) → (p ∧ r) → (q ∧ s) :=
begin
  intros h1 h2 h3, cases h3 with h3 h4,
  apply and.intro (h1 h3) (h2 h4)
end

namespace classical

local attribute [instance] classical.dec 

lemma iff_iff {a b : Prop} : (a ↔ b) ↔ ((¬a ∨ b) ∧ (a ∨ ¬b)) := 
begin
  rw [iff_iff_implies_and_implies a b],
  simp only [imp_iff_not_or, or.comm]
end

lemma imp_iff_not_or {a b : Prop} : a → b ↔ ¬a ∨ b := 
_root_.imp_iff_not_or 

lemma not_exists_not :
  ∀ {p : α → Prop}, (¬∃ (x : α), ¬p x) ↔ ∀ (x : α), p x := 
λ p, _root_.not_exists_not

lemma not_and_distrib : ¬(p ∧ q) ↔ ¬p ∨ ¬q := not_and_distrib

end classical
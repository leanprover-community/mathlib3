/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon
-/
import data.list.chain
import data.list.zip

/-!
# The Following Are Equal

This file allows to state that all elements in a list are equival. It is used by
`tactic.tfae`. `tfae l` means `pairwise (=) l`.
-/

namespace list

variables {α β γ : Type*} {l la : list α} {lb : list β} {a b : α}

/--
tfae: The Following Are Equival.

The `tfae_have` and `tfae_finish` tactics can be useful in proofs with `tfae` goals.
-/
def tfae (l : list α) : Prop := pairwise (=) l

theorem tfae_nil : tfae ([] : list α) := pairwise.nil
theorem tfae_singleton (x : α) : tfae [x] := pairwise_singleton _ _
theorem tfae_repeat (x : α) (n : ℕ) : tfae (repeat x n) := pairwise_repeat rfl _

lemma tfae.eq_of_mem (h : tfae l) (ha : a ∈ l) (hb : b ∈ l) : a = b :=
h.forall_of_forall (λ _ _, eq.symm) (λ _ _, rfl) ha hb

lemma tfae_iff_forall : tfae l ↔ ∀ (a ∈ l) (b ∈ l), a = b :=
⟨λ h a ha b hb, h.eq_of_mem ha hb, pairwise_of_forall_mem_list⟩

lemma tfae_iff_chain' : tfae l ↔ chain' (=) l :=
iff.symm (chain'_iff_pairwise $ λ a b c, eq.trans)

alias tfae_iff_chain' ↔ list.tfae.chain' list.chain'.tfae

lemma tfae_iff_repeat : tfae l ↔ l = [] ∨ ∃ a n, l = repeat a n :=
begin
  refine ⟨λ h, _, _⟩,
  { cases l with a l, { exact or.inl rfl },
    refine or.inr ⟨a, length (a :: l), eq_repeat'.2 _⟩,
    exact λ b hb, h.eq_of_mem hb (mem_cons_self _ _) },
  { rintro (rfl|⟨a, n, rfl⟩),
    exacts [tfae_nil, tfae_repeat a n] }
end

theorem tfae_cons_of_mem (hb : b ∈ l) :
  tfae (a::l) ↔ (a = b) ∧ tfae l :=
pairwise_cons.trans $ and_congr_left $
  λ hl, ⟨λ h, h _ hb, λ hab c hc, hab.trans $ tfae.eq_of_mem hl hb hc⟩

theorem tfae_cons_cons : tfae (a::b::l) ↔ (a = b) ∧ tfae (b::l) :=
tfae_cons_of_mem (or.inl rfl)

theorem tfae_of_forall (h : ∀ a ∈ l, a = b) : tfae l :=
tfae_iff_forall.2 $ λ a₁ h₁ a₂ h₂, (h _ h₁).trans (h _ h₂).symm

theorem tfae_of_forall' (b : Prop) (l : list Prop) (h : ∀ a ∈ l, a ↔ b) : tfae l :=
tfae_of_forall $ λ a ha, iff_iff_eq.mp (h a ha)

theorem tfae.map (h : tfae l) (f : α → β) : tfae (map f l) :=
h.map f $ λ a b, congr_arg f

theorem tfae.zip_with (ha : tfae la) (hb : tfae lb) (f : α → β → γ) :
  tfae (zip_with f la lb) :=
begin
  simp only [tfae_iff_repeat] at *,
  rcases ha with rfl|⟨a, m, rfl⟩, { left, simp },
  rcases hb with rfl|⟨b, n, rfl⟩, { left, simp },
  exact or.inr ⟨f a b, min m n, zip_with_repeat _ _ _ _ _⟩,
end

theorem tfae_of_cycle [partial_order α] (hle : chain (≤) a l)
  (h : last (a :: l) (cons_ne_nil _ _) ≤ a) : tfae (a::l) :=
begin
  have := hle.pairwise transitive_le,
  refine this.imp₂ (λ a b, le_antisymm) (pairwise_of_forall_mem_list _),
  intros x hx y hy,
  set z := last (a :: l) (cons_ne_nil _ _),
  have hya : y ≤ a := (this.rel_last hy le_rfl).trans h,
  rcases hx with rfl|hx,
  exacts [hya, hya.trans $ rel_of_pairwise_cons this hx]
end

theorem tfae.out {l : list Prop} (h : tfae l) (n₁ n₂) {a b}
  (h₁ : list.nth l n₁ = some a . tactic.interactive.refl)
  (h₂ : list.nth l n₂ = some b . tactic.interactive.refl) :
  a ↔ b :=
iff_of_eq (h.eq_of_mem (list.nth_mem h₁) (list.nth_mem h₂))

end list

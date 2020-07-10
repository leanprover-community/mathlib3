/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon
-/
import data.list.basic

namespace list

/- tfae: The Following (propositions) Are Equivalent -/
def tfae (l : list Prop) : Prop := ∀ x ∈ l, ∀ y ∈ l, x ↔ y

theorem tfae_nil : tfae [] := forall_mem_nil _
theorem tfae_singleton (p) : tfae [p] := by simp [tfae, -eq_iff_iff]

theorem tfae_cons_of_mem {a b} {l : list Prop} (h : b ∈ l) :
  tfae (a::l) ↔ (a ↔ b) ∧ tfae l :=
⟨λ H, ⟨H a (by simp) b (or.inr h), λ p hp q hq, H _ (or.inr hp) _ (or.inr hq)⟩,
begin
   rintro ⟨ab, H⟩ p (rfl | hp) q (rfl | hq),
   { refl },
   { exact ab.trans (H _ h _ hq) },
   { exact (ab.trans (H _ h _ hp)).symm },
   { exact H _ hp _ hq }
end⟩

theorem tfae_cons_cons {a b} {l : list Prop} : tfae (a::b::l) ↔ (a ↔ b) ∧ tfae (b::l) :=
tfae_cons_of_mem (or.inl rfl)

theorem tfae_of_forall (b : Prop) (l : list Prop) (h : ∀ a ∈ l, a ↔ b) : tfae l :=
λ a₁ h₁ a₂ h₂, (h _ h₁).trans (h _ h₂).symm

theorem tfae_of_cycle {a b} {l : list Prop} :
  list.chain (→) a (b::l) → (ilast' b l → a) → tfae (a::b::l) :=
begin
  induction l with c l IH generalizing a b;
    simp only [tfae_cons_cons, tfae_singleton, and_true, chain_cons, chain.nil] at *,
  { intros a b, exact iff.intro a b },
  rintros ⟨ab,⟨bc,ch⟩⟩ la,
  have := IH ⟨bc,ch⟩ (ab ∘ la),
  exact ⟨⟨ab, la ∘ (this.2 c (or.inl rfl) _ (ilast'_mem _ _)).1 ∘ bc⟩, this⟩
end

theorem tfae.out {l} (h : tfae l) (n₁ n₂)
 (h₁ : n₁ < list.length l . tactic.exact_dec_trivial)
 (h₂ : n₂ < list.length l . tactic.exact_dec_trivial) :
  list.nth_le l n₁ h₁ ↔ list.nth_le l n₂ h₂ :=
h _ (list.nth_le_mem _ _ _) _ (list.nth_le_mem _ _ _)

end list

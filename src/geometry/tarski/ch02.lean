import geometry.tarski.axioms
import tactic.rcases
import tactic.show_term

variables {α : Type*} [tarski α]
variables {A B C D E F A' B' C' P Q X Y : α}

namespace tarski

lemma cong.refl (A B : α) : cong A B A B :=
(cong.pseudo_refl _ _).inner_trans (cong.pseudo_refl _ _)

lemma cong.symm (h : cong A B C D) : cong C D A B := h.inner_trans (cong.refl _ _)

lemma cong.trans (h₁ : cong A B C D) (h₂ : cong C D E F) : cong A B E F := h₁.symm.inner_trans h₂

lemma cong.left_comm (h : cong A B C D) : cong B A C D := (cong.pseudo_refl _ _).symm.inner_trans h

lemma cong.right_comm (h : cong A B C D) : cong A B D C := h.symm.left_comm.symm

lemma cong.comm (h : cong A B C D) : cong B A D C := h.left_comm.right_comm

lemma cong.reverse_identity (h : cong A A C D) : C = D := h.symm.identity

lemma cong.trivial_identity (A B : α) : cong A A B B :=
begin
  obtain ⟨E, hE₁, hE₂⟩ := segment_construction A B A A,
  cases hE₂.identity,
  apply hE₂.symm
end

lemma cong.diff (h₁ : cong A B C D) (h₂ : A ≠ B) : C ≠ D :=
by { rintro rfl, apply h₂ h₁.identity }

-- addition of segments
lemma l2_11 (h₁ : betw A B C) (h₂ : betw A' B' C') (h₃ : cong A B A' B') (h₄ : cong B C B' C') :
  cong A C A' C' :=
begin
  rcases eq_or_ne A B with rfl | nAB,
  { cases h₃.reverse_identity,
    apply h₄ },
  apply (five_segment h₃ h₄ (cong.trivial_identity _ _) h₃.comm h₁ h₂ nAB).comm
end

lemma construction_uniqueness (h₁ : Q ≠ A) (h₂ : betw Q A X) (h₃ : cong A X B C) (h₄ : betw Q A Y)
  (h₅ : cong A Y B C) : X = Y :=
(five_segment (cong.refl Q A) (h₃.trans h₅.symm) (cong.refl Q Y) (cong.refl A Y) h₂ h₄ h₁).identity

end tarski

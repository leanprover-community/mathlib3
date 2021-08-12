import tactic.tauto
import geometry.tarski.ch03

variables {α : Type*} [tarski α]
variables {A B C D E F A' B' C' D' P Q X Y : α}

namespace tarski

-- inner five segment
lemma l4_2 (h₁ : betw A B C) (h₁' : betw A' B' C') (h₃ : cong A C A' C') (h₄ : cong B C B' C')
  (h₅ : cong A D A' D') (h₆ : cong C D C' D') : cong B D B' D' :=
begin
  rcases eq_or_ne A C with rfl | nAC,
  { cases h₃.reverse_identity,
    cases h₁'.identity,
    cases h₁.identity,
    apply h₅ },
  obtain ⟨E, hE₁, hE₂⟩ := point_construction_different A C,
  obtain ⟨E', hE'₁, hE'₂⟩ := segment_construction A' C' C E,
  have : cong E D E' D' := five_segment h₃ hE'₂.symm h₅ h₆ hE₁ hE'₁ nAC,
  exact five_segment hE'₂.symm.comm h₄.comm this h₆
    (h₁.left_cancel hE₁).symm (h₁'.left_cancel hE'₁).symm hE₂.symm,
end

lemma l4_3 (h₁ : betw A B C) (h₁' : betw A' B' C') (hAC : cong A C A' C') (hBC : cong B C B' C') :
  cong A B A' B' :=
(l4_2 h₁ h₁' hAC hBC (cong.trivial_identity _ _) hAC.comm).comm

lemma l4_3_1 (h₁ : betw A B C) (h₁' : betw A' B' C') (hBC : cong A B A' B') (hAC : cong A C A' C') :
  cong B C B' C' :=
(l4_3 h₁.symm h₁'.symm hAC.comm hBC.comm).comm

lemma l4_5 (h : betw A B C) (hAC : cong A C A' C') :
  ∃ B', betw A' B' C' ∧ cong A B A' B' ∧ cong A C A' C' ∧ cong B C B' C' :=
begin
  obtain ⟨x', hx'₁, hx'₂⟩ := point_construction_different C' A',
  obtain ⟨B', hB'₁, hB'₂⟩ := segment_construction x' A' A B,
  obtain ⟨C'', hC''₁, hC''₂⟩ := segment_construction x' B' B C,
  have : betw A' B' C'' := hB'₁.left_cancel hC''₁,
  have : C'' = C' := construction_uniqueness hx'₂.symm (hB'₁.left_trans hC''₁)
    (l2_11 this h hB'₂ hC''₂) hx'₁.symm hAC.symm,
  subst C'',
  exact ⟨B', this, hB'₂.symm, hAC, hC''₂.symm⟩,
end

lemma l4_6 (h : betw A B C) (hAB : cong A B A' B') (hAC : cong A C A' C') (hBC : cong B C B' C') :
  betw A' B' C' :=
begin
  obtain ⟨B'', hB''₁, hB''₂, -, hB''₃⟩ := l4_5 h hAC,
  have : cong B'' B'' B'' B' :=
    l4_2 hB''₁ hB''₁ (cong.refl _ _) (cong.refl _ _) (hB''₂.inner_trans hAB)
      (hB''₃.inner_trans hBC).comm,
  cases this.reverse_identity,
  apply hB''₁
end

lemma cong3_betw_eq (ABC : betw A B C) (ABAX : cong A B A X) (BCXC : cong B C X C) :
  X = B :=
(l4_2 ABC ABC (cong.refl _ _) (cong.refl _ _) ABAX BCXC.comm).reverse_identity.symm

/-- `col A B C` means the points are collinear. -/
def col (A B C : α) := betw A B C ∨ betw B C A ∨ betw C A B
lemma col.rotate : col A B C → col B C A := by { dsimp [col], tauto }
lemma col.rotate' (h : col A B C) : col C A B := h.rotate.rotate
lemma col.symm (h : col A B C) : col C B A :=
or.elim3 h (λ h', or.inl h'.symm) (λ h', or.inr (or.inr h'.symm)) (λ h', or.inr (or.inl h'.symm))
lemma col.left_symm (h : col A B C) : col B A C := h.symm.rotate
lemma col.right_symm (h : col A B C) : col A C B := h.rotate.symm

def betw.col (ABC : betw A B C) : col A B C := or.inl ABC

lemma l4_16 (h : col A B C)
  (hAB : cong A B A' B') (hAC : cong A C A' C') (hBC : cong B C B' C')
  (hAD : cong A D A' D') (hBD : cong B D B' D') (nAB : A ≠ B) :
  cong C D C' D' :=
begin
  rcases h with h | h | h,
  { exact five_segment hAB hBC hAD hBD h (l4_6 h hAB hAC hBC) nAB },
  { exact l4_2 h (l4_6 h hBC hAB.comm hAC.comm) hAB.comm hAC.comm hBD hAD },
  { exact five_segment hAB.comm hAC hBD hAD h.symm (l4_6 h.symm hAB.comm hBC hAC) nAB.symm },
end

-- converse of upper_dim
lemma l4_17 (nAB : A ≠ B) (h₁ : col A B C) (h₂ : cong A P A Q) (h₃ : cong B P B Q) :
  cong C P C Q :=
l4_16 h₁ (cong.refl _ _) (cong.refl _ _) (cong.refl _ _) h₂ h₃ nAB

lemma l4_18 (h₁ : A ≠ B) (h₂ : col A B C) (h₃ : cong A C A C') (h₄ : cong B C B C') :
  C = C' :=
(l4_17 h₁ h₂ h₃ h₄).reverse_identity

lemma l4_19 (h₁ : betw A C B) (h₂ : cong A C A C') (h₃ : cong B C B C') :
  C = C' :=
begin
  rcases eq_or_ne A B with rfl | nAB,
  { cases h₁.identity,
    apply h₃.reverse_identity },
  exact l4_18 nAB (col.right_symm (or.inl h₁)) h₂ h₃,
end

end tarski

import tactic.tauto
import geometry.tarski.ch03

variables {α : Type*} [tarski α]
variables {A B C D E F A' B' C' D' E' P Q X Y : α}

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

lemma l4_2_bis (ABC : betw A B C) (ABC' : betw A' B' C') (AB : cong A B A' B') (BC : cong B C B' C')
  (AD : cong A D A' D') (CD : cong C D C' D') : cong B D B' D' :=
l4_2 ABC ABC' (l2_11 ABC ABC' AB BC) BC AD CD

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

-- aka `l4_6`
lemma betw.betw_of_congs (h : betw A B C)
  (hAB : cong A B A' B') (hAC : cong A C A' C') (hBC : cong B C B' C') :
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

@[simp] lemma col_id_left : col A A B := (betw.id_left _ _).col
@[simp] lemma col_id_right : col A B B := (betw.id_right _ _).col
@[simp] lemma col_id_mid : col A B A := col_id_left.rotate

lemma ne12_of_not_col (ABC : ¬ col A B C) : A ≠ B := λ h, ABC (h ▸ col_id_left)
lemma ne13_of_not_col (ABC : ¬ col A B C) : A ≠ C := λ h, ABC (h ▸ col_id_mid)
lemma ne23_of_not_col (ABC : ¬ col A B C) : B ≠ C := λ h, ABC (h ▸ col_id_right)

-- aka `l4_13`
lemma col.col_of_congs (h : col A B C)
  (AB : cong A B A' B') (AC : cong A C A' C') (BC : cong B C B' C') :
  col A' B' C' :=
h.elim3 (λ i, or.inl (i.betw_of_congs AB AC BC))
  (λ i, or.inr (or.inl (i.betw_of_congs BC AB.comm AC.comm)))
  (λ i, or.inr (or.inr (i.betw_of_congs AC.comm BC.comm AB)))

lemma l4_14 (ABC : col A B C) (AB : cong A B A' B') :
  ∃ C', cong A B A' B' ∧ cong A C A' C' ∧ cong B C B' C' :=
begin
  rcases ABC with ABC | BCA | CAB,
  { obtain ⟨C', ABC', BC⟩ := segment_construction A' B' B C,
    exact ⟨C', AB, l2_11 ABC ABC' AB BC.symm, BC.symm⟩ },
  { obtain ⟨C', -, BC, -, CA⟩ := l4_5 BCA AB.comm,
    exact ⟨C', AB, CA.comm, BC⟩ },
  { obtain ⟨C', BAC', AC⟩ := segment_construction B' A' A C,
    exact ⟨C', AB, AC.symm, l2_11 CAB.symm BAC' AB.comm AC.symm⟩ }
end

lemma l4_16 (h : col A B C)
  (AB : cong A B A' B') (AC : cong A C A' C') (BC : cong B C B' C')
  (AD : cong A D A' D') (BD : cong B D B' D') (nAB : A ≠ B) :
  cong C D C' D' :=
begin
  rcases h with h | h | h,
  { exact five_segment AB BC AD BD h (h.betw_of_congs AB AC BC) nAB },
  { exact l4_2 h (h.betw_of_congs BC AB.comm AC.comm) AB.comm AC.comm BD AD },
  { exact five_segment AB.comm AC BD AD h.symm (h.symm.betw_of_congs AB.comm BC AC) nAB.symm },
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

lemma six_segments_inner_betw
  (BAD : betw B A D) (BAD' : betw B' A' D') (BCE : betw B C E) (BCE' : betw B' C' E')
  (BA : cong B A B' A') (BD : cong B D B' D') (BC : cong B C B' C') (BE : cong B E B' E')
  (DE : cong D E D' E') :
  cong A C A' C' :=
begin
  apply (l4_2 BCE BCE' BE (l4_3_1 BCE BCE' BC BE) BA _).comm,
  apply (l4_2 BAD BAD' BD (l4_3_1 BAD BAD' BA BD) BE DE).comm,
end

end tarski

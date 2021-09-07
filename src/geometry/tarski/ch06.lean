import tactic.tauto
import geometry.tarski.ch05

variables {α : Type*} [tarski α]
variables {A B C D E F A' B' C' D' E' P Q X Y : α}

namespace tarski

def out (P A B : α) := A ≠ P ∧ B ≠ P ∧ (betw P A B ∨ betw P B A)

def betw.out (ABC : betw A B C) (nBA : B ≠ A) : out A B C :=
⟨nBA, by { rintro rfl, apply nBA ABC.identity.symm }, or.inl ABC⟩

def out.col (ABC : out A B C) : col A B C :=
ABC.2.2.elim or.inl (λ i, col.right_symm (or.inl i))

lemma l6_2 (nAP : A ≠ P) (nBP : B ≠ P) (nCP : C ≠ P) (APC : betw A P C) :
  betw B P C ↔ out P A B :=
begin
  split,
  { intro BPC,
    exact ⟨nAP, nBP, l5_2 nCP APC.symm BPC.symm⟩ },
  { rintro ⟨-, -, PAB | PBA⟩,
    { apply PAB.symm.trans APC nAP },
    { apply PBA.symm.left_cancel APC } }
end

lemma betw.out_betw (APC : betw A P C) (PAB : out P A B) :
  betw B P C :=
begin
  rcases eq_or_ne C P with rfl | nCP,
  { apply betw.id_right },
  rwa l6_2 PAB.1 PAB.2.1 nCP APC,
end

-- l6_6
lemma out.symm (PAB : out P A B) : out P B A :=
⟨PAB.2.1, PAB.1, PAB.2.2.swap⟩

lemma l6_3_1 (PAB : out P A B) :
  A ≠ P ∧ B ≠ P ∧ ∃ C, C ≠ P ∧ betw A P C ∧ betw B P C :=
begin
  refine ⟨PAB.1, PAB.2.1, _⟩,
  cases PAB.2.2,
  { obtain ⟨C, APC, nPC⟩ := point_construction_different A P,
    exact ⟨C, nPC.symm, APC, h.symm.trans APC PAB.1⟩ },
  { obtain ⟨C, BPC, nPC⟩ := point_construction_different B P,
    exact ⟨C, nPC.symm, h.symm.trans BPC PAB.2.1, BPC⟩ }
end

lemma l6_3_2 (nAP : A ≠ P) (nBP : B ≠ P) (nCP : C ≠ P) (APC : betw A P C) (BPC : betw B P C) :
  out P A B :=
(l6_2 nAP nBP nCP APC).1 BPC

lemma l6_4_1 (PAB : out P A B) : col A P B ∧ ¬ betw A P B :=
begin
  cases PAB.2.2,
  { exact ⟨h.col.left_symm, λ h', PAB.1.symm (h.antisymm_left h')⟩ },
  { exact ⟨h.col.rotate', λ h', PAB.2.1 (h.symm.antisymm_right h')⟩ },
end

-- aka `not_bet_out`
-- aka `l6_4_2`
lemma col.out_of_not_betw (APB : col A P B) (nAPB : ¬ betw A P B) : out P A B :=
begin
  rcases APB with APB | APB,
  { apply (nAPB APB).elim },
  rcases eq_or_ne A P with rfl | nAP,
  { exact (nAPB (betw.id_left _ _)).elim },
  rcases eq_or_ne B P with rfl | nBP,
  { exact (nAPB (betw.id_right _ _)).elim },
  exact ⟨nAP, nBP, or.imp_left betw.symm APB.swap⟩,
end

lemma l6_4 : out P A B ↔ col A P B ∧ ¬ betw A P B :=
⟨λ h, l6_4_1 h, λ ⟨h₁, h₂⟩, h₁.out_of_not_betw h₂⟩

lemma out.trivial (nAP : A ≠ P) : out P A A :=
⟨nAP, nAP, or.inl (betw.id_right _ _)⟩

-- l6_7
lemma out.trans (PAB : out P A B) (PBC : out P B C) : out P A C :=
begin
  refine ⟨PAB.1, PBC.2.1, _⟩,
  rcases PAB.2.2 with PAB | PBA;
  rcases PBC.2.2 with PBC | PCB,
  { exact or.inl (PAB.left_trans PBC) },
  { exact l5_3 PAB PCB },
  { exact l5_1 ‹out P A B›.2.1.symm PBA PBC },
  { exact or.inr (PCB.left_trans PBA) }
end

-- bet_out_out_bet
-- out2_bet_out

lemma l6_11_uniqueness {R : α} (nRA : R ≠ A)
  (AXR : out A X R) (AXBC : cong A X B C) (AYR : out A Y R) (AYBC : cong A Y B C) :
  X = Y :=
begin
  have AXAY : cong A X A Y := AXBC.trans AYBC.symm,
  rcases AXR.2.2 with AXR' | ARX';
  rcases AYR.2.2 with AYR' | ARY',
  { exact l4_19 AXR' AXAY (l4_3 AXR'.symm AYR'.symm (cong.refl R A) AXAY.comm) },
  { exact (AXR'.left_trans ARY').cong AXAY },
  { exact ((AYR'.left_trans ARX').cong AXAY.symm).symm },
  cases l5_1 nRA.symm ARX' ARY',
  { exact h.cong AXAY },
  { exact (h.cong AXAY.symm).symm }
end

lemma l6_11_existence {R : α} (nRA : R ≠ A) (nBC : B ≠ C) :
  ∃ X, out A X R ∧ cong A X B C :=
begin
  obtain ⟨X, ARX, AXBC⟩ := segment_construction_2 B C nRA,
  refine ⟨X, ⟨_, nRA, ARX.symm⟩, AXBC⟩,
  rintro rfl,
  apply nBC AXBC.reverse_identity,
end

lemma segment_construction_3 (nAB : A ≠ B) (nXY : X ≠ Y) :
  ∃ C, out A B C ∧ cong A C X Y :=
begin
  obtain ⟨C, ACB, ACXY⟩ := l6_11_existence nAB.symm nXY,
  exact ⟨_, ACB.symm, ACXY⟩,
end

lemma l6_13_1 (PAB : out P A B) (PAPB : le P A P B) : betw P A B :=
begin
  rcases PAB.2.2 with PAB' | PBA',
  { apply PAB' },
  rcases PAPB with ⟨Y, PYB, PAPY⟩,
  have : out P Y B,
  { refine ⟨_, PAB.2.1, or.inl PYB⟩,
    rintro rfl,
    apply PAB.1.symm PAPY.identity },
  cases l6_11_uniqueness PAB.2.1 this PAPY.symm PAB (cong.refl P A),
  apply PYB
end

lemma l6_13_2 (PAB' : betw P A B) : le P A P B :=
⟨A, PAB', cong.refl _ _⟩

lemma l6_13 (PAB : out P A B) : le P A P B ↔ betw P A B :=
⟨l6_13_1 PAB, l6_13_2⟩

lemma l6_16_1 {P Q S X : α} (nPQ : P ≠ Q) (SPQ : col S P Q) (XPQ : col X P Q) :
  col X P S :=
begin
  rcases SPQ with SPQ | PQS | QSP;
  rcases XPQ with XPQ | PQX | QXP,
  { exact or.inr (or.imp_right betw.symm (l5_2 nPQ.symm SPQ.symm XPQ.symm)) },
  { exact (SPQ.trans' PQX nPQ).symm.col },
  { exact (SPQ.right_cancel QXP.symm).symm.col },
  { exact (XPQ.trans' PQS nPQ).col, },
  { exact or.inr (or.imp_right betw.symm (l5_1 nPQ PQS PQX)) },
  { exact (QXP.symm.left_trans PQS).col.left_symm },
  { exact (XPQ.right_cancel QSP.symm).col },
  { exact (PQX.symm.right_trans QSP).col.right_symm },
  { exact or.inr (or.imp_right betw.symm (l5_3 QSP.symm QXP.symm)) }
end

lemma col.trans (PQA : col P Q A) (PQB : col P Q B) (nPQ : P ≠ Q) : col P A B :=
(l6_16_1 nPQ PQA.rotate' PQB.rotate').rotate

lemma col.trans' (PQA : col P Q A) (PQB : col P Q B) (nPQ : P ≠ Q) : col Q A B :=
PQA.left_symm.trans PQB.left_symm nPQ.symm

-- uniqueness of intersection
lemma l6_21 (ABC : ¬col A B C) (nCD : C ≠ D) (ABP : col A B P) (ABQ : col A B Q)
  (CDP : col C D P) (CDQ : col C D Q) :
  P = Q :=
begin
  by_contra nPQ,
  have nAB : A ≠ B := ne12_of_not_col ABC,
  have CPQ : col C P Q := CDP.trans CDQ nCD,
  have QBC : col Q B C := (ABP.trans' ABQ nAB).symm.trans CPQ.symm (ne.symm nPQ),
  apply ABC,
  rcases eq_or_ne Q B with rfl | nQB,
  { apply (CPQ.symm.trans ABP.rotate (ne.symm nPQ)).rotate' },
  { apply (QBC.left_symm.trans ABQ.rotate nQB.symm).rotate' },
end

lemma col3 (nXY : X ≠ Y) (XYA : col X Y A) (XYB : col X Y B) (XYC : col X Y C) :
  col A B C :=
begin
  rcases eq_or_ne X A with rfl | nXA,
  { apply XYB.trans XYC nXY },
  apply (XYA.trans XYB nXY).trans' (XYA.trans XYC nXY) nXA,
end

lemma exists_not_col {A B : α} (nAB : A ≠ B) : ∃ C, ¬ col A B C :=
begin
  obtain ⟨x₀ : α, x₁, x₂, h₀₁₂ : ¬betw x₀ _ _, h₁₂₀, h₂₀₁⟩ := lower_dim,
  by_cases ABx₀ : col A B x₀,
  { by_cases ABx₁ : col A B x₁,
    { by_cases ABx₂ : col A B x₂,
      have not_col : ¬col x₀ x₁ x₂,
      { simp only [col, not_or_distrib, *, not_false_iff, true_and] },
      { cases not_col (col3 nAB ‹col A B x₀› ‹col A B x₁› ‹col A B x₂›), },
      exact ⟨_, ABx₂⟩ },
    exact ⟨_, ABx₁⟩, },
  exact ⟨_, ABx₀⟩,
end

lemma out.betw_of_out (ABC : out A B C) (CAB : out C A B) : betw A B C :=
((third_point (out.col ABC)).resolve_left (λ i, (l6_4_1 ABC).2 i.symm)).resolve_left (l6_4_1 CAB).2

lemma bet2_le2_le1346 : betw A B C → betw A' B' C' → le A B A' B' → le B C B' C' → le A C A' C' :=
λ h₁ h₂ h₃, betw.le_le h₁ h₂ h₃.comm

-- not_out_bet
lemma col.betw_of_not_out (ABC : col A B C) (BAC : ¬out B A C) : betw A B C :=
by_contradiction (λ i, BAC (ABC.out_of_not_betw i))

-- cong_preserves_bet
lemma betw.betw_of_out_cong {A₀ D₀} (BA'A₀ : betw B A' A₀) (ED'D₀ : out E D' D₀)
  (BA'ED' : cong B A' E D') (BA₀ED₀ : cong B A₀ E D₀) :
  betw E D' D₀ :=
begin
  cases ED'D₀.2.2,
  { assumption },
  cases h.cong ((BA'A₀.le_left.cong BA'ED' BA₀ED₀).antisymm h.le_left).symm,
  apply betw.id_right,
end

-- out_cong_cong
lemma out_cong_cong (BA'A : out B A' A) (ED'D : out E D' D)
  (BA'ED' : cong B A' E D') (BAED : cong B A E D) :
  cong A' A D' D :=
begin
  cases BA'A.2.2 with BA'A BAA',
  { apply l4_3_1 BA'A (BA'A.betw_of_out_cong ED'D BA'ED' BAED) BA'ED' BAED },
  { apply l4_3 BAA'.symm (BAA'.betw_of_out_cong ED'D.symm BAED BA'ED').symm BA'ED'.comm BAED.comm }
end

-- cong3_preserves_out
lemma out.out_of_congs (h : out A B C)
  (AB : cong A B A' B') (AC : cong A C A' C') (BC : cong B C B' C') :
  out A' B' C' :=
begin
  refine ⟨AB.comm.diff h.1, AC.comm.diff h.2.1, _⟩,
  exact or.imp (λ i, betw.betw_of_congs i AB AC BC) (λ i, betw.betw_of_congs i AC AB BC.comm) h.2.2
end

lemma six_segments_out
  (BAD : out B A D) (BAD' : out B' A' D') (BCE : out B C E) (BCE' : out B' C' E')
  (BA : cong B A B' A') (BD : cong B D B' D') (BC : cong B C B' C') (BE : cong B E B' E')
  (AC : cong A C A' C') :
  cong D E D' E' :=
l4_16 BAD.col BA BD (out_cong_cong BAD BAD' BA BD) BE
  (l4_16 BCE.col BC BE (out_cong_cong BCE BCE' BC BE) BA AC.comm BCE.1.symm).comm BAD.1.symm

-- out_bet_out_1
lemma out.out_of_bet (PAC : out P A C) (ABC : betw A B C) : out P A B :=
begin
  rcases eq_or_ne B P with rfl | nBP,
  { apply ((l6_4_1 PAC).2 ABC).elim },
  refine ⟨PAC.1, nBP, _⟩,
  cases PAC.2.2,
  { apply or.inl (h.right_cancel ABC) },
  { apply or.inr (h.right_trans ABC.symm) }
end

end tarski

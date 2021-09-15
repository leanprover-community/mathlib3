import geometry.tarski.ch08

variables {α : Type*} [tarski α]
variables {A B C D E F A' B' C' D' M P Q R S U V X Y : α}

namespace tarski

-- P and Q are on opposite sides of the line A,B
def two_sides (A B P Q : α) := ¬ col P A B ∧ ¬ col Q A B ∧ ∃ T, col T A B ∧ betw P T Q

lemma two_sides.ne12 (h : two_sides A B P Q) : A ≠ B := ne23_of_not_col h.1
lemma two_sides.ne13 (h : two_sides A B P Q) : A ≠ P := (ne12_of_not_col h.1).symm
lemma two_sides.ne14 (h : two_sides A B P Q) : A ≠ Q := (ne12_of_not_col h.2.1).symm
lemma two_sides.ne23 (h : two_sides A B P Q) : B ≠ P := (ne13_of_not_col h.1).symm
lemma two_sides.ne24 (h : two_sides A B P Q) : B ≠ Q := (ne13_of_not_col h.2.1).symm
lemma two_sides.ne34 (h : two_sides A B P Q) : P ≠ Q :=
begin
  rintro rfl,
  obtain ⟨T, TAB, PTP⟩ := h.2.2,
  cases PTP.identity,
  apply h.1 TAB,
end

-- l9_2
lemma two_sides.right_symm (h : two_sides A B P Q) :
  two_sides A B Q P :=
begin
  obtain ⟨nPAB, nQAB, T, TAB, PTQ⟩ := h,
  exact ⟨nQAB, nPAB, T, TAB, PTQ.symm⟩,
end

lemma two_sides.left_symm (h : two_sides A B P Q) :
  two_sides B A P Q :=
begin
  obtain ⟨nPAB, nQAB, T, TAB, PTQ⟩ := h,
  exact ⟨λ i, nPAB i.right_symm, λ i, nQAB i.right_symm, T, TAB.right_symm, PTQ⟩
end

lemma not_two_sides_self : ¬ two_sides P Q A A :=
begin
  rintro ⟨h, _, T, TPQ, ATA⟩,
  cases ATA.identity,
  apply h TPQ,
end

-- If A and B are on the line PQ, and ABC are collinear with A ≠ B, then C is on PQ
lemma col.of_col (APQ : col A P Q) (BPQ : col B P Q) (ABC : col A B C) (nAB : A ≠ B) :
  col C P Q :=
begin
  rcases eq_or_ne P Q with rfl | nPQ,
  { apply col_id_right },
  apply col3 nAB ABC (l6_16_1 nPQ APQ BPQ).rotate'
    (l6_16_1 nPQ.symm APQ.right_symm BPQ.right_symm).rotate',
end

lemma midpoint.two_sides (MAC : midpoint M A C) (MPQ : col M P Q) (nAPQ : ¬ col A P Q) :
  two_sides P Q A C :=
⟨nAPQ, λ h, nAPQ (col.of_col MPQ h MAC.1.col.rotate
  begin
    rintro rfl,
    cases MAC.id,
    apply nAPQ h
  end), M, MPQ, MAC.1⟩

lemma l9_3_aux (PQAC : two_sides P Q A C) (MPQ : col M P Q) (MAC : midpoint M A C)
  (RPQ : col R P Q) (RBA : betw R B A) (nBR : B ≠ R) :
  two_sides P Q B C :=
begin
  obtain ⟨T, BTC, MTR⟩ := inner_pasch RBA MAC.1.symm,
  refine ⟨λ BPQ, PQAC.1 (RPQ.of_col BPQ RBA.col nBR.symm), PQAC.2.1, T, _, BTC⟩,
  rcases eq_or_ne M R with rfl | nMR,
  { cases MTR.identity,
    apply MPQ },
  apply RPQ.of_col MPQ MTR.col.rotate' nMR.symm
end

lemma l9_3 (PQAC : two_sides P Q A C) (MPQ : col M P Q) (MAC : midpoint M A C)
  (RPQ : col R P Q) (RAB : out R A B) :
  two_sides P Q B C :=
begin
  have nPQ : P ≠ Q := ne23_of_not_col PQAC.1,
  have nAR : A ≠ R := RAB.1,
  have nBR : B ≠ R := RAB.2.1,
  have nBPQ : ¬ col B P Q,
  { intro BPQ,
    apply PQAC.1 (RPQ.of_col BPQ RAB.col.right_symm nBR.symm) },
  cases RAB.2.2 with RAB RBA,
  { obtain ⟨B', MBB⟩ := symmetric_point_construction M B,
    obtain ⟨R', MRR⟩ := symmetric_point_construction M R,
    have nCR' : C ≠ R',
    { rintro rfl,
      apply nAR (l7_9 MAC MRR) },
    apply (l9_3_aux _ MPQ MBB.symm _ (RAB.betw_of_midpoints MRR MAC MBB) nCR').right_symm,
    { refine ⟨_, nBPQ, M, MPQ, MBB.symm.1⟩,
      intro BPQ',
      apply nBPQ (MPQ.of_col BPQ' MBB.1.col.rotate _),
      rintro rfl,
      cases MBB.id,
      apply nBPQ BPQ' },
    { rcases eq_or_ne M R with rfl | nMR,
      { cases MRR.id',
        apply MPQ },
      apply MPQ.of_col RPQ MRR.1.col.left_symm nMR } },
  { apply l9_3_aux PQAC MPQ MAC RPQ RBA RAB.2.1 }
end

-- V = C'
lemma l9_4_1_aux (SCRA : le S C R A)
  (PQAC : two_sides P Q A C) (RPQ : col R P Q) (PQAR : perp P Q A R)
  (SPQ : col S P Q) (PQCS : perp P Q C S) (RMS : midpoint M R S) (MUV : midpoint M U V)
  (nRS : R ≠ S) :
  out R U A ↔ out S V C :=
begin
  obtain ⟨B, RBA, SCRB⟩ := id SCRA,
  obtain ⟨nAPQ, nCPQ, T, TPQ, ATC⟩ := id PQAC,
  have CSSR : perp C S S R := (PQCS.col nRS.symm SPQ.rotate RPQ.rotate).symm,
  have ARSR : perp A R S R := (PQAR.col nRS.symm SPQ.rotate RPQ.rotate).symm,
  have SRT : col S R T := col3 (ne23_of_not_col nAPQ) SPQ.rotate RPQ.rotate TPQ.rotate,
  obtain ⟨M', MSR, MCB⟩ := l8_24 CSSR ARSR SRT ATC.symm RBA SCRB,
  cases l7_17_bis RMS MSR,
  clear MSR,
  have nBR : B ≠ R,
  { rintro rfl,
    apply PQCS.ne_right.symm SCRB.identity },
  have : out R U A ↔ out R U B := ⟨λ k, k.trans (RBA.out nBR).symm, λ k, k.trans (RBA.out nBR)⟩,
  rw this,
  split,
  { intro k,
    apply k.out_of_midpoints RMS MUV MCB.symm },
  { intro k,
    apply k.out_of_midpoints RMS.symm MUV.symm MCB }
end

lemma l9_4_1 (PQAC : two_sides P Q A C) (RPQ : col R P Q) (PQAR : perp P Q A R)
  (SPQ : col S P Q) (PQCS : perp P Q C S) (RMS : midpoint M R S) (MUV : midpoint M U V) :
  out R U A ↔ out S V C :=
begin
  obtain ⟨nAPQ, nCPQ, T, TPQ, ATC⟩ := id PQAC,
  have RPQAR : perp_at R P Q A R := PQAR.perp_at_of_col RPQ col_id_mid,
  have SPQCS : perp_at S P Q C S := PQCS.perp_at_of_col SPQ col_id_mid,
  rcases eq_or_ne R S with rfl | nRS,
  { have ART : per A R T := (RPQAR.2.2.2.2 _ _ TPQ col_id_left).symm,
    have CST : per C R T := (SPQCS.2.2.2.2 _ _ TPQ col_id_left).symm,
    cases l8_6 ART CST ATC,
    cases RMS.id'',
    have nCM := PQCS.ne_right,
    split,
    { intro MUA,
      apply l6_3_2 _ PQCS.ne_right MUA.1 MUV.symm.1 (ATC.out_betw MUA.symm).symm,
      rintro rfl,
      apply MUA.1 MUV.id.symm },
    { intro MVC,
      apply l6_3_2 _ PQAR.ne_right MVC.1 MUV.1 (ATC.symm.out_betw MVC.symm).symm,
      rintro rfl,
      apply MVC.1 MUV.id'.symm } },
  cases le.cases S C R A,
  { apply l9_4_1_aux h PQAC RPQ PQAR SPQ PQCS RMS MUV nRS },
  { apply (l9_4_1_aux h PQAC.right_symm SPQ PQCS RPQ PQAR RMS.symm MUV.symm nRS.symm).symm },
end

lemma l9_4_2_aux (SCRA : le S C R A) (PQAC : two_sides P Q A C) (RPQ : col R P Q)
  (PQAR : perp P Q A R) (SPQ : col S P Q) (PQCS : perp P Q C S) (RUA : out R U A)
  (SVC : out S V C) (nRS : R ≠ S) : two_sides P Q U V :=
begin
  obtain ⟨B, RBA, SCRB⟩ := id SCRA,
  obtain ⟨nAPQ, nCPQ, T, TPQ, ATC⟩ := id PQAC,
  have CSSR : perp C S S R := (PQCS.col nRS.symm SPQ.rotate RPQ.rotate).symm,
  have ARSR : perp A R S R := (PQAR.col nRS.symm SPQ.rotate RPQ.rotate).symm,
  have SRT : col S R T := col3 (ne23_of_not_col nAPQ) SPQ.rotate RPQ.rotate TPQ.rotate,
  obtain ⟨M, MSR, MCB⟩ := l8_24 CSSR ARSR SRT ATC.symm RBA SCRB,
  obtain ⟨U', MUU⟩ := symmetric_point_construction M U,
  have SUC : out S U' C,
  { rwa ←l9_4_1 PQAC RPQ PQAR SPQ PQCS MSR.symm MUU },
  have SUV : out S U' V := SUC.trans SVC.symm,
  have MPQ : col M P Q := RPQ.of_col SPQ (MSR.1.col.rotate') nRS,
  have PQUU : two_sides P Q U' U,
  { apply two_sides.right_symm,
    apply MUU.two_sides MPQ,
    intro k,
    apply nAPQ (RPQ.of_col k RUA.col RUA.1.symm) },
  apply (l9_3 PQUU MPQ MUU.symm SPQ SUV).right_symm,
end

lemma l9_4_2 (PQAC : two_sides P Q A C) (RPQ : col R P Q) (PQAR : perp P Q A R)
  (SPQ : col S P Q) (PQCS : perp P Q C S) (RUA : out R U A) (SVC : out S V C) :
  two_sides P Q U V :=
begin
  obtain ⟨nAPQ, nCPQ, T, TPQ, ATC⟩ := id PQAC,
  have RPQAR : perp_at R P Q A R := PQAR.perp_at_of_col RPQ col_id_mid,
  have SPQCS : perp_at S P Q C S := PQCS.perp_at_of_col SPQ col_id_mid,
  rcases eq_or_ne R S with rfl | nRS,
  { have ART : per A R T := (RPQAR.2.2.2.2 _ _ TPQ col_id_left).symm,
    have CST : per C R T := (SPQCS.2.2.2.2 _ _ TPQ col_id_left).symm,
    cases l8_6 ART CST ATC,
    have nCR := PQCS.ne_right,
    refine ⟨λ k, nAPQ _, λ k, nCPQ _, R, TPQ, _⟩,
    { apply TPQ.of_col k RUA.col RUA.1.symm },
    { apply TPQ.of_col k SVC.col SVC.1.symm },
    apply ((ATC.out_betw RUA.symm).symm.out_betw SVC.symm).symm },
 cases le.cases S C R A,
  { apply l9_4_2_aux h PQAC RPQ PQAR SPQ PQCS RUA SVC nRS },
  { apply (l9_4_2_aux h PQAC.right_symm SPQ PQCS RPQ PQAR SVC RUA nRS.symm).right_symm },
end

lemma l9_5 (PQAC : two_sides P Q A C) (RPQ : col R P Q) (RAB : out R A B) :
  two_sides P Q B C :=
begin
  obtain ⟨X, PQX, PQAX⟩ := l8_18_existence (λ k, PQAC.1 k.rotate'),
  obtain ⟨Z, PQZ, PQCZ⟩ := l8_18_existence (λ k, PQAC.2.1 k.rotate'),
  have nBPQ : ¬ col B P Q,
  { intro k,
    apply PQAC.1 (k.of_col RPQ RAB.col.rotate' RAB.2.1) },
  obtain ⟨Y, PQY, PQBY⟩ := l8_18_existence (λ k, nBPQ k.rotate'),
  obtain ⟨M, MXZ⟩ := midpoint_existence X Z,
  obtain ⟨D, MAD⟩ := symmetric_point_construction M A,
  have ZDC : out Z D C,
  { rw ←l9_4_1 PQAC PQX.rotate' PQAX PQZ.rotate' PQCZ MXZ MAD,
    apply PQAX.ne_right.out },
  have PQAD : two_sides P Q A D :=
    l9_4_2 PQAC PQX.rotate' PQAX PQZ.rotate' PQCZ PQAX.ne_right.out ZDC,
  have PQBD : two_sides P Q B D,
  { apply l9_3 PQAD _ MAD RPQ RAB,
    rcases eq_or_ne X Z with rfl | nXZ,
    { cases MXZ.id'',
      apply PQX.rotate' },
    { apply PQX.rotate'.of_col PQZ.rotate' MXZ.1.col.right_symm nXZ } },
  apply l9_4_2 PQBD PQY.rotate' PQBY PQZ.rotate' _ PQBY.ne_right.out ZDC.symm,
  apply (PQCZ.symm.col ZDC.1 ZDC.col.rotate' col_id_right).symm,
end

-- 9.6
lemma outer_pasch (ACP : betw A C P) (BQC : betw B Q C) :
  ∃ X, betw A X B ∧ betw P Q X :=
begin
  by_cases PQC : col P Q C,
  { by_cases PQC' : betw P Q C,
    { exact ⟨A, betw.id_left _ _, PQC'.left_trans ACP.symm⟩ },
    { exact ⟨B, betw.id_right _ _, BQC.symm.out_betw (PQC.out_of_not_betw PQC').symm⟩ } },
  by_cases col P Q B,
  { refine ⟨B, betw.id_right _ _, _⟩,
    cases l6_21 PQC (ne23_of_not_col PQC).symm h col_id_right BQC.symm.col col_id_right,
    apply betw.id_right },
  have PQCB : two_sides P Q C B := ⟨λ k, PQC k.rotate, λ k, h k.rotate, Q, col_id_mid, BQC.symm⟩,
  have PCA : out P C A := betw.out ACP.symm (ne13_of_not_col PQC).symm,
  have PQAB : two_sides P Q A B := l9_5 PQCB col_id_left PCA,
  obtain ⟨nAPQ, nBPQ, X, XPQ, AXB⟩ := id PQAB,
  refine ⟨X, AXB, _⟩,
  obtain ⟨T, CTB, XTP⟩ := inner_pasch ACP.symm AXB.symm,
  have nBC : B ≠ C,
  { rintro rfl,
    apply ne23_of_not_col PQC BQC.identity.symm },
  have : T = Q,
  { apply l6_21 h nBC _ col_id_right CTB.col.rotate' BQC.col.right_symm,
    rcases eq_or_ne P X with rfl | nPX,
    { cases XTP.identity,
      apply col_id_mid },
    apply (XTP.col.right_symm.trans' XPQ nPX.symm).right_symm },
  cases this,
  apply XTP.symm
end

lemma two_sides.col (h : two_sides A B P Q) (nCD : C ≠ D) (CAB : col C A B) (DAB : col D A B) :
  two_sides C D P Q :=
begin
  obtain ⟨PAB, QAB, T, TAB, PTQ⟩ := h,
  refine ⟨_, _, T, _, PTQ⟩,
  { intro PCD,
    apply PAB (CAB.of_col DAB PCD.rotate nCD) },
  { intro QCD,
    apply QAB (CAB.of_col DAB QCD.rotate nCD) },
  apply col3 (ne23_of_not_col PAB) TAB.rotate CAB.rotate DAB.rotate,
end

def one_side (P Q A B : α) := ∃ C, two_sides P Q A C ∧ two_sides P Q B C

-- 9.12
lemma one_side.right_symm : one_side P Q A B → one_side P Q B A
| ⟨_, h⟩ := ⟨_, h.symm⟩

lemma one_side.left_symm : one_side P Q A B → one_side Q P A B
| ⟨C, h₁, h₂⟩ := ⟨C, h₁.left_symm, h₂.left_symm⟩

lemma one_side.not_col_left : one_side P Q A B → ¬ col A P Q
| ⟨_, ⟨h, _⟩, _⟩ := h
lemma one_side.not_col_right (h : one_side P Q A B) : ¬ col B P Q :=
h.right_symm.not_col_left

lemma one_side.col (h : one_side A B P Q) (nCD : C ≠ D) (CAB : col C A B) (DAB : col D A B) :
  one_side C D P Q :=
begin
  obtain ⟨X, ABPX, ABQX⟩ := h,
  exact ⟨X, ABPX.col nCD CAB DAB, ABQX.col nCD CAB DAB⟩,
end

-- 9.8
lemma l9_8 (PQAC : two_sides P Q A C) :
  two_sides P Q B C ↔ one_side P Q A B :=
begin
  split,
  { intro h,
    exact ⟨C, PQAC, h⟩ },
  rintro ⟨D, ⟨nAPQ, nDPQ, X, XPQ, AXD⟩, ⟨nBPQ, -, Y, YPQ, BYD⟩⟩,
  have nAX : A ≠ X,
  { rintro rfl,
    apply nAPQ XPQ },
  have nBX : B ≠ X,
  { rintro rfl,
    apply nBPQ XPQ },
  have nDX : D ≠ X,
  { rintro rfl,
    apply nDPQ XPQ },
  rcases eq_or_ne X Y with rfl | nXY,
  { apply l9_5 PQAC YPQ ((l6_2 nAX nBX nDX AXD).1 BYD) },
  obtain ⟨Z, XZB, YZA⟩ := inner_pasch AXD BYD,
  have nXZ : X ≠ Z,
  { rintro rfl,
    apply nAPQ (YPQ.of_col XPQ YZA.col nXY.symm) },
  have nYZ : Y ≠ Z,
  { rintro rfl,
    apply nBPQ (XPQ.of_col YPQ XZB.col nXY) },
  apply l9_5 (l9_5 PQAC YPQ (YZA.out nYZ.symm).symm) XPQ (XZB.out nXZ.symm),
end

lemma l9_9 (PQAB : two_sides P Q A B) : ¬ one_side P Q A B :=
begin
  rw ←l9_8 PQAB,
  apply not_two_sides_self,
end

lemma l9_10 (nAPQ : ¬ col A P Q) : ∃ C, two_sides P Q A C :=
begin
  obtain ⟨C, APC, nPC⟩ := point_construction_different A P,
  refine ⟨C, nAPQ, _, P, col_id_left, APC⟩,
  intro CPQ,
  apply nAPQ (CPQ.of_col col_id_left APC.symm.col nPC.symm),
end

lemma one_side.refl (nAPQ : ¬ col A P Q) : one_side P Q A A :=
begin
  obtain ⟨C, PQAC⟩ := l9_10 nAPQ,
  exact ⟨C, PQAC, PQAC⟩,
end

lemma one_side.trans (PQAB : one_side P Q A B) (PQBC : one_side P Q B C) :
  one_side P Q A C :=
begin
  obtain ⟨D, PQAD, PQBD⟩ := PQAB,
  exact ⟨D, PQAD, by rwa l9_8 PQBD⟩,
end

lemma l9_17 (PQAB : one_side P Q A B) (ACB : betw A C B) :
  one_side P Q A C :=
begin
  obtain ⟨D, PQAD, PQBD⟩ := id PQAB,
  obtain ⟨nAPQ, nDPQ, X, XPQ, AXD⟩ := id PQAD,
  obtain ⟨nBPQ, -, Y, YPQ, BYD⟩ := id PQBD,
  obtain ⟨T', CTD', YTA'⟩ := inner_pasch ACB BYD.symm,
  obtain ⟨T, XTY, TTD⟩ := inner_pasch AXD.symm YTA',
  have CTD : betw C T D := betw.right_trans CTD' TTD,
  clear_dependent T',
  refine ⟨D, PQAD, λ h, l9_9 ⟨nAPQ, nBPQ, C, h, ACB⟩ PQAB, nDPQ, T, _, CTD⟩,
  rcases eq_or_ne X Y with rfl | nXY,
  { cases XTY.identity,
    assumption },
  { apply XPQ.of_col YPQ XTY.col.right_symm nXY },
end

lemma l9_18 (PXY : col P X Y) (ABP : col A B P) :
  two_sides X Y A B ↔ betw A P B ∧ ¬ col A X Y ∧ ¬ col B X Y :=
begin
  split,
  { rintro ⟨nAXY, nBXY, Q, QXY, AQB⟩,
    refine ⟨_, nAXY, nBXY⟩,
    have nAB : A ≠ B,
    { rintro rfl,
      cases AQB.identity,
      apply nBXY QXY },
    cases l6_21 (λ k, nAXY k.rotate') nAB PXY.rotate QXY.rotate ABP AQB.col.right_symm,
    apply AQB },
  rintro ⟨APB, nAXY, nBXY⟩,
  exact ⟨nAXY, nBXY, _, PXY, APB⟩,
end

lemma l9_19 (PXY : col P X Y) (ABP : col A B P) :
  one_side X Y A B ↔ out P A B ∧ ¬ col A X Y :=
begin
  have : one_side X Y A B ∧ ¬ col A X Y ↔ one_side X Y A B,
  { apply and_iff_left_of_imp,
    rintro ⟨D, ⟨h, _⟩, _⟩,
    apply h },
  rw ←this, clear this,
  apply and_congr_left,
  intro nAXY,
  rcases eq_or_ne B P with rfl | nBP,
  { split,
    { intro h,
      cases h.not_col_right PXY },
    { intro h,
      cases h.2.1 rfl, } },
  have nAP : A ≠ P,
  { rintro rfl,
    apply nAXY PXY },
  obtain ⟨C, PAC⟩ := symmetric_point_construction P A,
  have nCP : C ≠ P,
  { rintro rfl,
    apply nAP PAC.id.symm },
  have nBXY : ¬ col B X Y,
  { intro BXY,
    apply nAXY (BXY.of_col PXY ABP.rotate nBP) },
  have nCXY : ¬ col C X Y,
  { intro CXY,
    apply nAXY (PXY.of_col CXY PAC.1.col.rotate nCP.symm) },
  have XYAC : two_sides X Y A C := ⟨nAXY, nCXY, P, PXY, PAC.1⟩,
  have BCP : col B C P := (ABP.right_symm.trans' PAC.1.col nAP).rotate,
  rw ←l9_8 XYAC,
  rw l9_18 PXY BCP,
  rw l6_2 nAP nBP nCP PAC.1,
  apply and_iff_left_of_imp,
  intro h,
  exact ⟨nBXY, nCXY⟩,
end

lemma out.one_side (PAB : out P A B) (PXY : col P X Y) (nAXY : ¬ col A X Y) :
  one_side X Y A B :=
(l9_19 PXY PAB.col.rotate).2 ⟨PAB, nAXY⟩

-- lemma l9_19 (PXY : col P X Y) (ABP : col A B P) :
--   one_side X Y A B ↔ out P A B ∧ ¬ col A X Y :=

-- lemma l9_31 (PQRS : one_side P Q R S) (PRQS : one_side P R Q S) :
--   two_sides P S Q R :=
-- begin
--   obtain ⟨R', PRR⟩ := symmetric_point_construction P R,
--   have PQRR : two_sides P Q R R',
--   { apply midpoint.two_sides PRR col_id_left,
--     exact λ h, PRQS.not_col_left h.symm },
--   have PQRS' : two_sides P Q R' S,
--   { apply two_sides.right_symm,
--     rwa l9_8 PQRR },
--   obtain ⟨nRPQ', nSPQ, T, TPQ, RTS'⟩ := PQRS',
--   have R'ST : out R' S T,
--   { have := RTS'.out,

--   }
-- end

end tarski

import tactic.tauto
import geometry.tarski.ch06

variables {α : Type*} [tarski α]
variables {A B C D E F A' B' C' D' M P Q R S P' Q' R' S' X Y Z : α}

namespace tarski

def midpoint (M A B : α) := betw A M B ∧ cong A M M B

-- l7_2
lemma midpoint.symm (h : midpoint M A B) : midpoint M B A :=
⟨h.1.symm, h.2.comm.symm⟩

lemma midpoint.id (h : midpoint A B A) : A = B := h.2.identity.symm
lemma midpoint.id' (h : midpoint A A B) : A = B := h.symm.id

-- l7_3
lemma midpoint.id'' (h : midpoint M A A) : M = A := h.1.identity.symm

-- l7_3_2
@[simp] lemma midpoint_refl : midpoint A A A := ⟨betw.id_left _ _, cong.refl _ _⟩

lemma symmetric_point_construction (A P : α) : ∃ P', midpoint A P P' :=
begin
  obtain ⟨E, PAE, AEPA⟩ := segment_construction P A P A,
  exact ⟨E, PAE, AEPA.symm⟩,
end

lemma symmetric_point_uniqueness {P₁ P₂ : α} (h₁ : midpoint P A P₁) (h₂ : midpoint P A P₂) :
  P₁ = P₂ :=
begin
  rcases eq_or_ne A P with rfl | nAP,
  { exact h₁.id'.symm.trans h₂.id' },
  exact construction_uniqueness nAP h₁.1 h₁.2.symm h₂.1 h₂.2.symm,
end

lemma l7_9 (APX : midpoint A P X) (AQX : midpoint A Q X) : P = Q :=
symmetric_point_uniqueness APX.symm AQX.symm

lemma l7_9_bis (APX : midpoint A P X) (AQX : midpoint A X Q) : P = Q :=
l7_9 APX AQX.symm

lemma l7_13_aux (AB : cong A B A B') (AC : cong A C A C') (BAC : betw B A C') (BAC' : betw B' A C) :
  cong B C B' C' :=
begin
  rcases eq_or_ne A B' with rfl | nAB,
  { cases AB.identity,
    apply AC },
  apply (l4_16 BAC'.col AB.symm.comm (l2_11 BAC' BAC AB.symm.comm AC) AC
    (cong.pseudo_refl _ _) AB nAB.symm).comm,
end

-- l7_13
lemma l7_13 (APP : midpoint A P' P) (AQQ : midpoint A Q' Q) :
  cong P Q P' Q' :=
begin
  obtain ⟨X, PPX, PXQA⟩ := segment_construction P' P Q A,
  obtain ⟨X', XPX, PXQA'⟩ := segment_construction X P' Q A,
  obtain ⟨Y, QQY, QYPA⟩ := segment_construction Q' Q P A,
  obtain ⟨Y', YQY, QYPA'⟩ := segment_construction Y Q' P A,
  have APX := APP.1.left_cancel PPX,
  have AQY := AQQ.1.left_cancel QQY,
  have AQY' := AQQ.1.symm.left_cancel (QQY.symm.left_cancel YQY),
  have APX' := APP.1.symm.left_cancel (PPX.symm.left_cancel XPX),
  have AXAY := (l2_11 APX AQY'.symm QYPA'.symm.comm (PXQA.trans AQQ.2.symm.left_comm)).right_comm,
  have AYAX := (l2_11 AQY APX'.symm PXQA'.symm.comm (QYPA.trans APP.2.symm.left_comm)).right_comm,
  have XAX := (APP.1.left_trans PPX).symm.left_trans XPX,
  have YAY := (AQQ.1.left_trans QQY).symm.left_trans YQY,
  have AXAX := l2_11 APX APX' APP.symm.2.left_comm (PXQA.trans PXQA'.symm),
  have AYAY := AYAX.trans (AXAX.symm.trans AXAY),
  have XYYX := l7_13_aux AXAY AYAX XAX YAY.symm,
  have QXQX := l4_2 AQY AQY' AYAY (QYPA.trans QYPA'.symm) AXAX XYYX.left_comm,
  exact l4_2 APX APX' AXAX (PXQA.trans PXQA'.symm) AQQ.symm.2.left_comm QXQX.comm,
end

lemma betw.betw_of_midpoints (PQR : betw P Q R)
  (APP : midpoint A P P') (AQQ : midpoint A Q Q') (ARR : midpoint A R R') :
  betw P' Q' R' :=
PQR.betw_of_congs (l7_13 APP AQQ).symm (l7_13 APP ARR).symm (l7_13 AQQ ARR).symm

lemma l7_16
  (APP : midpoint A P P') (AQQ : midpoint A Q Q') (ARR : midpoint A R R') (ASS : midpoint A S S')
  (PQRS : cong P Q R S) :
  cong P' Q' R' S' :=
(l7_13 APP AQQ).trans (PQRS.trans (l7_13 ARR ASS).symm)

lemma symmetry_preserves_midpoint
  (APP : midpoint A P P') (AQQ : midpoint A Q Q') (ARR : midpoint A R R') (QPR : midpoint Q P R) :
  midpoint Q' P' R' :=
⟨QPR.1.betw_of_midpoints APP AQQ ARR, l7_16 APP AQQ AQQ ARR QPR.2⟩

lemma col.col_of_midpoints (ABC : col A B C) (MAA : midpoint M A A') (MBB : midpoint M B B')
  (MCC : midpoint M C C') :
  col A' B' C' :=
begin
  rcases ABC with ABC | BCA | CAB,
  { apply or.inl (ABC.betw_of_midpoints MAA MBB MCC) },
  { apply or.inr (or.inl (BCA.betw_of_midpoints MBB MCC MAA)) },
  { apply or.inr (or.inr (CAB.betw_of_midpoints MCC MAA MBB)) },
end

lemma out.out_of_midpoints (ABC : out A B C) (MAA : midpoint M A A') (MBB : midpoint M B B')
  (MCC : midpoint M C C') :
  out A' B' C' :=
begin
  rw l6_4 at ABC ⊢,
  refine ⟨ABC.1.col_of_midpoints MBB MAA MCC, λ k, ABC.2 _⟩,
  apply k.betw_of_midpoints MBB.symm MAA.symm MCC.symm,
end

-- midpoints are unique
lemma l7_17 (APP : midpoint A P P') (BPP : midpoint B P P') :
  A = B :=
begin
  obtain ⟨B', ABB⟩ := symmetric_point_construction A B,
  have PBP : betw P B P' := BPP.1,
  have : cong P' B P B' := l7_13 APP ABB.symm,
  have : cong P B P B' := BPP.2.right_comm.trans this,
  have : cong P B P' B' := (l7_13 APP ABB).symm,
  have : cong P' B P' B' := ‹cong P' B P B'›.trans (‹cong P B P B'›.symm.trans ‹cong P B P' B'›),
  cases l4_19 BPP.1 ‹_› ‹_›,
  apply ABB.id'',
end

lemma l7_17_bis (APP : midpoint A P P') (BPP : midpoint B P' P) :
  A = B :=
l7_17 APP BPP.symm

lemma l7_20 (AMB : col A M B) (MAMB : cong M A M B) : A = B ∨ midpoint M A B :=
begin
  by_cases AMB' : betw A M B,
  { exact (or.inr ⟨AMB', MAMB.left_comm⟩) },
  have MAB := AMB.out_of_not_betw AMB',
  left,
  apply l6_11_uniqueness MAB.2.1 MAB MAMB MAB.2.1.out (cong.refl _ _),
end

-- aka `l7_20_bis`
-- aka `cong_col_mid`
lemma cong.midpoint_of_col_of_ne (MAMB : cong M A M B) (AMB : col A M B) (nAB : A ≠ B) :
  midpoint M A B :=
(l7_20 AMB MAMB).resolve_left nAB

lemma l7_21 (ABC : ¬ col A B C) (nBD : B ≠ D) (ABCD : cong A B C D) (BCDA : cong B C D A)
  (APC : col A P C) (BPD : col B P D) :
  midpoint P A C ∧ midpoint P B D :=
begin
  obtain ⟨P', -, BPDP', DPBP'⟩ := l4_14 BPD.right_symm (cong.pseudo_refl B D),
  have DBP : col D B P' := col.col_of_congs BPD.right_symm (cong.pseudo_refl _ _) BPDP' DPBP',
  have PAPC := l4_16 BPD.right_symm (cong.pseudo_refl _ _) BPDP' DPBP' ABCD.comm BCDA.symm nBD,
  have PCPA := l4_16 BPD.right_symm (cong.pseudo_refl _ _) BPDP' DPBP' BCDA ABCD.comm.symm nBD,
  have CPA := col.col_of_congs APC PAPC.comm (cong.pseudo_refl _ _) PCPA,
  have : P = P' :=
    l6_21 (λ i, ABC i.right_symm) nBD APC.right_symm CPA.rotate' BPD.right_symm DBP.left_symm,
  cases this,
  have : A ≠ C := ne13_of_not_col ABC,
  exact ⟨PCPA.symm.midpoint_of_col_of_ne APC ‹A ≠ C›, BPDP'.comm.midpoint_of_col_of_ne BPD nBD⟩,
end

lemma l7_22_aux {A₁ A₂ B₁ B₂ C M₁ M₂ : α} (AC : betw A₁ C A₂) (BC : betw B₁ C B₂)
  (CAB₁ : cong C A₁ C B₁) (CAB₂ : cong C A₂ C B₂)
  (hM₁ : midpoint M₁ A₁ B₁) (hM₂ : midpoint M₂ A₂ B₂) (h : le C A₁ C A₂) :
  betw M₁ C M₂ :=
begin
  rcases eq_or_ne A₁ C with rfl | nA₁C,
  { cases CAB₁.reverse_identity,
    cases hM₁.id'',
    apply betw.id_left },
  have nA₂C : A₂ ≠ C,
  { rintro rfl,
    apply nA₁C,
    apply h.zero.symm },
  obtain ⟨A, CAA⟩ := symmetric_point_construction C A₂,
  obtain ⟨B, CBB⟩ := symmetric_point_construction C B₂,
  obtain ⟨M, CMM⟩ := symmetric_point_construction C M₂,
  have MAB : midpoint M A B := symmetry_preserves_midpoint CAA CMM CBB hM₂,
  have CACB : cong C A C B := CAA.2.symm.right_comm.trans (CAB₂.trans CBB.2.left_comm),
  have CA : le C A₁ C A := h.cong (cong.refl _ _) CAA.2.left_comm,
  have CB : le C B₁ C B := CA.cong CAB₁ CACB,
  have nAC : A ≠ C,
  { rintro rfl,
    apply nA₁C,
    apply CA.zero.symm },
  have nBC : B ≠ C,
  { rintro rfl,
    cases CBB.id,
    apply nA₂C CAB₂.identity.symm },
  have CAA' : out C A₁ A := l6_3_2 nA₁C nAC nA₂C AC CAA.symm.1,
  have CAA'' : betw C A₁ A := l6_13_1 CAA' CA,
  have CBB' : out C B₁ B := l6_3_2 (CAB₁.comm.diff nA₁C) nBC (CAB₂.comm.diff nA₂C) BC CBB.symm.1,
  have CBB'' : betw C B₁ B := l6_13_1 CBB' CB,
  obtain ⟨Q, MQC, AQB⟩ := l3_17 CAA''.symm CBB''.symm MAB.1,
  have A₁QB₁Q := six_segments_inner_betw CAA'' CBB'' MQC.symm MQC.symm CAB₁ CACB (cong.refl _ _)
    (cong.refl _ _) MAB.2.right_comm,
  cases l7_17 hM₁ ⟨AQB, A₁QB₁Q.right_comm⟩,
  apply (CMM.1.right_cancel MQC.symm).symm,
end

lemma l7_22 {A₁ A₂ B₁ B₂ C M₁ M₂ : α} (AC : betw A₁ C A₂) (BC : betw B₁ C B₂)
  (CAB₁ : cong C A₁ C B₁) (CAB₂ : cong C A₂ C B₂)
  (hM₁ : midpoint M₁ A₁ B₁) (hM₂ : midpoint M₂ A₂ B₂) :
  betw M₁ C M₂ :=
begin
  cases le.cases C A₁ C A₂,
  { apply l7_22_aux AC BC CAB₁ CAB₂ hM₁ hM₂ h },
  { apply (l7_22_aux AC.symm BC.symm CAB₂ CAB₁ hM₂ hM₁ h).symm }
end

lemma l7_25 (CACB : cong C A C B) : ∃ X, midpoint X A B :=
begin
  by_cases ABC : col A B C,
  { rcases l7_20 ABC.right_symm CACB with rfl | CAB,
    { exact ⟨A, midpoint_refl⟩ },
    { exact ⟨_, CAB⟩ } },
  obtain ⟨P, CAP, nAP⟩ := point_construction_different C A,
  obtain ⟨Q, CBQ, BQAP⟩ := segment_construction C B A P,
  obtain ⟨R, ARQ, BRP⟩ := inner_pasch CAP.symm CBQ.symm,
  obtain ⟨X, AXB, RXC⟩ := inner_pasch CAP BRP,
  refine ⟨X, AXB, _⟩,
  apply cong.left_comm,
  suffices : cong R A R B,
  { rcases eq_or_ne R C with rfl | nRC,
    { cases RXC.identity,
      apply CACB },
    apply l4_17 nRC RXC.col.right_symm this CACB },
  have PBQA := five_segment CACB BQAP.symm CACB.symm (cong.pseudo_refl _ _) CAP CBQ
    (ne13_of_not_col ABC).symm,
  obtain ⟨R', ARQ', BRAR, BPAQ, RPRQ⟩ := l4_5 BRP PBQA.comm,
  have RARB : cong R A R' B := l4_2 BRP ARQ' PBQA.comm RPRQ (cong.pseudo_refl _ _) BQAP.comm.symm,
  have RQRP : cong R Q R' P := l4_2 BRP ARQ' BPAQ RPRQ BQAP (cong.pseudo_refl _ _),
  have BRP' : col B R' P := ARQ.col.col_of_congs RARB.comm PBQA.comm.symm RQRP,
  suffices : R = R',
  { subst R',
    apply RARB },
  have nBP : B ≠ P,
  { rintro rfl,
    apply ABC CAP.col.rotate },
  apply l6_21 _ nBP ARQ.col.right_symm ARQ'.col.right_symm BRP.col.right_symm BRP'.right_symm,
  intro AQB,
  apply ABC,
  have BPA := AQB.col_of_congs BPAQ.symm (cong.pseudo_refl _ _) BQAP.comm,
  apply (CAP.col.rotate.trans BPA.symm nAP).right_symm,
end

end tarski

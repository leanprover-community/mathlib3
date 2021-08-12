import geometry.tarski.ch04

variables {α : Type*} [tarski α]
variables {A B C D E F A' B' C' D' P Q X Y : α}

namespace tarski

def le (A B C D : α) := ∃ E, betw C E D ∧ cong A B C E
def ge (A B C D : α) := le C D A B
def lt (A B C D : α) := le A B C D ∧ ¬cong A B C D
def gt (A B C D : α) := lt C D A B

lemma l5_1 (nAB : A ≠ B) (h₁ : betw A B C) (h₂ : betw A B D) :
  betw A C D ∨ betw A D C :=
begin
  obtain ⟨C', hC'₁, hC'₂⟩ := segment_construction A D C D,
  obtain ⟨D', hD'₁, hD'₂⟩ := segment_construction A C C D,
  obtain ⟨B', hB'₁, hB'₂⟩ := segment_construction A C' C B,
  obtain ⟨B'', hB''₁, hB''₂⟩ := segment_construction A D' D B,
  have C'B'CB := l2_11 (h₂.left_cancel hC'₁) (hB''₁.symm.right_cancel hD'₁.symm) hB''₂.symm.comm
    (hC'₂.trans hD'₂.symm.right_comm),
  have BB'B'B : cong B B' B'' B,
  { apply l2_11 _ _ C'B'CB hB'₂,
    { rcases eq_or_ne B D with rfl | nBD,
      { apply hC'₁.left_cancel hB'₁ },
      { apply (h₂.left_trans hC'₁).left_cancel hB'₁ } },
    { rcases eq_or_ne D' C with rfl | nCD',
      { apply (h₁.left_cancel hB''₁).symm },
      { apply (hD'₁.left_cancel hB''₁).symm.trans (h₁.left_cancel hD'₁).symm nCD' } } },
  have : B'' = B' :=
    construction_uniqueness nAB ((h₁.left_trans hD'₁).left_trans hB''₁) (cong.refl B B'')
      ((h₂.left_trans hC'₁).left_trans hB'₁) BB'B'B.right_comm,
  subst B'',
  rcases eq_or_ne B C with rfl | nBC,
  { left,
    apply h₂ },
  have CD'C'D := (hD'₂.trans hC'₂.symm.right_comm),
  have BCD' := h₁.left_cancel hD'₁,
  have D'C'DC := l4_16 (or.inl BCD') hB'₂.symm.comm (l2_11 BCD' (hC'₁.left_cancel hB'₁).symm
    hB'₂.symm.comm CD'C'D) CD'C'D ‹cong B C' B' C› (cong.pseudo_refl _ _) nBC,
  obtain ⟨E, hE₁, hE₂⟩ := inner_pasch hD'₁.symm hC'₁.symm,
  have ECEC' := l4_2 hE₂ hE₂ (cong.refl _ _) (cong.refl _ _) hC'₂.symm.left_comm
    (hD'₂.left_comm.trans D'C'DC.symm.left_comm),
  have EDED' := l4_2 hE₁ hE₁ (cong.refl _ _) (cong.refl _ _) hD'₂.symm
    (hC'₂.left_comm.trans D'C'DC.comm.symm),
  rcases eq_or_ne C C' with rfl | nCC',
  { right,
    apply hC'₁ },
  have nCD' : C ≠ D',
  { rintro rfl,
    cases hD'₂.reverse_identity,
    apply nCC' hC'₂.identity },
  obtain ⟨P, hP₁, hP₂⟩ := segment_construction C' C C D',
  obtain ⟨R, hR₁, hR₂⟩ := segment_construction D' C C E,
  obtain ⟨Q, hQ₁, hQ₂⟩ := segment_construction P R R P,
  have RPED' : cong R P E D' := l4_16 (or.inl hR₁) hP₂.symm.comm
    (l2_11 hR₁ (hP₁.symm.right_cancel hE₁) hP₂.symm.comm hR₂) hR₂ (cong.pseudo_refl _ _) hP₂
    nCD'.symm,
  have RQED : cong R Q E D := (hQ₂.trans RPED').trans EDED'.symm,
  rcases eq_or_ne D' E with rfl | nD'E,
  { cases EDED'.identity,
    left,
    assumption },
  have DCQC := l4_16 (or.inl hE₂.symm) RPED'.symm.comm (l2_11 hE₂.symm hQ₁ RPED'.symm.comm
    RQED.symm) RQED.symm hP₂.symm.comm hR₂.symm.comm nD'E,
  have CPCQ : cong C P C Q := hP₂.trans (hD'₂.trans DCQC.comm),
  have nRC : R ≠ C,
  { rintro rfl,
    cases hR₂.reverse_identity,
    apply nCC' ECEC'.reverse_identity },
  have D'PD'Q := l4_17 nRC (col.symm (or.inl hR₁)) hQ₂.symm CPCQ,
  have BPBQ := l4_17 nCD' (col.rotate (or.inl BCD')) CPCQ D'PD'Q,
  have B'PB'Q := l4_17 nCD' (or.inl (hD'₁.left_cancel hB''₁)) CPCQ D'PD'Q,
  rcases eq_or_ne B B' with rfl | nBB',
  { cases betw.antisymm_right (h₁.left_trans hD'₁) hB''₁,
    apply (nBC (BCD'.identity)).elim },
  have C'PC'Q : cong C' P C' Q,
  { apply l4_17 nBB' _ BPBQ B'PB'Q,
    apply col.right_symm,
    left,
    apply (h₂.left_trans hC'₁).left_cancel ‹betw A C' B'› },
  have : cong P P P Q := l4_17 nCC' (or.inr (or.inr hP₁.symm)) CPCQ C'PC'Q,
  cases this.reverse_identity,
  cases hQ₁.identity,
  apply (nD'E.symm RPED'.reverse_identity).elim,
end

lemma l5_2 (nAB : A ≠ B) (ABC : betw A B C) (ABD : betw A B D) :
  betw B C D ∨ betw B D C :=
or.imp ABC.left_cancel ABD.left_cancel (l5_1 nAB ABC ABD)

lemma segment_construction_2 (B C : α) (nAQ : A ≠ Q) :
  ∃ X, (betw Q A X ∨ betw Q X A) ∧ cong Q X B C :=
begin
  obtain ⟨A', AQA', QA'AQ⟩ := segment_construction A Q A Q,
  obtain ⟨X, A'QX, QXBC⟩ := segment_construction A' Q B C,
  have : A' ≠ Q,
  { rintro rfl,
    apply nAQ (QA'AQ.reverse_identity) },
  refine ⟨X, l5_2 ‹A' ≠ Q› AQA'.symm A'QX, QXBC⟩,
end

lemma l5_3 (ABD : betw A B D) (ACD : betw A C D) : betw A B C ∨ betw A C B :=
begin
  obtain ⟨P, DAP, nAP⟩ := point_construction_different D A,
  apply l5_2 nAP.symm (DAP.symm.right_cancel ABD) (DAP.symm.right_cancel ACD),
end

lemma l5_5_1 (h : le A B C D) : ∃ X, betw A B X ∧ cong A X C D :=
begin
  rcases h with ⟨P, CPD, ABCP⟩,
  obtain ⟨X, ABX, BXPD⟩ := segment_construction A B P D,
  refine ⟨X, ABX, l2_11 ABX CPD ABCP BXPD⟩,
end

lemma l5_5_2 {X : α} (ABX : betw A B X) (AXCD : cong A X C D) : le A B C D :=
begin
  obtain ⟨Y, CYD, ABCY, _, _⟩ := l4_5 ABX AXCD,
  exact ⟨Y, CYD, ABCY⟩,
end

lemma l5_5 : le A B C D ↔ ∃ X, betw A B X ∧ cong A X C D :=
⟨l5_5_1, λ ⟨X, h₁, h₂⟩, l5_5_2 h₁ h₂⟩

lemma l5_6 (ABCD : le A B C D) (ABA'B' : cong A B A' B') (CDC'D' : cong C D C' D') :
  le A' B' C' D' :=
begin
  rcases ABCD with ⟨E, CED, ABCE⟩,
  obtain ⟨E', C'E'D', CEC'E', -, EDE'D'⟩ := l4_5 CED CDC'D',
  exact ⟨E', C'E'D', ABA'B'.inner_trans (ABCE.trans CEC'E')⟩,
end

lemma le.refl (A B : α) : le A B A B := ⟨B, betw.id_right _ _, cong.refl _ _⟩

lemma le.trans (ABCD : le A B C D) (CDEF : le C D E F) : le A B E F :=
begin
  obtain ⟨X, CXD, ABCX⟩ := ABCD,
  obtain ⟨Y, EYF, CDEY⟩ := CDEF,
  obtain ⟨Z, EZY, CXEZ, _, _⟩ := l4_5 CXD CDEY,
  exact ⟨Z, EZY.left_trans EYF, ABCX.trans CXEZ⟩,
end

lemma betw.cong (ACB : betw A C B) (ACAB : cong A C A B) : C = B :=
ACB.antisymm_right (l4_6 ACB ACAB ACAB.symm (cong.pseudo_refl _ _))

lemma betw.cong' (ADB : betw A D B) (AEB : betw A E B) (ADAE : cong A D A E) : D = E :=
cong3_betw_eq AEB ADAE.symm
  (l4_2 AEB.symm ADB.symm (cong.refl _ _) ADAE.comm.symm (cong.refl _ _) (cong.refl _ _))

lemma betw.cong'' (nAB : A ≠ B) (ABD : betw A B D) (ABE : betw A B E) (BDBE : cong B D B E) :
  D = E :=
(l5_2 nAB ABD ABE).elim (λ h, h.cong BDBE) (λ h, (h.cong BDBE.symm).symm)

lemma le.antisymm (ABCD : le A B C D) (CDAB : le C D A B) : cong A B C D :=
begin
  obtain ⟨T, CDT, CTAB⟩ := l5_5_1 CDAB,
  obtain ⟨Y, CYD, ABCY⟩ := ABCD,
  have CYCT : cong C Y C T := (CTAB.trans ABCY).symm,
  have CYT : betw C Y T := CYD.left_trans CDT,
  cases betw.cong CYT CYCT,
  cases betw.antisymm_right CDT CYD,
  apply ABCY
end

lemma le.trivial : le A A C D :=
⟨C, betw.id_left _ _, cong.trivial_identity _ _⟩

lemma le.cases (A B C D : α) : le A B C D ∨ le C D A B :=
begin
  rcases eq_or_ne A B with rfl | nAB,
  { left,
    apply le.trivial },
  { obtain ⟨X, hX, AXCD⟩ := segment_construction_2 C D nAB.symm,
    exact or.imp (λ h, l5_5_2 h AXCD) (λ h, ⟨_, h, AXCD.symm⟩) hX },
end

lemma le.zero (h : le A B C C) : A = B := (h.antisymm le.trivial).identity

lemma lt.diff (h : lt A B C D) : C ≠ D :=
begin
  rintro rfl,
  cases le.zero h.1,
  apply h.2 (cong.trivial_identity _ _),
end

lemma betw.cong_eq (ABC : betw A B C) (ACD : betw A C D) (BCAD : cong B C A D) :
  C = D ∧ A = B :=
begin
  have : C = D,
  { apply betw.cong ACD (le.antisymm (l5_5_2 ACD (cong.refl _ _)) _),
    apply l5_6 (l5_5_2 ABC.symm (cong.refl _ _)) BCAD.left_comm (cong.pseudo_refl _ _) },
  subst D,
  exact ⟨rfl, (ABC.symm.cong BCAD.comm).symm⟩,
end

lemma cong.le (h : cong A B C D) : le A B C D :=
⟨D, betw.id_right _ _, h⟩

lemma le.left_comm (h : le A B C D) : le B A C D :=
(cong.pseudo_refl _ _).le.trans h

lemma le.right_comm (h : le A B C D) : le A B D C :=
le.trans h (cong.pseudo_refl _ _).le

lemma le.comm (h : le A B C D) : le B A D C := h.right_comm.left_comm

lemma lt.right_comm (h : lt A B C D) : lt A B D C := ⟨h.1.right_comm, λ i, h.2 i.right_comm⟩
lemma lt.left_comm (h : lt A B C D) : lt B A C D := ⟨h.1.left_comm, λ i, h.2 i.left_comm⟩
lemma lt.comm (h : lt A B C D) : lt B A D C := h.left_comm.right_comm

lemma cong.lt_lt (ABCD : lt A B C D) (ABA'B' : cong A B A' B') (CDC'D' : cong C D C' D') :
  lt A' B' C' D' :=
⟨l5_6 ABCD.1 ‹_› ‹_›, λ i, ABCD.2 (ABA'B'.trans (i.trans CDC'D'.symm))⟩

lemma fourth_point (nAB : A ≠ B) (nBC : B ≠ C) (ABP : col A B P) (ABC : betw A B C) :
  betw P A B ∨ betw A P B ∨ betw B P C ∨ betw B C P :=
begin
  rcases ABP with ABP | BPA | PAB,
  { exact or.inr (or.inr (l5_2 nAB ABC ABP).symm) },
  { exact or.inr (or.inl BPA.symm) },
  { exact or.inl PAB }
end

lemma third_point (ABP : col A B P) : betw P A B ∨ betw A P B ∨ betw A B P :=
begin
  rcases ABP with ABP | BPA | PAB,
  { exact or.inr (or.inr ABP) },
  { exact or.inr (or.inl BPA.symm) },
  { exact or.inl PAB }
end

lemma l5_12_a (ABC : betw A B C) : le A B A C ∧ le B C A C :=
⟨⟨B, ABC, cong.refl _ _⟩, le.comm ⟨B, ABC.symm, cong.refl _ _⟩⟩

lemma betw.le_left (ABC : betw A B C) : le A B A C := (l5_12_a ABC).1
lemma betw.le_right (ABC : betw A B C) : le B C A C := (l5_12_a ABC).2

lemma betw.lt_left (ABC : betw A B C) (nBC : B ≠ C) : lt A B A C :=
⟨ABC.le_left, λ i, nBC (ABC.cong i)⟩
lemma betw.lt_right (ABC : betw A B C) (nAB : A ≠ B) : lt B C A C :=
(ABC.symm.lt_left nAB.symm).comm

lemma l5_12_b (ABC : col A B C) (ABAC : le A B A C) (BCAC : le B C A C) :
  betw A B C :=
begin
  rcases ABC with ABC | BCA | CAB,
  { apply ABC },
  { cases BCA.symm.cong (BCA.le_right.comm.antisymm ABAC),
    apply betw.id_right },
  { cases betw.cong CAB (CAB.symm.le_right.antisymm BCAC).comm,
    apply betw.id_left },
end

lemma betw.le_eq (ABC : betw A B C) (ACBC : le A C B C) : A = B :=
(ABC.symm.cong ((l5_5_2 ABC.symm (cong.refl _ _)).antisymm ACBC.comm)).symm

lemma trichotomy (A B C D : α) : lt A B C D ∨ cong A B C D ∨ gt A B C D :=
begin
  by_cases eq : cong A B C D,
  { exact or.inr (or.inl eq) },
  rcases le.cases A B C D with leq | leq,
  { exact or.inl ⟨leq, eq⟩ },
  { exact or.inr (or.inr ⟨leq, λ i, eq i.symm⟩) }
end

lemma lt.le (h : lt A B C D) : le A B C D := h.1

lemma le.lt_trans (ABCD : le A B C D) (CDEF : lt C D E F) : lt A B E F :=
⟨ABCD.trans CDEF.1, λ i, CDEF.2 (CDEF.1.antisymm (i.symm.le.trans ABCD))⟩

lemma lt.trans_le (ABCD : lt A B C D) (CDEF : le C D E F) : lt A B E F :=
⟨ABCD.1.trans CDEF, λ i, ABCD.2 (ABCD.1.antisymm (CDEF.trans i.symm.le))⟩

lemma lt.trans (ABCD : lt A B C D) (CDEF : lt C D E F) : lt A B E F :=
ABCD.trans_le CDEF.1

lemma lt.asymm (A B : α) : ¬lt A B A B :=
λ i, i.2 (cong.refl _ _)

lemma betw.le_le {O o A B a b : α} (aob : betw a o b) (AOB : betw A O B)
  (oaOA : le o a O A) (obOB : le o b O B) : le a b A B :=
begin
  rcases eq_or_ne A O with rfl | nAO,
  { cases oaOA.zero,
    apply obOB },
  rcases eq_or_ne B O with rfl | nBO,
  { cases obOB.zero,
    apply oaOA.comm },
  obtain ⟨b', AOb', Ob'bo⟩ := segment_construction A O b o,
  obtain ⟨a', BOa', Oa'ao⟩ := segment_construction B O a o,
  obtain ⟨a'', Oa'A, oaO'a'⟩ := oaOA,
  cases construction_uniqueness nBO BOa' Oa'ao (AOB.symm.right_cancel Oa'A) oaO'a'.symm.right_comm,
  have : le B a' B A := ⟨a', AOB.symm.right_trans Oa'A, cong.refl _ _⟩,
  obtain ⟨b'', Ob'B, obO'b'⟩ := obOB,
  cases construction_uniqueness nAO AOb' Ob'bo (AOB.right_cancel Ob'B) obO'b'.symm.right_comm,
  have a'b'a'B : le a' b' a' B := ⟨b', BOa'.symm.right_trans ‹betw O b' B›, cong.refl _ _⟩,
  apply l5_6 (a'b'a'B.trans ‹le B a' B A›.comm) _ (cong.refl _ _),
  apply l2_11 (Oa'A.symm.left_cancel AOb') aob Oa'ao.left_comm obO'b'.symm,
end

end tarski

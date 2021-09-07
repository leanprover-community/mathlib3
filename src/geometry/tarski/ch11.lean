import tactic.tauto
import geometry.tarski.ch10

variables {α : Type*} [tarski α]
variables {A B C D E F A' B' C' D' E' F' A'' B'' C'' P Q P' X Y : α}

namespace tarski

structure cong_angle (A B C D E F : α) : Prop :=
(nAB : A ≠ B)
(nCB : C ≠ B)
(nDE : D ≠ E)
(nFE : F ≠ E)
(ex : ∃ A' C' D' F',
        betw B A A' ∧ cong A A' E D ∧
        betw B C C' ∧ cong C C' E F ∧
        betw E D D' ∧ cong D D' B A ∧
        betw E F F' ∧ cong F F' B C ∧
        cong A' C' D' F')

lemma l11_aux' (BA'A : out B A' A) (ED'D : out E D' D)
  (BA'ED' : cong B A' E D') (BAED : cong B A E D) :
  cong A' A D' D :=
out_cong_cong BA'A ED'D BA'ED' BAED

lemma l11_aux (BAA' : betw B A A') (EDD' : betw E D D')
  (AA'ED : cong A A' E D) (DD'BA : cong D D' B A) :
  cong B A' E D' :=
(l2_11 BAA' EDD'.symm DD'BA.symm.right_comm AA'ED.right_comm).right_comm

-- a more general way to show `cong_angle`: `A ≠ B ∧ betw B A A'` is generalised to `out B A' A`
lemma l11_3_bis (BA'A : out B A' A) (BC'C : out B C' C) (ED'D : out E D' D) (EF'F : out E F' F)
  (A'BD'E : cong A' B D' E) (BC'EF' : cong B C' E F') (A'C'D'F' : cong A' C' D' F') :
  cong_angle A B C D E F :=
begin
  obtain ⟨A₀, BAA₀, AA₀ED⟩ := segment_construction B A E D,
  obtain ⟨C₀, BCC₀, CC₀EF⟩ := segment_construction B C E F,
  obtain ⟨D₀, EDD₀, DD₀BA⟩ := segment_construction E D B A,
  obtain ⟨F₀, EFF₀, FF₀BC⟩ := segment_construction E F B C,
  have BC₀EF₀ : cong B C₀ E F₀ := l11_aux BCC₀ EFF₀ CC₀EF FF₀BC,
  have BA₀ED₀ : cong B A₀ E D₀ := l11_aux BAA₀ EDD₀ AA₀ED DD₀BA,
  have BC'C₀ : out B C' C₀ := BC'C.trans (BCC₀.out BC'C.2.1),
  have : cong C₀ A' F₀ D' := l4_16 BC'C₀.col BC'EF' BC₀EF₀
      (l11_aux' BC'C₀ (EF'F.trans (EFF₀.out EF'F.2.1)) BC'EF' BC₀EF₀)
      A'BD'E.comm A'C'D'F'.comm BC'C.1.symm,
  have BA'A₀ : out B A' A₀ := BA'A.trans (BAA₀.out BA'A.2.1),
  have : cong A₀ C₀ D₀ F₀ := l4_16 BA'A₀.col A'BD'E.comm BA₀ED₀
    (l11_aux' BA'A₀ (ED'D.trans (EDD₀.out ED'D.2.1)) A'BD'E.comm BA₀ED₀)
    BC₀EF₀ this.comm BA'A.1.symm,
  refine ⟨BA'A.2.1, BC'C.2.1, ED'D.2.1, EF'F.2.1, A₀, C₀, D₀, F₀, _, _, _, _, _, _, _, _, _⟩;
  assumption
end

lemma l11_3 :
  cong_angle A B C D E F ↔
    ∃ A' C' D' F', out B A' A ∧ out B C' C ∧ out E D' D ∧ out E F' F ∧
      cong A' B D' E ∧ cong B C' E F' ∧ cong A' C' D' F' :=
begin
  split,
  { rintro ⟨nAB, nCB, nDE, nFE, A', C', D', F', BAA, AAED, BCC, CCEF, EDD, DDBA, EFF, FFBC, ACDF⟩,
    refine ⟨A', C', D', F',
      (BAA.out nAB).symm, (BCC.out nCB).symm, (EDD.out nDE).symm, (EFF.out nFE).symm,
        _, _, ACDF⟩,
    apply (l2_11 BAA EDD.symm DDBA.left_comm.symm AAED.right_comm).left_comm,
    apply (l2_11 BCC EFF.symm FFBC.symm.right_comm CCEF.right_comm).right_comm },
  { rintro ⟨A', C', D', F', BAA, BCC, EDD, EFF, ABDE, BCEF, ACDF⟩,
    apply l11_3_bis BAA BCC EDD EFF ABDE BCEF ACDF }
end

lemma l11_4_2 (nAB : A ≠ B) (nCB : C ≠ B) (nDE : D ≠ E) (nFE : F ≠ E)
  (h : ∀ ⦃A' C' D' F'⦄, out B A' A → out B C' C → out E D' D → out E F' F →
    cong B A' E D' → cong B C' E F' → cong A' C' D' F') :
  cong_angle A B C D E F :=
begin
  obtain ⟨A', BAA', AA'ED⟩ := segment_construction B A E D,
  obtain ⟨C', BCC', CC'FE⟩ := segment_construction B C F E,
  obtain ⟨D', EDD', DD'AB⟩ := segment_construction E D A B,
  obtain ⟨F', EFF', FF'BC⟩ := segment_construction E F B C,
  have ABDE : cong A' B D' E := (l2_11 BAA'.symm EDD' AA'ED.left_comm DD'AB.symm).right_comm,
  have BCEF : cong B C' E F' := (l2_11 BCC' EFF'.symm FF'BC.symm.right_comm CC'FE).right_comm,
  apply l11_3_bis (BAA'.out nAB).symm (BCC'.out nCB).symm (EDD'.out nDE).symm (EFF'.out nFE).symm
    ABDE BCEF (h (BAA'.out nAB).symm (BCC'.out nCB).symm (EDD'.out nDE).symm (EFF'.out nFE).symm
      ABDE.comm BCEF),
end

-- l11_4_1
lemma cong_angle.cong_of_out
  (ABCDEF : cong_angle A B C D E F) (BA'A : out B A' A) (BC'C : out B C' C)
  (ED'D : out E D' D) (EF'F : out E F' F) (BA'ED' : cong B A' E D') (BC'EF' : cong B C' E F') :
  cong A' C' D' F' :=
begin
  rcases ABCDEF with ⟨-, -, -, -, A'', C'', D'', F'', BAA'', AA''ED, BCC'', CC''EF, EDD'', DD''BA,
    EFF'', FF''BC, ACDF⟩,
  have BA''ED'' : cong B A'' E D'' := l11_aux BAA'' EDD'' AA''ED DD''BA,
  have BC''EF'' : cong B C'' E F'' := l11_aux BCC'' EFF'' CC''EF FF''BC,
  have BA'A'' : out B A' A'' := BA'A.trans (BAA''.out BA'A.2.1),
  have BC'C'' : out B C' C'' := BC'C.trans (BCC''.out BC'C.2.1),
  have ED'D'' : out E D' D'' := ED'D.trans (EDD''.out ED'D.2.1),
  have EF'F'' : out E F' F'' := EF'F.trans (EFF''.out EF'F.2.1),
  have AADD : cong A' A'' D' D'' := l11_aux' BA'A'' ED'D'' BA'ED' BA''ED'',
  have CCFF : cong C' C'' F' F'' := l11_aux' BC'C'' EF'F'' BC'EF' BC''EF'',
  apply (l4_16 BC'C''.symm.col BC''EF'' BC'EF' CCFF.comm BA'ED' _ BC'C''.2.1.symm).comm,
  apply (l4_16 BA'A''.symm.col BA''ED'' BA'ED' AADD.comm BC''EF'' ACDF BA'A''.2.1.symm).comm,
end

lemma l11_4 (nAB : A ≠ B) (nCB : C ≠ B) (nDE : D ≠ E) (nFE : F ≠ E) :
  cong_angle A B C D E F ↔
    (∀ ⦃A' C' D' F'⦄, out B A' A → out B C' C → out E D' D → out E F' F →
      cong B A' E D' → cong B C' E F' → cong A' C' D' F') :=
⟨λ h A' C' D' F', h.cong_of_out, l11_4_2 nAB nCB nDE nFE⟩

lemma cong_angle_of_cong (nAB : A ≠ B) (nCB : C ≠ B)
  (AB : cong A B A' B') (AC : cong A C A' C') (BC : cong B C B' C') :
  cong_angle A B C A' B' C' :=
l11_3_bis
  (out.trivial nAB) (out.trivial nCB) (out.trivial (AB.diff nAB)) (out.trivial (BC.comm.diff nCB))
  AB BC AC

-- conga_refl
-- 11.6
lemma cong_angle.refl (nAB : A ≠ B) (nCB : C ≠ B) : cong_angle A B C A B C :=
cong_angle_of_cong nAB nCB (cong.refl _ _) (cong.refl _ _) (cong.refl _ _)

-- conga_sym
-- 11.7
lemma cong_angle.symm : cong_angle A B C A' B' C' → cong_angle A' B' C' A B C
| ⟨_, _, _, _, A₀, C₀, D₀, F₀, BAA₀, AA₀BA', BCC₀, CC₀B'C', B'A'D₀, A'D₀BA, B'C'F₀, C'F₀BC, ACDF⟩ :=
  { nAB := ‹_›, nCB := ‹_›, nDE := ‹_›, nFE := ‹_›,
    ex := ⟨D₀, F₀, A₀, C₀, B'A'D₀, A'D₀BA, B'C'F₀, C'F₀BC, BAA₀, AA₀BA', BCC₀, CC₀B'C', ACDF.symm⟩ }

-- out_conga
-- l11_10
lemma cong_angle.cong_angle_of_out (h : cong_angle A B C D E F)
  (BAA' : out B A A') (BCC' : out B C C') (EDD' : out E D D') (EFF' : out E F F') :
  cong_angle A' B C' D' E F' :=
l11_4_2 BAA'.2.1 BCC'.2.1 EDD'.2.1 EFF'.2.1
(λ A'' C'' D'' F'' BAA BCC EDD EFF BAED BCEF,
  h.cong_of_out
    (BAA.trans BAA'.symm) (BCC.trans BCC'.symm) (EDD.trans EDD'.symm) (EFF.trans EFF'.symm)
    BAED BCEF)

-- 11.8
lemma cong_angle.trans (h₁ : cong_angle A B C A' B' C') (h₂ : cong_angle A' B' C' A'' B'' C'') :
  cong_angle A B C A'' B'' C'' :=
begin
  apply l11_4_2 h₁.nAB h₁.nCB h₂.nDE h₂.nFE,
  intros A₀ C₀ A₂ C₂ BAA₀ BCC₀ BAA₂ BCC₂ BA₀₂ BC₀₂,
  obtain ⟨A₁, BAA₁, BA₁₀⟩ := segment_construction_3 h₁.nDE.symm BAA₀.1.symm,
  obtain ⟨C₁, BCC₁, BC₁₀⟩ := segment_construction_3 h₁.nFE.symm BCC₀.1.symm,
  apply (h₁.cong_of_out BAA₀ BCC₀ BAA₁.symm BCC₁.symm BA₁₀.symm BC₁₀.symm).trans
    (h₂.cong_of_out BAA₁.symm BCC₁.symm BAA₂ BCC₂ (BA₁₀.trans BA₀₂) (BC₁₀.trans BC₀₂)),
end

-- cong3_conga2
lemma cong_angle.cong_angle_of_cong
  (AB : cong A B A' B') (AC : cong A C A' C') (BC : cong B C B' C')
  (a : cong_angle A B C A'' B'' C'') :
  cong_angle A' B' C' A'' B'' C'' :=
cong_angle.trans (cong_angle_of_cong (AB.diff a.nAB) (BC.comm.diff a.nCB) AB.symm AC.symm BC.symm) a

-- 11.9
lemma cong_angle_pseudo_refl (nAB : A ≠ B) (nCB : C ≠ B) : cong_angle A B C C B A :=
begin
  obtain ⟨C', BAC, BC⟩ := segment_construction_3 nAB.symm nCB.symm,
  apply l11_3_bis BAC.symm (out.trivial nCB) (out.trivial nCB) BAC.symm BC.comm BC.symm
    (cong.pseudo_refl _ _),
end

lemma cong_angle_zero (nAB : A ≠ B) (nCD : C ≠ D) : cong_angle A B A C D C :=
begin
  obtain ⟨C', BAC, BCDC⟩ := segment_construction_3 nAB.symm nCD.symm,
  apply l11_3_bis BAC.symm BAC.symm (out.trivial nCD) (out.trivial nCD) BCDC.comm BCDC
    (cong.trivial_identity _ _),
end

-- l11_13
lemma cong_angle.complement (h : cong_angle A B C D E F) (ABA : betw A B A') (nAB' : A' ≠ B)
  (DED : betw D E D') (nDE' : D' ≠ E) :
  cong_angle A' B C D' E F :=
begin
  obtain ⟨nAB, nCB, nDE, nFE, A'', C'', D'', F'',
    BAA, AAED, BCC, CCEF, EDD, DDBA, EFF, FFBC, ACDF⟩ := h,
  obtain ⟨A₀, BAA₀, AAED₀⟩ := segment_construction B A' E D',
  obtain ⟨D₀, EDD₀, DDBA₀⟩ := segment_construction E D' B A',
  refine ⟨nAB', nCB, nDE', nFE, A₀, _, D₀, _, BAA₀, AAED₀, BCC, CCEF, EDD₀, DDBA₀, EFF, FFBC, _⟩,
  exact five_segment (l11_aux BAA EDD AAED DDBA).comm (l11_aux BAA₀ EDD₀ AAED₀ DDBA₀) ACDF
    (l11_aux BCC EFF CCEF FFBC)
    ((BAA.symm.trans ABA nAB).trans' BAA₀ nAB'.symm)
    ((EDD.symm.trans DED nDE).trans' EDD₀ nDE'.symm)
    (BAA.symm.ne' nAB.symm),
end

lemma cong_angle.right_comm (h : cong_angle A B C D E F) : cong_angle A B C F E D :=
h.trans (cong_angle_pseudo_refl h.nDE h.nFE)

lemma cong_angle.left_comm (h : cong_angle A B C D E F) : cong_angle C B A D E F :=
cong_angle.trans (cong_angle_pseudo_refl h.nCB h.nAB) h

lemma cong_angle.comm (h : cong_angle A B C D E F) : cong_angle C B A F E D :=
h.left_comm.right_comm

-- conga_line
lemma betw.cong_angle (ABC : betw A B C) (DEF : betw D E F)
  (nAB : A ≠ B) (nBC : B ≠ C) (nDE : D ≠ E) (nEF : E ≠ F) :
  cong_angle A B C D E F :=
(cong_angle_zero nBC.symm nEF.symm).complement ABC.symm nAB DEF.symm nDE

-- l11_14
lemma cong_angle_opposite (ABA : betw A B A') (nAB : A ≠ B) (nAB' : A' ≠ B)
  (CBC : betw C B C') (nBC : B ≠ C) (nBC' : B ≠ C') :
  cong_angle A B C A' B C' :=
((cong_angle_pseudo_refl nAB nBC.symm).complement ABA nAB' CBC nBC'.symm).right_comm.complement
  ABA.symm nAB ABA nAB'

-- cong2_conga_cong
lemma cong_angle.cong (ABC : cong_angle A B C A' B' C') (AB : cong A B A' B')
  (BC : cong B C B' C') :
  cong A C A' C' :=
ABC.cong_of_out (out.trivial ABC.1) (out.trivial ABC.2) (out.trivial ABC.3) (out.trivial ABC.4)
  AB.comm BC

-- l11_21_a
lemma out.out_of_cong_angle (BAC : out B A C) (h : cong_angle A B C D E F) :
  out E D F :=
begin
  obtain ⟨A', C', D', F', BAA, AAED, BCC, CCEF, EDD, DDBA, EFF, FFBC, ACDF⟩ := h.ex,
  apply (EDD.out h.nDE).trans (out.trans _ (EFF.out h.nFE).symm),
  apply out.out_of_congs _ (l11_aux BAA EDD AAED DDBA) (l11_aux BCC EFF CCEF FFBC) ACDF,
  apply (BAA.out BAC.1).symm.trans (BAC.trans (BCC.out BAC.2.1)),
end

-- l11_21_b
lemma out.cong_angle_of_out (BAC : out B A C) (EDF : out E D F) :
  cong_angle A B C D E F :=
(cong_angle_zero BAC.1 EDF.1).cong_angle_of_out (out.trivial BAC.1) BAC (out.trivial EDF.1) EDF

def in_angle (P A B C : α) := A ≠ B ∧ C ≠ B ∧ P ≠ B ∧ ∃ X, betw A X C ∧ (X = B ∨ out B X P)

-- l11_24
lemma in_angle.symm : in_angle P A B C → in_angle P C B A :=
begin
  rintro ⟨nAB, nCB, nPB, X, AXC, h⟩,
  exact ⟨nCB, nAB, nPB, X, AXC.symm, h⟩,
end

-- out321__inagle
lemma out.in_angle_left (nCB : C ≠ B) (BAP : out B A P) :
  in_angle P A B C :=
⟨BAP.1, nCB, BAP.2.1, A, betw.id_left _ _, or.inr BAP⟩

-- out341__inagle
lemma out.in_angle_right (nAB : A ≠ B) (BCP : out B C P) :
  in_angle P A B C :=
⟨nAB, BCP.1, BCP.2.1, C, betw.id_right _ _, or.inr BCP⟩

-- out_in_angle
lemma out.in_angle_zero (BAC : out B A C) (BPA : out B P A) :
  in_angle P A B C :=
out.in_angle_left BAC.2.1 BPA.symm

-- inangle1123
lemma in_angle_left (nAB : A ≠ B) (nCB : C ≠ B) : in_angle A A B C :=
⟨nAB, nCB, nAB, A, betw.id_left _ _, or.inr (out.trivial nAB)⟩

-- inangle3123
lemma in_angle_right (nAB : A ≠ B) (nCB : C ≠ B) : in_angle C A B C :=
⟨nAB, nCB, nCB, C, betw.id_right _ _, or.inr (out.trivial nCB)⟩

-- in_angle_out
lemma in_angle.out_of_out (BAC : out B A C) (hP : in_angle P A B C) :
  out B A P :=
begin
  obtain ⟨X, AXC, _ | h⟩ := hP.2.2.2,
  { subst X,
    apply ((l6_4_1 BAC).2 AXC).elim },
  apply (BAC.out_of_bet AXC).trans h,
end

-- l11_25_aux
lemma in_angle.in_angle_of_out' (hP : in_angle P A B C) (ABC : ¬ betw A B C) (BAA : out B A' A) :
  in_angle P A' B C :=
begin
  obtain ⟨X, AXC, BXP⟩ := hP.2.2.2,
  have nXB : X ≠ B,
  { rintro rfl,
    apply ABC AXC },
  replace BXP := BXP.resolve_left nXB,
  refine ⟨BAA.1, hP.2.1, hP.2.2.1, _⟩,
  cases BAA.2.2,
  { obtain ⟨X', XXB, AXC⟩ := inner_pasch AXC.symm h,
    refine ⟨X', AXC, _⟩,
    rw or_iff_not_imp_left,
    intro h,
    apply (XXB.symm.out h).trans BXP },
  obtain ⟨X', AXC, BXX⟩ := outer_pasch h.symm AXC.symm,
  refine ⟨X', AXC, _⟩,
  rw or_iff_not_imp_left,
  intro h,
  apply (BXX.out nXB).symm.trans BXP,
end

-- l11_25
lemma in_angle.in_angle_of_out (hP : in_angle P A B C)
  (BAA : out B A' A) (BCC : out B C' C) (BPP : out B P' P) :
  in_angle P' A' B C' :=
begin
  refine ⟨BAA.1, BCC.1, BPP.1, _⟩,
  by_cases betw A B C,
  { refine ⟨B, _, or.inl rfl⟩,
    apply ((h.out_betw BAA.symm).symm.out_betw BCC.symm).symm },
  have hP' := hP.in_angle_of_out' h BAA,
  obtain ⟨-, -, -, X, AXC, (rfl | BXP)⟩ :=
    (hP'.symm.in_angle_of_out' (λ k, h (k.symm.out_betw BAA)) BCC).symm,
  { exact ⟨X, AXC, or.inl rfl⟩ },
  { exact ⟨X, AXC, or.inr (BXP.trans BPP.symm)⟩ }
end

def le_angle (A B C D E F : α) := ∃ P, in_angle P D E F ∧ cong_angle A B C D E P
@[reducible] def ge_angle (A B C D E F : α) := le_angle D E F A B C
def lt_angle (A B C D E F : α) := le_angle A B C D E F ∧ ¬ cong_angle A B C D E F
@[reducible] def gt_angle (A B C D E F : α) := lt_angle D E F A B C

lemma l11_30 (le : le_angle A B C D E F) (ABC : cong_angle A B C A' B' C')
  (DEF : cong_angle D E F D' E' F') :
  le_angle A' B' C' D' E' F' :=
begin
  obtain ⟨P, PDEF, ABCDEP⟩ := le,

  -- refine ⟨_, _, _⟩,
end

lemma l11_44_2 (ABC : ¬col A B C) : lt_angle B A C B C A ↔ lt B C B A :=
begin
  sorry
end

lemma le_angle.lt_trans {G H I : α} (le : le_angle A B C D E F) (lt : lt_angle D E F G H I) :
  lt_angle A B C G H I :=
sorry

lemma betw.le_lt (ADB : betw A D B) (nAD : A ≠ D) (nDB : D ≠ B) (ACBC : le A C B C) :
  lt D C B C :=
begin
  have nBA : B ≠ A,
  { rintro rfl,
    apply nAD ADB.identity },
  apply lt.comm,
  by_cases ABC : col A B C,
  { by_cases CDB : betw C D B,
    { exact ⟨⟨D, CDB, cong.refl _ _⟩, λ i, nDB (CDB.cong i)⟩ },
    have DCB : out D C B := (ADB.col.right_symm.trans' ABC nBA.symm).symm.out_of_not_betw CDB,
    have nCD : C ≠ D := DCB.1,
    have CDA : betw C D A := (l6_2 nDB.symm nCD nAD ADB.symm).2 DCB.symm,
    have nAC : A ≠ C,
    { rintro rfl,
      apply nCD CDA.identity },
    apply (CDA.lt_left nAD.symm).trans_le ACBC.comm },
  have BCD : ¬col B C D := λ i, ABC (ADB.symm.col.trans i.right_symm nDB.symm).left_symm,
  rw ←l11_44_2 BCD,
  have nCA : C ≠ A,
  { rintro rfl,
    apply ABC (betw.id_left _ _).col.right_symm },
  have : le_angle C B D C A B,
  { apply @l11_30 _ _ C B A C A B,
    { sorry },
    { sorry },
    { apply cong_angle.refl nCA nBA },
  },
  apply this.lt_trans,

end

end tarski

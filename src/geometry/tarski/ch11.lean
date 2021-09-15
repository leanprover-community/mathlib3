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
l11_3_bis nAB.out nCB.out (AB.diff nAB).out (BC.comm.diff nCB).out AB BC AC

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
  apply l11_3_bis BAC.symm nCB.out nCB.out BAC.symm BC.comm BC.symm (cong.pseudo_refl _ _),
end

lemma cong_angle_zero (nAB : A ≠ B) (nCD : C ≠ D) : cong_angle A B A C D C :=
begin
  obtain ⟨C', BAC, BCDC⟩ := segment_construction_3 nAB.symm nCD.symm,
  apply l11_3_bis BAC.symm BAC.symm nCD.out nCD.out BCDC.comm BCDC (cong.trivial_identity _ _),
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

lemma cong_angle.complement' (h : cong_angle A B C D E F) (CBC : betw C B C') (nCB' : C' ≠ B)
  (FEF : betw F E F') (nFE' : F' ≠ E) :
  cong_angle A B C' D E F' :=
(h.comm.complement CBC nCB' FEF nFE').comm

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
(cong_angle_zero BAC.1 EDF.1).cong_angle_of_out BAC.1.out BAC EDF.1.out EDF

-- converse of `betw.cong_angle`
lemma cong_angle.betw_of_betw (h : cong_angle A B C D E F) (ABC : betw A B C) :
  betw D E F :=
begin
  obtain ⟨A', ABA, AB⟩ := point_construction_different A B,
  obtain ⟨D', DED, DE⟩ := point_construction_different D E,
  have ABCDEF := h.complement ABA AB.symm DED DE.symm,
  have BAC : out B A' C := l6_3_2 AB.symm h.nCB h.nAB ABA.symm ABC.symm,
  apply (DED.symm.out_betw (BAC.out_of_cong_angle ABCDEF)).symm,
end

lemma cong_angle.col_of_col (h : cong_angle A B C D E F) (ABC : col A B C) :
  col D E F :=
begin
  have : out B A C ∨ betw A B C,
  { rw or_iff_not_imp_right,
    apply ABC.out_of_not_betw },
  cases this with BAC ABC,
  { apply (BAC.out_of_cong_angle h).col.left_symm },
  apply (h.betw_of_betw ABC).col,
end

-- cong2_conga_cong
lemma cong_angle.cong (ABC : cong_angle A B C A' B' C') (AB : cong A B A' B')
  (BC : cong B C B' C') :
  cong A C A' C' :=
ABC.cong_of_out ABC.1.out ABC.2.out ABC.3.out ABC.4.out AB.comm BC

-- 11.15 one
-- angle_construction_1
lemma angle_construction_existence (nABC : ¬ col A B C) (nDEP : ¬ col D E P) :
  ∃ F, cong_angle A B C D E F ∧ one_side E D F P :=
begin
  have nAB := ne12_of_not_col nABC,
  have nBC := ne23_of_not_col nABC,
  have nDE := ne12_of_not_col nDEP,
  obtain ⟨D', EDD, EDBA⟩ := segment_construction_3 (ne12_of_not_col nDEP).symm nAB.symm,
  have nDEP' : ¬ col D' E P,
  { intro DEP,
    apply nDEP (DEP.of_col col_id_left EDD.col.rotate' EDD.2.1) },
  obtain ⟨F, ABDE, ACDF, BCEF, DEFP⟩ := l10_16_existence nABC nDEP' EDBA.symm.comm,
  have nEF : E ≠ F := BCEF.diff nBC,
  refine ⟨F, _⟩,
  have : cong_angle A B C D' E F := cong_angle_of_cong nAB nBC.symm ABDE ACDF BCEF,
  refine ⟨_, _⟩,
  apply this.cong_angle_of_out nAB.out nBC.symm.out EDD.symm nEF.symm.out,
  apply DEFP.col nDE.symm col_id_mid EDD.col.rotate,
end

-- 11.15 two
lemma angle_construction_uniqueness {F₁ F₂ : α} (nABC : ¬ col A B C) (nDEP : ¬ col D E P)
  (ABCDEF₁ : cong_angle A B C D E F₁) (EDFP₁ : one_side E D F₁ P)
  (ABCDEF₂ : cong_angle A B C D E F₂) (EDFP₂ : one_side E D F₂ P) :
  out E F₁ F₂ :=
begin
  have nAB := ne12_of_not_col nABC,
  have nBC := ne23_of_not_col nABC,
  have nDE := ne12_of_not_col nDEP,
  have nEF₁ := ABCDEF₁.nFE.symm,
  have nEF₂ := ABCDEF₂.nFE.symm,
  obtain ⟨D', EDD, ABDE⟩ := segment_construction_3 nDE.symm nAB.symm,
  replace ABDE := ABDE.symm.comm,
  have nDEP' : ¬ col D' E P,
  { intro DEP,
    apply nDEP (DEP.of_col col_id_left EDD.col.rotate' EDD.2.1) },
  obtain ⟨F₃, EFF₃, EF₃⟩ := segment_construction_3 nEF₁ nBC,
  obtain ⟨F₄, EFF₄, EF₄⟩ := segment_construction_3 nEF₂ nBC,
  have : F₃ = F₄,
  { refine (l10_16 nABC nDEP' ABDE).unique _ _,
    { refine ⟨ABDE, _, EF₃.symm, _⟩,
      { apply ABCDEF₁.cong_of_out nAB.out nBC.symm.out EDD.symm EFF₃.symm ABDE.comm EF₃.symm },
      have : one_side E D F₁ F₃,
      { apply EFF₃.one_side col_id_left,
        intro h,
        apply nABC (ABCDEF₁.symm.col_of_col h.symm) },
      have : one_side E D F₃ P,
      { apply this.right_symm.trans EDFP₁ },
      apply this.col (ne12_of_not_col nDEP') EDD.col.rotate' col_id_left },
    { refine ⟨ABDE, _, EF₄.symm, _⟩,
      { apply ABCDEF₂.cong_of_out nAB.out nBC.symm.out EDD.symm EFF₄.symm ABDE.comm EF₄.symm },
      have : one_side E D F₂ F₄,
      { apply EFF₄.one_side col_id_left,
        intro h,
        apply nABC (ABCDEF₂.symm.col_of_col h.symm) },
      have : one_side E D F₄ P,
      { apply this.right_symm.trans EDFP₂ },
      apply this.col (ne12_of_not_col nDEP') EDD.col.rotate' col_id_left } },
  cases this,
  apply EFF₃.trans EFF₄.symm,
end

-- 11.15 two
lemma angle_construction_uniqueness' {F₁ F₂ : α} (nABC : ¬ col A B C)
  (ABCDEF₁ : cong_angle A B C D E F₁) (ABCDEF₂ : cong_angle A B C D E F₂)
  (EDF : one_side E D F₁ F₂) :
  out E F₁ F₂ :=
angle_construction_uniqueness
  nABC (λ h, EDF.not_col_right h.symm) ABCDEF₁ EDF ABCDEF₂ (one_side.refl EDF.not_col_right)

-- 10.12, 8.10 and 8.1 according to 11.5.

-- lemma l11_3_bis (BA'A : out B A' A) (BC'C : out B C' C) (ED'D : out E D' D) (EF'F : out E F' F)
--   (A'BD'E : cong A' B D' E) (BC'EF' : cong B C' E F') (A'C'D'F' : cong A' C' D' F') :
--   cong_angle A B C D E F :=

-- l11_16
lemma per.cong_angle_of_per (ABC : per A B C) (ABC' : per A' B' C')
  (nAB : A ≠ B) (nCB : C ≠ B) (nAB' : A' ≠ B') (nCB' : C' ≠ B') :
  cong_angle A B C A' B' C' :=
begin
  obtain ⟨A'', BAA, BA⟩ := segment_construction_3 nAB'.symm nAB.symm,
  obtain ⟨C'', BCC, BC⟩ := segment_construction_3 nCB'.symm nCB.symm,
  apply l11_3_bis nAB.out nCB.out BAA.symm BCC.symm BA.comm.symm BC.symm,
  apply l10_12 ABC (ABC'.of_col_of_col nAB' nCB' BAA.col.symm BCC.col.symm) BA.comm.symm BC.symm,
end

-- l11_17
lemma per.per_of_cong_angle (ABC : per A B C) (h : cong_angle A B C A' B' C') :
  per A' B' C' :=
begin
  obtain ⟨A'', BAA, BA⟩ := segment_construction_3 h.nDE.symm h.nAB.symm,
  obtain ⟨C'', BCC, BC⟩ := segment_construction_3 h.nFE.symm h.nCB.symm,
  have AC := h.cong_of_out h.nAB.out h.nCB.out BAA.symm BCC.symm BA.symm BC.symm,
  have ABC' := ABC.of_congs BA.comm.symm AC BC.symm,
  exact ABC'.of_col_of_col BAA.2.1 BCC.2.1 BAA.col.rotate BCC.col.rotate,
end

-- l11_22_a
lemma cong_angle.two_sides (ABPABP : cong_angle A B P A' B' P') (PBCPBC : cong_angle P B C P' B' C')
  (BPAC : two_sides B P A C) (BPAC' : two_sides B' P' A' C') :
  cong_angle A B C A' B' C' :=
begin
  obtain ⟨nABP, nCBP, D, DBP, ADC⟩ := BPAC,
  have nAB := ABPABP.nAB,
  have nAB' := ABPABP.nDE,
  have nCB := PBCPBC.nCB,
  have nAD : A ≠ D,
  { rintro rfl,
    apply nABP DBP },
  obtain ⟨A'', BAA, BA⟩ := segment_construction_3 ABPABP.nDE.symm ABPABP.nAB.symm,
  obtain ⟨D'', BD, h₁, h₂⟩ :
    ∃ D'', cong B' D'' B D ∧ (betw D B P → betw D'' B' P') ∧ (out B D P → out B' D'' P'),
  { cases DBP.betw_or_out,
    { obtain ⟨D'', PBD, BD⟩ := segment_construction P' B' B D,
      exact ⟨D'', BD, λ _, PBD.symm, λ h₂, ((l6_4_1 h₂).2 h).elim⟩ },
    { obtain ⟨D'', BPD', BD⟩ := segment_construction_3 PBCPBC.nDE.symm h.1.symm,
      exact ⟨D'', BD, λ h₂, ((l6_4_1 h).2 h₂).elim, λ _, BPD'.symm⟩ } },
  have DBP' : col D'' B' P',
  { cases DBP.betw_or_out,
    { apply (h₁ h).col },
    { apply (h₂ h).col.left_symm } },
  obtain ⟨C'', ADC', DC⟩ := segment_construction A'' D'' D C,
  have ABDABD : D ≠ B → cong_angle A B D A' B' D'',
  { intro nDB,
    cases DBP.betw_or_out,
    { apply ABPABP.complement' h.symm nDB (h₁ h).symm (BD.symm.diff nDB.symm).symm },
    { apply ABPABP.cong_angle_of_out nAB.out h.symm nAB'.out (h₂ h).symm } },
  have AD : cong A D A'' D'',
  { rcases eq_or_ne D B with rfl | nDB,
    { cases BD.identity,
      apply BA.symm.comm },
    have nBD' := BD.symm.diff nDB.symm,
    apply (ABDABD nDB).cong_of_out nAB.out nDB.out BAA.symm nBD'.symm.out BA.symm BD.symm },
  have nAD' : A'' ≠ D'' := AD.diff nAD,
  have BC := (five_segment AD DC.symm BA.symm.comm BD.symm.comm ADC ADC' nAD).comm,
  have PBCPBC' : cong_angle P B C P' B' C'',
  { rcases eq_or_ne B D with rfl | nBD,
    { cases BD.identity,
      apply (ABPABP.complement ADC nCB (ADC'.out_betw BAA.symm) (DC.comm.symm.diff nCB)).comm },
    have DBCDBC : cong_angle D B C D'' B' C'' :=
      cong_angle_of_cong nBD.symm nCB BD.symm.comm DC.symm BC,
    cases DBP.betw_or_out,
    { apply DBCDBC.complement h PBCPBC.nAB (h₁ h) PBCPBC.nDE },
    { apply DBCDBC.cong_angle_of_out h nCB.out (h₂ h) (BC.comm.diff nCB).out } },
  have nCBP'' : ¬ col C'' B' P' := λ h, nCBP (PBCPBC'.comm.symm.col_of_col h),
  have BPAC'' : two_sides B' P' A'' C'' :=
    ⟨λ h, nCBP'' (h.of_col DBP' ADC'.col nAD'), nCBP'', D'', DBP', ADC'⟩,
  have BPAA : one_side B' P' A' A'',
  { rw l9_19 col_id_left BAA.col.rotate,
    exact ⟨BAA, λ ABP, nABP (ABPABP.symm.col_of_col ABP)⟩ },
  have BCC : out B' C' C'',
  { apply angle_construction_uniqueness' (λ h, nCBP h.symm) PBCPBC PBCPBC',
    exact ⟨A'', ((l9_8 BPAC').2 BPAA).right_symm, BPAC''.right_symm⟩ },
  apply l11_3_bis nAB.out nCB.out BAA.symm BCC.symm BA.symm.comm BC (l2_11 ADC ADC' AD DC.symm),
end

-- l11_22_b
lemma cong_angle.one_side (ABPABP : cong_angle A B P A' B' P') (PBCPBC : cong_angle P B C P' B' C')
  (BPAC : one_side B P A C) (BPAC' : one_side B' P' A' C') :
  cong_angle A B C A' B' C' :=
begin
  obtain ⟨D, ABD, nBD⟩ := point_construction_different A B,
  obtain ⟨D', ABD', nBD'⟩ := point_construction_different A' B',
  have DBPDBP := ABPABP.complement ABD nBD.symm ABD' nBD'.symm,
  apply (DBPDBP.two_sides PBCPBC _ _).complement ABD.symm ABPABP.nAB ABD'.symm ABPABP.nDE,
  { have : two_sides B P A D,
    { refine ⟨BPAC.not_col_left, _, _, col_id_left, ABD⟩,
      intro DBP,
      apply BPAC.not_col_left (ABD.col.symm.trans' DBP nBD.symm).left_symm },
    apply two_sides.right_symm,
    rwa l9_8 this },
  { have : two_sides B' P' A' D',
    { refine ⟨BPAC'.not_col_left, _, _, col_id_left, ABD'⟩,
      intro DBP,
      apply BPAC'.not_col_left (ABD'.col.symm.trans' DBP nBD'.symm).left_symm },
    apply two_sides.right_symm,
    rwa l9_8 this },
end

def in_angle (P A B C : α) := A ≠ B ∧ C ≠ B ∧ P ≠ B ∧ ∃ X, betw A X C ∧ (X = B ∨ out B X P)

-- l11_24
lemma in_angle.symm : in_angle P A B C → in_angle P C B A :=
begin
  rintro ⟨nAB, nCB, nPB, X, AXC, h⟩,
  exact ⟨nCB, nAB, nPB, X, AXC.symm, h⟩,
end

-- out321__inagle
lemma out.in_angle_left (BAP : out B A P) (nCB : C ≠ B) :
  in_angle P A B C :=
⟨BAP.1, nCB, BAP.2.1, A, betw.id_left _ _, or.inr BAP⟩

-- out341__inagle
lemma out.in_angle_right (BCP : out B C P) (nAB : A ≠ B) :
  in_angle P A B C :=
⟨nAB, BCP.1, BCP.2.1, C, betw.id_right _ _, or.inr BCP⟩

-- out_in_angle
lemma out.in_angle_zero (BAC : out B A C) (BPA : out B P A) :
  in_angle P A B C :=
BPA.symm.in_angle_left BAC.2.1

-- inangle1123
lemma in_angle_left (nAB : A ≠ B) (nCB : C ≠ B) : in_angle A A B C :=
nAB.out.in_angle_left nCB

-- inangle3123
lemma in_angle_right (nAB : A ≠ B) (nCB : C ≠ B) : in_angle C A B C :=
nCB.out.in_angle_right nAB

-- in_angle_out
lemma in_angle.out_of_out (hP : in_angle P A B C) (BAC : out B A C) :
  out B A P :=
begin
  obtain ⟨X, AXC, _ | h⟩ := hP.2.2.2,
  { subst X,
    apply ((l6_4_1 BAC).2 AXC).elim },
  apply (BAC.out_of_bet AXC).trans h,
end

lemma betw.in_angle_iff (ABC : betw A B C) : in_angle P A B C ↔ A ≠ B ∧ C ≠ B ∧ P ≠ B :=
begin
  split,
  { rintro ⟨nAB, nCB, nPB, -, -, -⟩,
    exact ⟨nAB, nCB, nPB⟩, },
  { rintro ⟨nAB, nCB, nPB⟩,
    exact ⟨nAB, nCB, nPB, B, ABC, or.inl rfl⟩ },
end

lemma betw.in_angle_iff_of_ne (ABC : betw A B C) (nAB : A ≠ B) (nCB : C ≠ B) :
  in_angle P A B C ↔ P ≠ B :=
begin
  rw ABC.in_angle_iff,
  simp [nAB, nCB]
end

lemma betw.in_angle_betw (ABC : betw A B P) (PABC : in_angle P A B C) : betw A B C :=
begin
  obtain ⟨nAB, nCB, nPB, X, AXC, rfl | BXP⟩ := PABC,
  { exact AXC },
  { exact (ABC.symm.out_betw BXP.symm).symm.left_trans AXC },
end

-- l11_25_aux
lemma in_angle.in_angle_of_out_aux (hP : in_angle P A B C) (ABC : ¬ betw A B C) (BAA : out B A' A) :
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
  have hP' := hP.in_angle_of_out_aux h BAA,
  obtain ⟨-, -, -, X, AXC, (rfl | BXP)⟩ :=
    (hP'.symm.in_angle_of_out_aux (λ k, h (k.symm.out_betw BAA)) BCC).symm,
  { exact ⟨X, AXC, or.inl rfl⟩ },
  { exact ⟨X, AXC, or.inr (BXP.trans BPP.symm)⟩ }
end

lemma l11_28 (AB : cong A B A' B') (AC : cong A C A' C') (BC : cong B C B' C')
  (ACD : col A C D) :
  ∃ D', cong A D A' D' ∧ cong B D B' D' ∧ cong C D C' D' :=
begin
  rcases eq_or_ne A C with rfl | nAC,
  { cases AC.reverse_identity,
    by_cases ABD : col A B D,
    { obtain ⟨D', _, AD, BD⟩ := l4_14 ABD AB,
      exact ⟨D', AD, BD, AD⟩ },
    { obtain ⟨E, nABE⟩ := exists_not_col (AB.diff (ne12_of_not_col ABD)),
      obtain ⟨D', -, AD, BD, -⟩ := l10_16_existence ABD nABE AB,
      exact ⟨D', AD, BD, AD⟩ } },
  { obtain ⟨D', -, AD, CD⟩ := l4_14 ACD AC,
    exact ⟨D', AD, (l4_16 ACD AC AD CD AB BC.comm nAC).comm, CD⟩ }
end

lemma in_angle.one_side (PABC : in_angle P A B C) (nABC : ¬ col A B C) (nABP : ¬ col A B P) :
  one_side A B C P :=
begin
  obtain ⟨nAB, nCB, nPB, X, AXC, h⟩ := PABC,
  have nBX : B ≠ X,
  { rintro rfl,
    apply nABC AXC.col },
  replace h := h.resolve_left nBX.symm,
  have nAX : A ≠ X,
  { rintro rfl,
    apply nABP h.col.left_symm },
  have ABCX : one_side A B C X := (AXC.out nAX.symm).symm.one_side col_id_left (λ i, nABC i.rotate),
  apply ABCX.trans (h.one_side col_id_mid ABCX.not_col_right),
end

lemma in_angle.trans (CABD : in_angle C A B D) (DABE : in_angle D A B E) :
  in_angle C A B E :=
begin
  obtain ⟨nAB, nEB, nDB, Y, AYE, h₂⟩ := DABE,
  have nCB := CABD.2.2.1,
  rcases h₂ with rfl | h₂,
  { rwa AYE.in_angle_iff_of_ne nAB nEB },
  have CABY : in_angle C A B Y := CABD.in_angle_of_out nAB.out h₂ nCB.out,
  obtain ⟨_, _, -, Z, AZY, h⟩ := CABY,
  exact ⟨nAB, nEB, nCB, Z, AZY.left_trans AYE, h⟩,
end

lemma in_angle.antisymm (DABC : in_angle D A B C) (CABD : in_angle C A B D) :
  out B C D :=
begin
  obtain ⟨nAB, nCB, nDB, X, AXC, h₁ | h₁⟩ := id DABC,
  { subst X,
    apply l6_3_2 nCB nDB nAB AXC.symm (AXC.in_angle_betw CABD).symm },
  obtain ⟨-, -, -, Y, AYD, h₂ | h₂⟩ := id CABD,
  { subst Y,
    apply l6_3_2 nCB nDB nAB ((AYD.symm.out_betw h₁.symm).symm.left_trans AXC).symm AYD.symm },
  obtain ⟨Z, XZD, YZC⟩ := inner_pasch AXC.symm AYD.symm,
  apply (h₂.symm.out_of_bet YZC.symm).trans (h₁.symm.out_of_bet XZD.symm).symm,
end

lemma in_angle.antisymm' (DABC : in_angle D A B C) (CABD : in_angle C A B D) :
  cong_angle A B C A B D :=
(cong_angle.refl DABC.1 DABC.2.1).cong_angle_of_out
  DABC.1.out DABC.2.1.out DABC.1.out (DABC.antisymm CABD)

def le_angle (A B C D E F : α) := ∃ P, in_angle P D E F ∧ cong_angle A B C D E P
@[reducible] def ge_angle (A B C D E F : α) := le_angle D E F A B C
def lt_angle (A B C D E F : α) := le_angle A B C D E F ∧ ¬ cong_angle A B C D E F
@[reducible] def gt_angle (A B C D E F : α) := lt_angle D E F A B C

lemma le_angle.le_angle_of_out (ABCDEF : le_angle A B C D E F)
  (BAA : out B A A') (BCC : out B C C')
  (EDD : out E D D') (EFF : out E F F') :
  le_angle A' B C' D' E F' :=
begin
  obtain ⟨P, PDEF, ABCDEP⟩ := ABCDEF,
  have EPP := PDEF.2.2.1.out,
  exact ⟨P, PDEF.in_angle_of_out EDD.symm EFF.symm EPP, ABCDEP.cong_angle_of_out BAA BCC EDD EPP⟩,
end

lemma le_angle.left_comm (ABCDEF : le_angle A B C D E F) :
  le_angle C B A D E F :=
begin
  obtain ⟨P, PDEF, ABCDEP⟩ := ABCDEF,
  refine ⟨P, PDEF, ABCDEP.left_comm⟩,
end

lemma lt_angle.lt_angle_of_out (ABCDEF : lt_angle A B C D E F)
  (BAA : out B A A') (BCC : out B C C')
  (EDD : out E D D') (EFF : out E F F') :
  lt_angle A' B C' D' E F' :=
⟨ABCDEF.1.le_angle_of_out BAA BCC EDD EFF,
 λ i, ABCDEF.2 (i.cong_angle_of_out BAA.symm BCC.symm EDD.symm EFF.symm)⟩

lemma lt_angle.left_comm (ABCDEF : lt_angle A B C D E F) :
  lt_angle C B A D E F :=
⟨ABCDEF.1.left_comm, λ h, ABCDEF.2 h.left_comm⟩

lemma le_angle.ne_ : le_angle A B C D E F → A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E
| ⟨P, h₁, h₂⟩ := ⟨h₂.nAB, h₂.nCB, h₂.nDE, h₁.2.1⟩
lemma le_angle.nAB (h : le_angle A B C D E F) : A ≠ B := h.ne_.1
lemma le_angle.nCB (h : le_angle A B C D E F) : C ≠ B := h.ne_.2.1
lemma le_angle.nDE (h : le_angle A B C D E F) : D ≠ E := h.ne_.2.2.1
lemma le_angle.nFE (h : le_angle A B C D E F) : F ≠ E := h.ne_.2.2.2

lemma cong_angle.le (h : cong_angle A B C D E F) : le_angle A B C D E F :=
⟨_, in_angle_right h.nDE h.nFE, h⟩

-- 11.32
lemma le_angle_refl (nAB : A ≠ B) (nCB : C ≠ B) : le_angle A B C A B C :=
(cong_angle.refl nAB nCB).le

lemma out.le_angle (h : out B A C) (nDE : D ≠ E) (nFE : F ≠ E) : le_angle A B C D E F :=
⟨D, in_angle_left nDE nFE, h.cong_angle_of_out nDE.out⟩

-- l11_27
lemma in_angle.le_angle (hP : in_angle P A B C) : le_angle A B P A B C :=
⟨_, hP, cong_angle.refl hP.1 hP.2.2.1⟩

lemma le_angle.in_angle_of_one_side (ABPABC : le_angle A B P A B C) (h : one_side A B C P) :
  in_angle P A B C :=
begin
  obtain ⟨Q, QABC, ABPABQ⟩ := ABPABC,
  have nABC : ¬ col A B C := λ i, h.not_col_left i.rotate',
  have nABP : ¬ col A B P := λ i, h.not_col_right i.rotate',
  have nABQ : ¬ col A B Q := λ i, nABP (ABPABQ.symm.col_of_col i),
  have : one_side B A P Q := (h.right_symm.trans (QABC.one_side nABC nABQ)).left_symm,
  have := angle_construction_uniqueness' nABP (cong_angle.refl ABPABQ.nAB ABPABQ.nCB) ABPABQ this,
  apply QABC.in_angle_of_out ABPABQ.nAB.out QABC.2.1.out this,
end

lemma one_side.in_angle_of_in_angle_cong (DEFQ : one_side D E F Q)
  (ABCDEF : cong_angle A B C D E F) (ABPDEQ : cong_angle A B P D E Q)
  (CABQ : in_angle P A B C) :
  in_angle Q D E F :=
begin
  have nABC : ¬ col A B C := λ h, DEFQ.not_col_left (ABCDEF.col_of_col h).rotate',
  have nABP : ¬ col A B P := λ h, DEFQ.not_col_right (ABPDEQ.col_of_col h).rotate',
  have ABCP := CABQ.one_side nABC nABP,
  have PBCQEF : cong_angle P B C Q E F :=
    (ABCDEF.comm.one_side ABPDEQ ABCP.left_symm DEFQ.left_symm).comm,
  obtain ⟨nAB, nCB, nPB, X, AXC, BXP⟩ := id CABQ,
  have nXB : X ≠ B,
  { rintro rfl,
    apply nABC AXC.col },
  replace BXP := BXP.resolve_left nXB,
  obtain ⟨D', EDD, EDBA⟩ := segment_construction_3 ABCDEF.nDE.symm nAB.symm,
  obtain ⟨F', EFF, EFBC⟩ := segment_construction_3 ABCDEF.nFE.symm nCB.symm,
  obtain ⟨X', EQX, EXBX⟩ := segment_construction_3 ABPDEQ.nFE.symm nXB.symm,
  have DXF : betw D' X' F',
  { apply AXC.betw_of_congs,
    { apply ABPDEQ.cong_of_out nAB.out BXP EDD.symm EQX.symm EDBA.symm EXBX.symm },
    { apply ABCDEF.cong_of_out nAB.out nCB.out EDD.symm EFF.symm EDBA.symm EFBC.symm, },
    { apply PBCQEF.cong_of_out BXP nCB.out EQX.symm EFF.symm EXBX.symm EFBC.symm, } },
  have QDEF : in_angle Q D' E F' := ⟨EDD.2.1, EFF.2.1, EQX.1, X', DXF, or.inr EQX.symm⟩,
  apply QDEF.in_angle_of_out EDD EFF EQX.1.out,
end

lemma l11_29_b (CABQ : in_angle C A B Q) (ABQDEF : cong_angle A B Q D E F) :
  le_angle A B C D E F :=
begin
  rcases betw_or_out_or_not_col A B C with ABC | BAC | ABC,
  { have DEF := ABQDEF.betw_of_betw (ABC.in_angle_betw CABQ),
    apply (ABC.cong_angle DEF ABQDEF.nAB CABQ.2.2.1.symm ABQDEF.nDE ABQDEF.nFE.symm).le },
  { apply BAC.le_angle ABQDEF.nDE ABQDEF.nFE },
  rcases betw_or_out_or_not_col D E F with DEF | EDF | DEF,
  { obtain ⟨F', DEF'⟩ := exists_not_col ABQDEF.nDE,
    obtain ⟨P, ABCDEP, EDPF⟩ := angle_construction_existence ABC DEF',
    refine ⟨P, _, ABCDEP⟩,
    rw DEF.in_angle_iff_of_ne ABQDEF.nDE ABQDEF.nFE,
    apply ABCDEP.nFE },
  { have BAQ : out B A Q := EDF.out_of_cong_angle ABQDEF.symm,
    apply ((CABQ.out_of_out BAQ).cong_angle_of_out EDF).le },
  obtain ⟨P, ABCDEP, EDPF⟩ := angle_construction_existence ABC DEF,
  refine ⟨P, _, ABCDEP⟩,
  apply one_side.in_angle_of_in_angle_cong EDPF.right_symm.left_symm ABQDEF ABCDEP CABQ,
end

-- lemma l11_29 :
--   le_angle A B C D E F ↔ ∃ Q, in_angle C A B Q ∧ cong_angle A B Q D E F :=
-- begin
--   obtain ⟨A', BAA, BAED⟩ : ∃ A', out B A A' ∧ cong B A' E D := segment_construction_3 sorry sorry,
--   -- obtain ⟨C', _⟩ : ∃ C', out B C C' ∧ cong B C' E F := segment_construction_3 sorry sorry,
--   split,
--   { rintro ⟨P, PDEF, ABCDEP⟩,
--     obtain ⟨P', BCP, BPEP⟩ : ∃ P', out B C P' ∧ cong B P' E P := segment_construction_3 sorry sorry,

--     have := angle_construction_existence,
--     -- have := l6_11_existence
--   }
-- end

lemma betw.ge_angle (h : betw D E F) (nAB : A ≠ B) (nCB : C ≠ B) (nDE : D ≠ E) (nFE : F ≠ E) :
  le_angle A B C D E F :=
begin
  obtain ⟨C', ABC', nBC'⟩ := point_construction_different A B,
  apply l11_29_b _ (betw.cong_angle ABC' h nAB nBC' nDE nFE.symm),
  rw ABC'.in_angle_iff_of_ne nAB nBC'.symm,
  apply nCB
end

-- lemma one_side.in_angle_of_in_angle_cong (DEFQ : one_side D E F Q)
--   (ABCDEF : cong_angle A B C D E F) (ABPDEQ : cong_angle A B P D E Q)
--   (CABQ : in_angle P A B C) :
--   in_angle Q D E F :=

lemma l11_30 (ABCDEF : le_angle A B C D E F) (ABCABC : cong_angle A B C A' B' C')
  (DEFDEF : cong_angle D E F D' E' F') :
  le_angle A' B' C' D' E' F' :=
begin
  obtain ⟨P, PDEF, ABCDEP⟩ := ABCDEF,
  rcases betw_or_out_or_not_col A B C with ABC | BAC | ABC,
  { have ABC' : betw A' B' C' := ABCABC.betw_of_betw ABC,
    have DEP : betw D E P := ABCDEP.betw_of_betw ABC,
    apply (ABC'.cong_angle (DEFDEF.betw_of_betw (DEP.in_angle_betw PDEF))
            ABCABC.nDE ABCABC.nFE.symm DEFDEF.nDE DEFDEF.nFE.symm).le },
  { have BAC' : out B' A' C' := BAC.out_of_cong_angle ABCABC,
    apply BAC'.le_angle DEFDEF.nDE DEFDEF.nFE },
  rcases betw_or_out_or_not_col D E F with DEF | EDF | DEF,
  { apply (DEFDEF.betw_of_betw DEF).ge_angle ABCABC.nDE ABCABC.nFE DEFDEF.nDE DEFDEF.nFE },
  { have := (PDEF.out_of_out EDF).out_of_cong_angle (ABCABC.symm.trans ABCDEP).symm,
    apply this.le_angle DEFDEF.nDE DEFDEF.nFE },
  have ABC' : ¬ col A' B' C' := λ ABC', ABC (ABCABC.symm.col_of_col ABC'),
  have DEF' : ¬ col D' E' F' := λ DEF', DEF (DEFDEF.symm.col_of_col DEF'),
  obtain ⟨P', ABCDEP', EDPF'⟩ := angle_construction_existence ABC' DEF',
  refine ⟨_, _, ABCDEP'⟩,
  apply EDPF'.left_symm.right_symm.in_angle_of_in_angle_cong DEFDEF _ PDEF,
  apply ABCDEP.symm.trans (ABCABC.trans ABCDEP'),
end

lemma le_angle.right_comm (ABCDEF : le_angle A B C D E F) :
  le_angle A B C F E D :=
l11_30 ABCDEF (cong_angle.refl ABCDEF.nAB ABCDEF.nCB) (cong_angle_pseudo_refl ABCDEF.nDE ABCDEF.nFE)

lemma lt_angle.right_comm (ABCDEF : lt_angle A B C D E F) :
  lt_angle A B C F E D :=
⟨ABCDEF.1.right_comm, λ h, ABCDEF.2 h.right_comm⟩

lemma le_angle.comm (ABCDEF : le_angle A B C D E F) :
  le_angle C B A F E D :=
ABCDEF.left_comm.right_comm

lemma lt_angle.comm (ABCDEF : lt_angle A B C D E F) :
  lt_angle C B A F E D :=
ABCDEF.left_comm.right_comm

lemma le_angle.trans {G H I : α} (ABCDEF : le_angle A B C D E F) (DEFGHI : le_angle D E F G H I) :
  le_angle A B C G H I :=
begin
  obtain ⟨Q, QGHI, DEFGHQ⟩ := DEFGHI,
  obtain ⟨R, RGHQ, ABCGHR⟩ := l11_30 ABCDEF (cong_angle.refl ABCDEF.nAB ABCDEF.nCB) DEFGHQ,
  refine ⟨R, RGHQ.trans QGHI, ABCGHR⟩,
end

-- lemma one_side.in_angle_of_in_angle_cong (DEFQ : one_side D E F Q)
--   (ABCDEF : cong_angle A B C D E F) (ABPDEQ : cong_angle A B P D E Q)
--   (CABQ : in_angle P A B C) :
--   in_angle Q D E F :=

lemma le_angle.antisymm_aux (ABCABD : le_angle A B C A B D) (ABDABC : le_angle A B D A B C)
  (CD : one_side A B C D) :
  cong_angle A B C A B D :=
(ABDABC.in_angle_of_one_side CD).antisymm' (ABCABD.in_angle_of_one_side CD.right_symm)

-- lemma in_angle.out_of_out (hP : in_angle P A B C) (BAC : out B A C) :
--   out B A P :=

lemma le_angle.antisymm_aux1 (ABC : betw A B C) (ABCDEF : le_angle A B C D E F)
  (DEFABC : le_angle D E F A B C) :
  cong_angle A B C D E F :=
begin
  obtain ⟨P, PDEF, ABCDEP⟩ := ABCDEF,
  have DEF := (ABCDEP.betw_of_betw ABC).in_angle_betw PDEF,
  apply ABC.cong_angle DEF ABCDEP.nAB ABCDEP.nCB.symm PDEF.1 PDEF.2.1.symm,
end

lemma le_angle.antisymm_aux2 (BAC : out B A C) (ABCDEF : le_angle A B C D E F)
  (DEFABC : le_angle D E F A B C) :
  cong_angle A B C D E F :=
begin
  obtain ⟨Q, QABC, DEFABQ⟩ := DEFABC,
  exact BAC.cong_angle_of_out ((QABC.out_of_out BAC).out_of_cong_angle DEFABQ.symm)
end

lemma le_angle.antisymm (ABCDEF : le_angle A B C D E F) (DEFABC : le_angle D E F A B C) :
  cong_angle A B C D E F :=
begin
  rcases betw_or_out_or_not_col A B C with ABC | BAC | nABC,
  { apply le_angle.antisymm_aux1 ABC ABCDEF DEFABC },
  { apply le_angle.antisymm_aux2 BAC ABCDEF DEFABC },
  rcases betw_or_out_or_not_col D E F with DEF | EDF | nDEF,
  { apply (le_angle.antisymm_aux1 DEF DEFABC ABCDEF).symm },
  { apply (le_angle.antisymm_aux2 EDF DEFABC ABCDEF).symm },
  obtain ⟨Q, QABC, DEFABQ⟩ := id DEFABC,
  have nABQ : ¬ col A B Q := λ i, nDEF (cong_angle.col_of_col DEFABQ.symm i),
  obtain ⟨P, PDEF, ABCDEP⟩ := id ABCDEF,
  have ABCABQ : le_angle A B C A B Q := l11_30 ABCDEF (cong_angle.refl QABC.1 QABC.2.1) DEFABQ,
  apply (ABCABQ.antisymm_aux QABC.le_angle (QABC.one_side nABC nABQ)).trans DEFABQ.symm,
end

lemma le_angle.lt_trans {G H I : α} (le : le_angle A B C D E F) (lt : lt_angle D E F G H I) :
  lt_angle A B C G H I :=
begin
  obtain ⟨DEFGHI, nDEFGHI⟩ := lt,
  exact ⟨le.trans DEFGHI, λ i, nDEFGHI (DEFGHI.antisymm (i.symm.le.trans le))⟩,
end

lemma lt_angle.trans_le {G H I : α} (lt : lt_angle A B C D E F) (le : le_angle D E F G H I) :
  lt_angle A B C G H I :=
begin
  obtain ⟨ABCDEF, nABCDEF⟩ := lt,
  exact ⟨ABCDEF.trans le, λ i, nABCDEF (ABCDEF.antisymm (le.trans i.symm.le))⟩,
end

lemma lt_angle.irrefl (ABCABC : lt_angle A B C A B C) :
  false :=
ABCABC.2 (cong_angle.refl ABCABC.1.nAB ABCABC.1.nCB)

lemma lt_angle.asymm (ABCDEF : lt_angle A B C D E F) (DEFABC : lt_angle D E F A B C) :
  false :=
(ABCDEF.trans_le DEFABC.1).irrefl

-- exterior angle
lemma l11_41_1 (nABC : ¬ col A B C) (BAD : betw B A D) (nDA : D ≠ A) :
  lt_angle A C B C A D :=
begin
  obtain ⟨M, MAC⟩ := midpoint_existence A C,
  obtain ⟨P, _⟩ := symmetric_point_construction M B,
  have nAB := ne12_of_not_col nABC,
  have nAC := ne13_of_not_col nABC,
  have nBC := ne23_of_not_col nABC,
  have ABCP := l7_13 MAC.symm h.symm,
  have CBAP := l7_13 MAC h.symm,
  have nAP : A ≠ P := CBAP.diff nBC.symm,
  have nAM : A ≠ M,
  { rintro rfl,
    apply nAC MAC.id' },
  have ACBCAP : cong_angle A C B C A P,
  { apply cong_angle_of_cong nAC nBC (cong.pseudo_refl _ _) ABCP CBAP },
  obtain ⟨X, AXP, MXD⟩ := inner_pasch BAD.symm h.1.symm,
  have AMC := MAC.1.out nAM.symm,
  have nDAC : ¬ col D A C,
  { intro DAC,
    apply nABC (BAD.col.rotate.trans DAC.left_symm nDA.symm) },
  have nAX : A ≠ X,
  { rintro rfl,
    apply nDAC (MXD.out_betw AMC).symm.col },
  have PCAD : in_angle P C A D,
  { have : in_angle P M A D := ⟨nAM.symm, nDA, nAP.symm, X, MXD, or.inr (AXP.out nAX.symm)⟩,
    apply this.in_angle_of_out (MAC.1.out nAM.symm).symm nDA.out nAP.symm.out },
  have nACP : ¬ col A C P,
  { intro ACP,
    apply nABC (ACBCAP.symm.col_of_col ACP.left_symm).right_symm },
  apply ACBCAP.le.lt_trans _,
  refine ⟨PCAD.le_angle, _⟩,
  have : one_side A C P D,
  { refine ⟨B, _ , _⟩,
    { exact ⟨λ i, nACP i.rotate, λ i, nABC i.left_symm, M, AMC.col.left_symm, h.1.symm⟩ },
    { exact ⟨nDAC, λ i, nABC i.left_symm, A, col_id_left, BAD.symm⟩ } },
  have nBM : B ≠ M,
  { rintro rfl,
    apply nABC AMC.col },
  have nBP : B ≠ P,
  { rintro rfl,
    apply nBM.symm h.id'' },
  have nADP : ¬ col A D P,
  { intro ADP,
    have BAP : col B A P := ADP.left_symm.of_col col_id_left BAD.col.symm nDA,
    have MAP : col M A P := BAP.of_col col_id_mid h.1.col.right_symm nBP,
    have CAP : col C A P := col_id_left.of_col MAP AMC.col nAM,
    apply nACP CAP.left_symm },
  have nAPD : ¬ out A P D := λ i, nADP i.col.right_symm,
  intro CAPCAD,
  apply nAPD (angle_construction_uniqueness' _ (cong_angle.refl nAC.symm nAP.symm) CAPCAD this),
  exact λ i, nACP i.left_symm,
end

-- exterior angle
lemma l11_41_2 (nABC : ¬ col A B C) (BAD : betw B A D) (nDA : D ≠ A) :
  lt_angle A B C C A D :=
begin
  obtain ⟨D', CAD', AD⟩ := segment_construction C A A D,
  have nDA' : D' ≠ A := AD.comm.symm.diff nDA,
  apply (l11_41_1 (λ i, nABC i.right_symm) CAD' nDA').trans_le (cong_angle.le _),
  apply (cong_angle_opposite CAD'.symm nDA' _ BAD (ne12_of_not_col nABC) nDA.symm).left_comm,
  apply (ne13_of_not_col nABC).symm
end

lemma l11_44_1_a (ABC : ¬col A B C) (ABAC : cong A B A C) : cong_angle A C B A B C :=
l11_3_bis
  (ne13_of_not_col ABC).out (ne23_of_not_col ABC).out
  (ne12_of_not_col ABC).out (ne23_of_not_col ABC).symm.out
  ABAC.symm (cong.pseudo_refl _ _) ABAC

lemma angle_lt_shift (ADB : betw A D B) (nACD : ¬ col A C D) (nBD : B ≠ D) :
  lt_angle C A B C D B :=
(l11_41_2 (λ i, nACD i.rotate) ADB nBD).left_comm.lt_angle_of_out
  (ne12_of_not_col nACD).symm.out (ADB.out (ne13_of_not_col nACD).symm)
  (ne23_of_not_col nACD).out nBD.out

lemma l11_44_2_a (ABC : ¬col A B C) : lt A B A C → lt_angle A C B A B C :=
begin
  rintro ⟨⟨C', ACC, ABAC⟩, h⟩,
  have nCC : C' ≠ C,
  { rintro rfl,
    apply h ABAC },
  have nCB' : C' ≠ B,
  { rintro rfl,
    apply ABC ACC.col },
  have nAB := ne12_of_not_col ABC,
  have nBC := ne23_of_not_col ABC,
  have CABC : in_angle C' A B C,
  { exact ⟨ne12_of_not_col ABC, nBC.symm, nCB', C', ACC, or.inr nCB'.out⟩ },
  have nAC' : A ≠ C' := ABAC.diff nAB,
  have ABCABC := CABC.le_angle,
  have nCCB : ¬ col C' C B,
  { intro CCB,
    apply ABC (col.trans' CCB ACC.col.rotate nCC).symm },
  have nABC : ¬ col A B C',
  { intro ABC',
    apply ABC (ABC'.rotate'.trans' ACC.col.left_symm nAC'.symm) },
  have ACBACB : lt_angle A C B A C' B := (angle_lt_shift ACC.symm (λ i, nCCB i.rotate') nAC').comm,
  apply ACBACB.trans_le ((l11_44_1_a nABC ABAC).le.trans ABCABC),
end

lemma l11_44_2 (ABC : ¬col A B C) : lt A B A C ↔ lt_angle A C B A B C :=
begin
  split,
  { apply l11_44_2_a ABC },
  { intro h,
    rcases trichotomy A B A C with h₁ | h₁ | h₁,
    { apply h₁ },
    { cases h.2 (l11_44_1_a ABC h₁) },
    { cases h.asymm (l11_44_2_a (λ i, ABC i.right_symm) h₁) } },
end

lemma l11_44_1 (ABC : ¬col A B C) : cong A B A C ↔ cong_angle A C B A B C :=
begin
  split,
  { apply l11_44_1_a ABC },
  intro ACBABC,
  rcases trichotomy A B A C with h₁ | h₁ | h₁,
  { cases (l11_44_2_a ABC h₁).2 ACBABC },
  { apply h₁ },
  { cases (l11_44_2_a (λ i, ABC i.right_symm) h₁).2 ACBABC.symm }
end

lemma l11_44_3 (ABC : ¬ col A B C) : le A B A C ↔ le_angle A C B A B C :=
begin
  by_cases cong A B A C,
  { simp [h.le, ((l11_44_1 ABC).1 h).le] },
  split,
  { intro h₁,
    apply ((l11_44_2 ABC).1 ⟨h₁, h⟩).1 },
  { intro h₁,
    apply ((l11_44_2 ABC).2 ⟨h₁, _⟩).1,
    rwa ←l11_44_1 ABC }
end

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
  have nBC : B ≠ C := ne12_of_not_col BCD,
  have nAC : A ≠ C := ne13_of_not_col ABC,
  rw l11_44_2 (λ i, BCD i.rotate'),
  have : le_angle C B D C A B,
  { apply @l11_30 _ _ C B A C A B,
    { rw ←l11_44_3 (λ i, ABC i.rotate),
      apply ACBC.comm },
    { apply l11_3_bis nBC.symm.out nBA.symm.out nBC.symm.out _
        (cong.refl _ _) (cong.refl _ _) (cong.refl _ _),
      apply (ADB.symm.out nDB).symm },
    { apply cong_angle.refl nAC.symm nBA } },
  apply this.lt_trans,
  apply angle_lt_shift ADB _ nDB.symm,
  intro ACD,
  apply ABC (ADB.col.trans ACD.right_symm nAD),
end

example (ABAC : le A B A C) (BDC : betw B D C) (nBD : B ≠ D) (nDC : D ≠ C) : lt A D A C :=
(BDC.le_lt nBD nDC ABAC.comm).comm

end tarski

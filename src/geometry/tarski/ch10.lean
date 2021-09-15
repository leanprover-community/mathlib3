import geometry.tarski.ch09

variables {α : Type*} [tarski α]
variables {A B C D E F A' B' C' D' P P' P'' Q Q' Q'' X Y Z : α}

namespace tarski

def reflect_l (A B P P' : α) :=
(perp A B P P' ∨ P = P') ∧ (∃ M, midpoint M P P' ∧ col M A B)

def reflect (A B P P' : α) :=
(A ≠ B ∧ reflect_l A B P P') ∨ (A = B ∧ midpoint A P P')

lemma _root_.ne.reflect_iff (nAB : A ≠ B) : reflect A B P P' ↔ reflect_l A B P P' :=
by simp [reflect, nAB]

lemma reflect_self_iff : reflect A A P P' ↔ midpoint A P P' :=
by simp [reflect]

lemma col.reflect_l_iff {A B P P' : α} (PAB : col P A B) :
  reflect_l A B P P' ↔ P = P' :=
begin
  split,
  { rintro ⟨(h' | h'), M, MPP, MAB⟩,
    { rcases eq_or_ne P M with rfl | nPM,
      { apply MPP.id' },
      have PAB' : col P' A B := MAB.of_col PAB MPP.1.col.left_symm nPM.symm,
      by_contra,
      apply l8_14_1 (h'.col h PAB.rotate PAB'.rotate) },
    apply h' },
  { rintro rfl,
    exact ⟨or.inr rfl, _, midpoint_refl, PAB⟩ }
end

lemma exists_reflect_l (A B P : α) :
  ∃ P', reflect_l A B P P' :=
begin
  by_cases col P A B,
  { exact ⟨P, by rw h.reflect_l_iff⟩ },
  { obtain ⟨M, ABM, ABPM⟩ := l8_18_existence (λ k, h k.rotate'),
    obtain ⟨P', MPP⟩ := symmetric_point_construction M P,
    refine ⟨P', or.inl _, M, MPP, ABM.rotate'⟩,
    apply (ABPM.symm.col _ col_id_mid MPP.1.col).symm,
    rintro rfl,
    apply ABPM.ne_right.symm MPP.id'' },
end

lemma exists_reflect (A B P : α) :
  ∃ P', reflect A B P P' :=
begin
  rcases eq_or_ne A B with rfl | nAB,
  { obtain ⟨P', APP⟩ := symmetric_point_construction A P,
    exact ⟨P', or.inr ⟨rfl, APP⟩⟩ },
  { obtain ⟨P', ABPP'⟩ := exists_reflect_l A B P,
    exact ⟨P', or.inl ⟨nAB, ABPP'⟩⟩ }
end

lemma unique_reflect_l (A B P P₁ P₂ : α) :
  reflect_l A B P P₁ → reflect_l A B P P₂ → P₁ = P₂ :=
begin
  by_cases col P A B,
  { rw h.reflect_l_iff,
    rw h.reflect_l_iff,
    rintro rfl rfl,
    refl },
  { rintro ⟨h₁, X₁, XPP₁, XAB₁⟩ ⟨h₂, X₂, XPP₂, XAB₂⟩,
    have nPX₁ : P ≠ X₁,
    { rintro rfl,
      apply h XAB₁ },
    have nPX₂ : P ≠ X₂,
    { rintro rfl,
      apply h XAB₂ },
    have nPP₁ : P ≠ P₁,
    { rintro rfl,
      apply nPX₁.symm XPP₁.id'' },
    have nPP₂ : P ≠ P₂,
    { rintro rfl,
      apply nPX₂.symm XPP₂.id'' },
    replace h₁ := h₁.resolve_right nPP₁,
    replace h₂ := h₂.resolve_right nPP₂,
    have : perp A B P X₁ := (h₁.symm.col nPX₁ col_id_mid XPP₁.1.col.right_symm).symm,
    have : perp A B P X₂ := (h₂.symm.col nPX₂ col_id_mid XPP₂.1.col.right_symm).symm,
    cases l8_18_uniqueness (λ k, h k.rotate') XAB₁.rotate ‹_› XAB₂.rotate ‹_›,
    apply symmetric_point_uniqueness XPP₁ XPP₂ }
end

lemma unique_reflect {P₁ P₂ : α} :
  reflect A B P P₁ → reflect A B P P₂ → P₁ = P₂ :=
begin
  rcases eq_or_ne A B with rfl | nAB,
  { simp only [reflect_self_iff],
    apply symmetric_point_uniqueness },
  { rw [nAB.reflect_iff, nAB.reflect_iff],
    apply unique_reflect_l }
end

lemma reflect_l.right_symm : ∀ {P'}, reflect_l A B P P' → reflect_l A B P' P
| P' ⟨or.inl h, M, MPP, MAB⟩ := ⟨or.inl h.right_comm, M, MPP.symm, MAB⟩
| _ ⟨or.inr rfl, M, MPP, MAB⟩ := ⟨or.inr rfl, M, MPP, MAB⟩

-- l10_4
lemma reflect.right_symm : reflect A B P P' → reflect A B P' P :=
begin
  rcases eq_or_ne A B with rfl | nAB,
  { simp only [reflect_self_iff],
    apply midpoint.symm },
  { simp only [nAB.reflect_iff],
    apply reflect_l.right_symm }
end

lemma reflect_l.left_symm : ∀ {P'}, reflect_l A B P P' → reflect_l B A P P'
| P' ⟨or.inl h, M, MPP, MAB⟩ := ⟨or.inl h.left_comm, M, MPP, MAB.right_symm⟩
| _ ⟨or.inr rfl, M, MPP, MAB⟩ := ⟨or.inr rfl, M, MPP, MAB.right_symm⟩

lemma reflect.left_symm : reflect A B P P' → reflect B A P P' :=
begin
  rcases eq_or_ne A B with rfl | nAB,
  { simp only [reflect_self_iff],
    apply id },
  { simp only [nAB.reflect_iff, nAB.symm.reflect_iff],
    apply reflect_l.left_symm }
end

-- l10_5 l10_6 both trivial

-- l10_8
lemma reflect_l_eq_self_iff : reflect_l A B P P ↔ col P A B :=
begin
  by_cases col P A B,
  { simp [h, col.reflect_l_iff] },
  { simp only [h, iff_false],
    rintro ⟨_, M, MPP, MAB⟩,
    cases MPP.id'',
    apply h MAB }
end

lemma reflect_self : reflect A B A A :=
begin
  rcases eq_or_ne A B with rfl | nAB,
  { rw reflect_self_iff,
    simp },
  { simp only [nAB.reflect_iff, reflect_l_eq_self_iff, col_id_left] }
end

lemma midpoint.col_of_reflect_l (hX : midpoint X P P') (h : reflect_l A B P P') :
  col X A B :=
begin
  obtain ⟨_, _, MPP, MAB⟩ := h,
  cases l7_17 MPP hX,
  apply MAB
end

lemma reflect_l.cong_aux (hP : reflect_l A B P P') (ZAB : col Z A B) :
  cong Z P Z P' :=
begin
  obtain ⟨X, XPP⟩ := midpoint_existence P P',
  have XAB : col X A B := XPP.col_of_reflect_l hP,
  have : perp A B P X ∨ P = X,
  { rw or_iff_not_imp_right,
    intro nPX,
    apply ((hP.1.resolve_right _).symm.col nPX col_id_mid XPP.1.col.right_symm).symm,
    rintro rfl,
    apply nPX XPP.id''.symm },
  have ZXP : per Z X P,
  { rcases this with h | rfl,
    { rw l8_15 XAB.rotate at h,
      apply h.2.2.2.2 _ _ ZAB col_id_left },
    apply per_trivial },
  apply ZXP.cong_of_midpoint XPP,
end

lemma reflect_l.cong (hP : reflect_l A B P P') (hQ : reflect_l A B Q Q') :
  cong P Q P' Q' :=
begin
  obtain ⟨X, XPP⟩ := midpoint_existence P P',
  obtain ⟨Y, YQQ⟩ := midpoint_existence Q Q',
  rcases eq_or_ne X Y with rfl | nXY,
  { apply l7_13 XPP.symm YQQ.symm },
  obtain ⟨Z, ZXY⟩ := midpoint_existence X Y,
  obtain ⟨R, ZPR⟩ := symmetric_point_construction Z P,
  obtain ⟨R', ZPR'⟩ := symmetric_point_construction Z P',
  have XAB : col X A B := XPP.col_of_reflect_l hP,
  have YAB : col Y A B := YQQ.col_of_reflect_l hQ,
  have ZAB : col Z A B := XAB.of_col YAB ZXY.1.col.right_symm nXY,
  have YRR : midpoint Y R R' := symmetry_preserves_midpoint ZPR ZXY ZPR' XPP,
  have QR := l7_13 YQQ.symm YRR.symm,
  have ZP : cong Z P Z P' := hP.cong_aux ZAB,
  have ZR : cong Z R Z R' := (ZPR.2.left_comm.symm.trans ZP).trans ZPR'.2.left_comm,
  have ZQ : cong Z Q Z Q' := hQ.cong_aux ZAB,
  rcases eq_or_ne R Z with rfl | nRZ,
  { cases ZPR.id,
    cases ZP.reverse_identity,
    apply ZQ },
  apply five_segment ZR.comm ZP QR.comm ZQ ZPR.symm.1 ZPR'.symm.1 nRZ,
end

-- l10_10
lemma reflect.cong (hP : reflect A B P P') (hQ : reflect A B Q Q') :
  cong P Q P' Q' :=
begin
  rcases eq_or_ne A B with rfl | nAB,
  { simp only [reflect_self_iff] at hP hQ,
    apply l7_13 hP.symm hQ.symm },
  { simp only [nAB.reflect_iff] at hP hQ,
    apply hP.cong hQ }
end

lemma midpoint.reflect (BCC : midpoint B C C') (AC : cong A C A C') :
  reflect A B C C' :=
begin
  rcases eq_or_ne A B with rfl | nAB,
  { rwa reflect_self_iff },
  rw nAB.reflect_iff,
  refine ⟨_, B, BCC, col_id_mid⟩,
  rw or_iff_not_imp_right,
  rintro hC,
  refine ⟨B, l8_13_2 nAB hC col_id_mid BCC.1.col.left_symm col_id_left col_id_left nAB _ _⟩,
  { rintro rfl,
    apply hC BCC.id' },
  { exact ⟨_, BCC, AC⟩, },
end

lemma l10_12_aux_aux (ABC : per A B C) (ABC' : per A' B C) (AB : cong A B A' B) :
  cong A C A' C :=
begin
  obtain ⟨Z, ZAA⟩ := midpoint_existence A A',
  have BZA : per B Z A := ⟨_, ZAA, AB.comm⟩,
  have BZAA : reflect B Z A A' := midpoint.reflect ZAA AB.comm,
  have BZBB : reflect B Z B B := reflect_self,
  obtain ⟨C₁, BCC⟩ := symmetric_point_construction B C,
  have AC : cong A C A C₁ := ABC.cong_of_midpoint BCC,
  have AC' : cong A' C A' C₁ := per.cong_of_midpoint ABC' BCC,
  rcases eq_or_ne A A' with rfl | nAA,
  { apply cong.refl },
  have ZC := l4_17 nAA.symm ZAA.1.col.rotate' AC' AC,
  apply AC.trans (BZAA.cong (BCC.reflect ZC).left_symm.right_symm),
end

lemma l10_12_aux (ABC : per A B C) (ABC' : per A' B C')
  (AB : cong A B A' B) (BC : cong B C B C') :
  cong A C A' C' :=
begin
  obtain ⟨Y, YCC⟩ := midpoint_existence C C',
  have BYCC : reflect B Y C C' := midpoint.reflect YCC BC,
  obtain ⟨A₁, BYAA⟩ := exists_reflect B Y A',
  have ABC₁ : per A₁ B C,
  { apply ABC'.of_congs (BYAA.cong reflect_self) (BYAA.cong BYCC.right_symm) _,
    apply reflect_self.cong BYCC.right_symm },
  apply (l10_12_aux_aux ABC ABC₁ (AB.trans (BYAA.cong reflect_self))).trans
    (BYAA.cong BYCC.right_symm).symm,
end

lemma l10_12 (ABC : per A B C) (ABC' : per A' B' C')
  (AB : cong A B A' B') (BC : cong B C B' C') :
  cong A C A' C' :=
begin
  obtain ⟨X, XBB⟩ := midpoint_existence B B',
  obtain ⟨A₁, XAA⟩ := symmetric_point_construction X A',
  obtain ⟨C₁, XCC⟩ := symmetric_point_construction X C',
  have AB₁ := l7_13 XAA.symm XBB,
  have AC₁ := (l7_13 XAA XCC).symm,
  have BC₁ := (l7_13 XBB XCC.symm),
  have ABC₁ := ABC'.of_congs AB₁ AC₁ BC₁,
  apply (l10_12_aux ABC ABC₁ (AB.trans AB₁) (BC.trans BC₁)).trans AC₁.symm,
end

lemma l10_14 (ABPP : reflect A B P P') (nPAB : ¬ col P A B) :
  two_sides A B P P' :=
begin
  rw (ne23_of_not_col nPAB).reflect_iff at ABPP,
  rcases ABPP with ⟨_, M, MPP, MAB⟩,
  refine ⟨nPAB, _, M, MAB, MPP.1⟩,
  intro PAB,
  apply nPAB (PAB.of_col MAB MPP.1.col.symm _),
  rintro rfl,
  cases MPP.id,
  apply nPAB MAB,
end

lemma l10_15_aux (nQAB : ¬ col Q A B) :
  ∃ P, perp A B P A ∧ one_side A B P Q :=
begin
  have nAB : A ≠ B := ne23_of_not_col nQAB,
  obtain ⟨C, ABQC⟩ := l9_10 nQAB,
  obtain ⟨P, T, ABPA, ABT, CTP : betw C T P⟩ := l8_21 nAB,
  refine ⟨P, ABPA, _⟩,
  apply one_side.right_symm,
  rw ←l9_8 ABQC,
  refine ⟨_, ABQC.2.1, T, ABT.rotate', CTP.symm⟩,
  intro PAB,
  apply ABPA.per1.not_col nAB.symm ABPA.ne_right.symm PAB.symm,
end

lemma l10_15 (AXY : col A X Y) (nQXY : ¬ col Q X Y) :
  ∃ P, perp X Y P A ∧ one_side X Y P Q :=
begin
  have nXY := (ne23_of_not_col nQXY),
  rcases eq_or_ne A Y with rfl | nAY,
  { obtain ⟨P, AXPA, AXPQ⟩ := l10_15_aux (λ h, nQXY h.right_symm),
    exact ⟨P, AXPA.left_comm, AXPQ.left_symm⟩ },
  have nQAY : ¬ col Q A Y,
  { intro QAY,
    apply nQXY (QAY.rotate.trans' AXY.right_symm nAY).rotate },
  obtain ⟨P, AYPA, AYPQ⟩ := l10_15_aux nQAY,
  exact ⟨P, AYPA.col nXY AXY.right_symm col_id_right, AYPQ.col nXY AXY.left_symm col_id_mid⟩,
end

lemma l10_16_existence (nABC : ¬ col A B C) (nABP : ¬ col A' B' P) (AB : cong A B A' B') :
  ∃ C', cong A B A' B' ∧ cong A C A' C' ∧ cong B C B' C' ∧ one_side A' B' C' P :=
begin
  obtain ⟨X, ABX, ABCX⟩ := l8_18_existence nABC,
  obtain ⟨X', -, AX, BX⟩ := l4_14 ABX AB,
  have ABX' : col A' B' X' := ABX.col_of_congs AB AX BX,
  obtain ⟨Q, ABQX', ABQP'⟩ := l10_15 ABX'.rotate' (λ h, nABP h.rotate),
  obtain ⟨C', XCQ', XC⟩ := l6_11_existence ABQX'.ne_right ABCX.ne_right.symm,
  have nABC' : ¬ col A' B' C',
  { intro ABC',
    apply ABQP'.not_col_left,
    apply col.of_col ABX'.rotate' ABC'.rotate' XCQ'.col XCQ'.1.symm },
  have : one_side A' B' C' Q,
  { rw l9_19 ABX'.rotate' XCQ'.col.rotate,
    exact ⟨XCQ', λ i, nABC' i.rotate⟩ },
  have ABCP' := one_side.trans this ABQP',
  have AXC : per A X C,
  { rcases eq_or_ne A X with rfl | nAX,
    { apply per_trivial.symm },
    apply (ABCX.col nAX.symm ABX col_id_mid).per1 },
  have AXC' : per A' X' C',
  { rcases eq_or_ne A' X' with rfl | nAX,
    { apply per_trivial.symm },
    apply perp.per1,
    apply (ABQX'.col nAX.symm ABX' col_id_mid).col' XCQ'.1 XCQ'.col.rotate' col_id_right },
  have BXC : per B X C,
  { rcases eq_or_ne B X with rfl | nBX,
    { apply per_trivial.symm },
    apply (ABCX.col nBX.symm ABX col_id_right).per1 },
  have BXC' : per B' X' C',
  { rcases eq_or_ne B' X' with rfl | nAX,
    { apply per_trivial.symm },
    apply perp.per1,
    apply (ABQX'.col nAX.symm ABX' col_id_right).col' XCQ'.1 XCQ'.col.rotate' col_id_right },
  exact ⟨C', AB, l10_12 AXC AXC' AX XC.symm, l10_12 BXC BXC' BX XC.symm, ABCP'⟩,
end

lemma l10_16 (nABC : ¬ col A B C) (nABP : ¬ col A' B' P) (AB : cong A B A' B') :
  ∃! C', cong A B A' B' ∧ cong A C A' C' ∧ cong B C B' C' ∧ one_side A' B' C' P :=
begin
  have nAB := ne12_of_not_col nABP,
  apply exists_unique_of_exists_of_unique (l10_16_existence nABC nABP AB),
  intros C' C'',
  rintro ⟨-, AC', BC', ABCP'⟩ ⟨-, AC'', BC'', ABCP''⟩,
  have ABCC : one_side A' B' C' C'' := ABCP'.trans ABCP''.right_symm,
  obtain ⟨C₁, ABCC₁⟩ := exists_reflect A' B' C'',
  have ABCC''₁ : two_sides A' B' C'' C₁ := l10_14 ABCC₁ ABCP''.not_col_left,
  have ABCC'₁ : two_sides A' B' C' C₁,
  { rw l9_8 ABCC''₁,
    apply ABCC.right_symm },
  obtain ⟨nCAB, nCAB₁, T, TAB, CTC⟩ := ABCC'₁,
  have A'C₁ : cong A' C'' A' C₁ := reflect.cong reflect_self ABCC₁,
  have B'C₁ : cong B' C'' B' C₁ := reflect.cong reflect_self.left_symm ABCC₁,
  have AC₁ : cong A' C' A' C₁ := (AC'.symm.trans (AC''.trans A'C₁)),
  have BC₁ : cong B' C' B' C₁ := (BC'.symm.trans (BC''.trans B'C₁)),
  have TC₁ : cong T C' T C₁ := l4_17 nAB TAB.rotate AC₁ BC₁,
  have TCC : midpoint T C' C₁ := ⟨CTC, TC₁.left_comm⟩,
  have ATC : per A' T C' := ⟨_, TCC, AC₁⟩,
  have BTC : per B' T C' := ⟨_, TCC, BC₁⟩,
  have nCT : C' ≠ T,
  { rintro rfl,
    apply nCAB TAB },
  have nCC : C' ≠ C₁,
  { rintro rfl,
    apply nCT CTC.identity },
  have : perp_at T A' B' C' C₁,
  { rcases eq_or_ne A' T with rfl | nAT,
    { exact l8_13_2 nAB nCC col_id_left
        CTC.col.left_symm col_id_mid col_id_left nAB.symm nCT BTC },
    { exact l8_13_2 nAB nCC TAB
      TCC.1.col.left_symm col_id_left col_id_left nAT nCT ATC } },
  have : reflect A' B' C' C₁,
  { rw nAB.reflect_iff,
    exact ⟨or.inl ⟨_, this⟩, T, TCC, TAB⟩ },
  exact unique_reflect this.right_symm ABCC₁.right_symm,
end

end tarski

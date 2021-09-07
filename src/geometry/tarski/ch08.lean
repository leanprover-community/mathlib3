import tactic.tauto
import geometry.tarski.ch07

variables {α : Type*} [tarski α]
variables {A B C D E F A' B' C' D' P Q R T U V X Y : α}

namespace tarski

def per (A B C : α) := ∃ C', midpoint B C C' ∧ cong A C A C'

-- aka `l8_2`
lemma per.symm : per A B C → per C B A :=
begin
  rintro ⟨C', BCC, AC⟩,
  obtain ⟨A', ABB⟩ := symmetric_point_construction B A,
  exact ⟨A', ABB, AC.comm.trans (l7_13 BCC ABB.symm)⟩,
end

-- aka `l8_3`
lemma per.of_col (ABC : per A B C) (BAA : col B A A') (nAB : A ≠ B) : per A' B C :=
begin
  rcases ABC with ⟨C', BCC, AC⟩,
  exact ⟨C', BCC, l4_17 nAB BAA.left_symm AC BCC.2.left_comm⟩,
end

-- aka `per_col`
lemma per.of_col' (ABC : per A B C) (BCC : col B C C') (nBC : B ≠ C) : per A B C' :=
(ABC.symm.of_col BCC nBC.symm).symm

-- aka `l8_4`
lemma per.of_midpoint (ABC : per A B C) (BCC : midpoint B C C') : per A B C' :=
begin
  rcases ABC with ⟨B', BCB, AC⟩,
  cases symmetric_point_uniqueness BCB BCC,
  exact ⟨C, BCC.symm, AC.symm⟩,
end

-- aka `l8_5`
lemma per_trivial : per A B B :=
⟨B, midpoint_refl, cong.refl _ _⟩

lemma l8_6 (ABC : per A B C) (ABC' : per A' B C) (ACA : betw A C A') :
  B = C :=
begin
  obtain ⟨C', BCC, AC⟩ := ABC,
  obtain ⟨C'', BCC', AC'⟩ := ABC',
  cases symmetric_point_uniqueness BCC BCC',
  cases l4_19 ACA AC AC',
  apply BCC.id'',
end

lemma l8_7 (ABC : per A B C) (ACB : per A C B) : B = C :=
begin
  obtain ⟨C', BCC, AC⟩ := ABC,
  obtain ⟨A', CAA⟩ := symmetric_point_construction C A,
  rcases eq_or_ne B C with rfl | nBC,
  { refl },
  have CCA : per C' C A := ACB.symm.of_col BCC.1.col nBC,
  have AC' : cong A C' A' C',
  { rcases CCA with ⟨Z, CAZ, h⟩,
    cases symmetric_point_uniqueness CAA CAZ,
    apply h.comm },
  apply l8_6 ⟨C', BCC, AC⟩ ⟨C', BCC, CAA.2.symm.left_comm.trans (AC.trans AC')⟩ CAA.1,
end

-- aka `l8_8`
lemma per.identity (AB : per A B A) : A = B :=
l8_7 per_trivial.symm AB

-- aka `l8_9`
lemma per.eq_or_eq_of_col (ABC : per A B C) (ABC' : col A B C) : A = B ∨ C = B :=
begin
  rcases eq_or_ne A B with rfl | nAB,
  { left, refl },
  apply or.inr (l8_7 (per.symm per_trivial) (ABC.of_col ABC'.left_symm nAB)),
end

-- aka `l8_10`
lemma per.of_congs (ABC : per A B C)
  (AB : cong A B A' B') (AC : cong A C A' C') (BC : cong B C B' C') :
  per A' B' C' :=
begin
  obtain ⟨D, BCD, ACAD⟩ := ABC,
  obtain ⟨D', BCD'⟩ := symmetric_point_construction B' C',
  refine ⟨D', BCD', _⟩,
  rcases eq_or_ne C B with rfl | nCB,
  { cases BC.reverse_identity,
    cases BCD'.id',
    apply cong.refl },
  suffices : cong A D A' D',
  { apply AC.symm.trans (ACAD.trans this) },
  apply (five_segment BC.comm _ AC.comm AB.comm BCD.1 BCD'.1 nCB).comm,
  apply BCD.2.symm.trans (BC.comm.trans BCD'.2),
end

-- col_col_per_per
lemma per.of_col_of_col (AXC : per A X C) (nAX : A ≠ X) (nCX : C ≠ X)
  (UAX : col U A X) (VCX : col V C X) :
  per U X V :=
((AXC.of_col UAX.symm nAX).symm.of_col VCX.symm nCX).symm

def perp_at (X A B C D : α) :=
A ≠ B ∧ C ≠ D ∧ col X A B ∧ col X C D ∧ (∀ U V, col U A B → col V C D → per U X V)

def perp (A B C D : α) := ∃ X, perp_at X A B C D

-- aka `perp_distinct`
lemma perp.ne_left : perp A B C D → A ≠ B :=
by { rintro ⟨_, h, _⟩, apply h }
lemma perp.ne_right : perp A B C D → C ≠ D :=
by { rintro ⟨_, _, h, _⟩, apply h }

-- l8_12
lemma perp_at.symm : perp_at X A B C D → perp_at X C D A B
| ⟨nAB, nCD, XAB, XCD, h⟩ := ⟨nCD, nAB, XCD, XAB, λ U V UCB VAD, (h _ _ VAD UCB).symm⟩

lemma perp_at.right_comm : perp_at X A B C D → perp_at X A B D C
| ⟨AB, CD, X₁, X₂, h⟩ := ⟨AB, CD.symm, X₁, X₂.right_symm, λ U V UAB VDC, h _ _ UAB VDC.right_symm⟩

lemma perp_at.left_comm (h : perp_at X A B C D) : perp_at X B A C D :=
h.symm.right_comm.symm

lemma perp_at.comm (h : perp_at X A B C D) : perp_at X B A D C :=
h.left_comm.right_comm

lemma perp.right_comm : perp A B C D → perp A B D C
| ⟨X, h⟩ := ⟨X, h.right_comm⟩

lemma perp.left_comm : perp A B C D → perp B A C D
| ⟨X, h⟩ := ⟨X, h.left_comm⟩

lemma perp.symm : perp A B C D → perp C D A B
| ⟨X, h⟩ := ⟨X, h.symm⟩

lemma perp.comm (h : perp A B C D) : perp B A D C :=
h.left_comm.right_comm

lemma l8_13_2 (nAB : A ≠ B) (nCD : C ≠ D) (XAB : col X A B) (XCD : col X C D)
  (UAB : col U A B) (VCD : col V C D) (nUX : U ≠ X) (nVX : V ≠ X) (UXV : per U X V) :
  perp_at X A B C D :=
begin
  refine ⟨nAB, nCD, XAB, XCD, _⟩,
  intros U' V' UAB' VCD',
  apply UXV.of_col_of_col nUX nVX,
  apply col3 nAB UAB'.rotate UAB.rotate XAB.rotate,
  apply col3 nCD VCD'.rotate VCD.rotate XCD.rotate,
end

-- potentially not useful but true
-- lemma l8_13 :
--   perp_at X A B C D ↔ A ≠ B ∧ C ≠ D ∧ col X A B ∧ col X C D ∧
--     ∃ U V, col U A B ∧ col V C D ∧ U ≠ X ∧ V ≠ X ∧ per U X V :=
-- begin
--   sorry
-- end

lemma l8_14_1 : ¬ perp A B A B :=
begin
  rintro ⟨X, nAB, -, XAB, -, h⟩,
  have : per A X A := h _ _ (betw.id_left _ _).col (betw.id_left _ _).col,
  cases this.identity,
  have : per B A B := h _ _ (betw.id_right _ _).col.rotate' (betw.id_right _ _).col.rotate',
  apply nAB.symm this.identity,
end

/-- If AB is perpendicular to CD at X and they intersect at Y, then X = Y. -/
lemma l8_14_2_1b (hX : perp_at X A B C D) (YAB : col Y A B) (YCD : col Y C D) : X = Y :=
(hX.2.2.2.2 Y Y YAB YCD).identity.symm

/-- If AB is perpendicular to CD, and they intersect at X, then AB is perpendicular to CD at X. -/
-- l8_14_2_1b_bis
lemma perp.perp_at_of_col (h : perp A B C D) (XAB : col X A B) (XCD : col X C D) :
  perp_at X A B C D :=
begin
  obtain ⟨Y, hY⟩ := h,
  cases l8_14_2_1b hY XAB XCD,
  apply hY
end

/-- If AB is perpendicular to CD and any intersection point is X, then AB is perpendicular to CD at
X. -/
lemma l8_14_2_2 (h : perp A B C D) (h' : ∀ Y, col Y A B → col Y C D → X = Y) :
  perp_at X A B C D :=
begin
  obtain ⟨Y, nAB, nCD, YAB, YCD, h⟩ := h,
  cases h' _ YAB YCD,
  exact ⟨nAB, nCD, YAB, YCD, h⟩,
end

/-- If AB is perpendicular to CD at X and Y, then X = Y. -/
-- l8_14_3
lemma perp_at.unique (hX : perp_at X A B C D) (hY : perp_at Y A B C D) : X = Y :=
l8_14_2_1b hX hY.2.2.1 hY.2.2.2.1

lemma l8_15_1 (ABX : col A B X) (ABCX : perp A B C X) :
  perp_at X A B C X :=
ABCX.perp_at_of_col ABX.rotate' col_id_mid

lemma l8_15 (ABX : col A B X) :
  perp A B C X ↔ perp_at X A B C X :=
⟨l8_15_1 ABX, λ h, ⟨X, h⟩⟩

-- similar to `perp_col0` but flipped
lemma perp.col (h : perp A B C D) (nXY : X ≠ Y) (ABX : col A B X) (ABY : col A B Y) :
  perp X Y C D :=
begin
  obtain ⟨T, nAB, nCD, TAB, TCD, h⟩ := h,
  refine ⟨T, nXY, nCD, col3 nAB TAB.rotate ABX ABY, TCD, λ U V UAB VCD, h _ _ _ VCD⟩,
  apply (col3 nXY (ABX.trans ABY nAB).rotate (ABX.trans' ABY nAB).rotate UAB.rotate).rotate',
end

-- lemma perp_col1 (nCX : C ≠ X) (ABCD : perp A B C D) (CDX : col C D X) :
--   perp A B C X :=
-- (ABCD.symm.col nCX col_id_mid CDX).symm

lemma l8_18_uniqueness (nABC : ¬ col A B C) (ABX : col A B X) (ABCX : perp A B C X)
  (ABY : col A B Y) (ABCY : perp A B C Y) : X = Y :=
begin
  have : A ≠ B := ne12_of_not_col nABC,
  have XABCX : perp_at X A B C X := l8_15_1 ABX ABCX,
  have YABCY : perp_at Y A B C Y := l8_15_1 ABY ABCY,
  have : per C X Y := (XABCX.2.2.2.2 _ _ ABY.rotate' col_id_left).symm,
  apply l8_7 this (YABCY.2.2.2.2 _ _ ABX.rotate' col_id_left).symm,
end

lemma l8_18_existence (nABC : ¬ col A B C) : ∃ X, col A B X ∧ perp A B C X :=
begin
  obtain ⟨Y, BAY, AYAC⟩ := segment_construction B A A C,
  obtain ⟨P, PCY⟩ := l7_25 AYAC.symm,
  have APY : per A P Y := ⟨C, PCY.symm, AYAC⟩,
  obtain ⟨Z, AYZ, YZYP⟩ := segment_construction A Y Y P,
  obtain ⟨Q, CYQ, YQYA⟩ := segment_construction C Y Y A,
  obtain ⟨Q', QZQ', ZQQZ'⟩ := segment_construction Q Z Q Z,
  have ZQQ' : midpoint Z Q Q' := ⟨QZQ', ZQQZ'.symm⟩,
  obtain ⟨C', QYC', YC⟩ := segment_construction Q' Y Y C,
  obtain ⟨X, XCC⟩ := l7_25 YC.symm,
  have PYQ : betw P Y Q := PCY.1.left_cancel CYQ,
  have ZQPA : cong Z Q P A := l7_13_aux YZYP YQYA AYZ.symm PYQ,
  have QZY := APY.of_congs ZQPA.symm.comm YQYA.comm.symm YZYP.comm.symm,
  obtain ⟨Q'', ZQQ'', YQ⟩ := QZY.symm,
  cases symmetric_point_uniqueness ZQQ' ZQQ'',
  have ZYX : betw Z Y X := l7_22 CYQ.symm QYC' YQ YC.symm ZQQ' XCC,
  have nAY : A ≠ Y,
  { rintro rfl,
    apply (ne13_of_not_col nABC AYAC.reverse_identity) },
  have nZY : Z ≠ Y,
  { rintro rfl,
    cases YZYP.reverse_identity,
    cases PCY.id,
    apply (nABC BAY.col.left_symm).elim },
  have ABX : col A B X := BAY.symm.col.trans' (AYZ.symm.col.trans' ZYX.col nZY) nAY.symm,
  have nCX : C ≠ X,
  { rintro rfl,
    apply nABC ABX },
  have BYZ : betw B Y Z := BAY.trans AYZ nAY,
  have QQ : Q ≠ Q',
  { rintro rfl,
    cases QZQ'.identity,
    apply nABC (col3 nZY.symm AYZ.col.rotate BYZ.col.rotate CYQ.col.rotate) },
  have nYQ : Y ≠ Q,
  { rintro rfl,
    apply QQ YQ.reverse_identity },
  have nYX : Y ≠ X,
  { rintro rfl,
    have nCY : C' ≠ Y := XCC.2.right_comm.diff nCX,
    have nYP : Y ≠ P := YZYP.diff nZY.symm,
    have CYP' : betw C' Y P := (PCY.1.left_cancel XCC.1).symm,
    have YPQ := CYP'.col.trans' QYC'.symm.col nCY,
    have YQQ : col Y Q Q' := col.trans PYQ.col.left_symm YPQ nYP,
    have QZY := ZQQ'.1.col.right_symm.trans YQQ.rotate QQ,
    have : col Y Z C := QZY.rotate'.trans CYQ.col.rotate nYQ,
    apply nABC (col3 nZY.symm AYZ.col.rotate BYZ.col.rotate this) },
  have : perp_at X Y Z C X,
  { apply l8_13_2 nZY.symm nCX ZYX.symm.col col_id_mid col_id_left col_id_left nYX nCX,
    exact ⟨_, XCC, YC.symm⟩ },
  refine ⟨X, ABX, X, _⟩,
  refine ⟨ne12_of_not_col nABC, nCX, ABX.rotate', col_id_mid, _⟩,
  intros U V UAB VCX,
  apply this.2.2.2.2 U V _ VCX,
  have BUY : col B U Y := UAB.rotate.trans' BAY.col.left_symm (ne12_of_not_col nABC),
  apply (BUY.rotate'.trans BYZ.col.left_symm _).left_symm,
  rintro rfl,
  apply nAY.symm BAY.identity,
end

lemma l8_18 (nABC : ¬ col A B C) : ∃! X, col A B X ∧ perp A B C X :=
begin
  apply exists_unique_of_exists_of_unique (l8_18_existence nABC),
  rintro X Y ⟨ABX, ABCX⟩ ⟨ABY, ABCY⟩,
  exact l8_18_uniqueness nABC ABX ABCX ABY ABCY,
end

-- `per_perp_in`
lemma per.perp_at (ABC : per A B C) (nAB : A ≠ B) (nBC : B ≠ C) : perp_at B A B B C :=
⟨nAB, nBC, by simp, by simp, λ U V UAB VBC, ABC.of_col_of_col nAB nBC.symm UAB VBC.right_symm⟩

-- `per_perp`
lemma per.perp (ABC : per A B C) (nAB : A ≠ B) (nBC : B ≠ C) : perp A B B C :=
⟨B, ABC.perp_at nAB nBC⟩

-- `perp_perp_in`
lemma perp.perp_at (h : perp A B C A) : perp_at A A B C A :=
l8_15_1 col_id_mid h

-- `per_not_colp`
lemma per.not_colp (BAP : per B A P) (ABR : per A B R) (nAB : A ≠ B) (nAP : A ≠ P) (nBR : B ≠ R) :
  ¬ col P A R :=
λ PAR, nAB (l8_7 (BAP.symm.of_col PAR.left_symm nAP.symm) ABR.symm)

lemma per.not_col (ABC : per A B C) (nAB : A ≠ B) (nBC : B ≠ C) : ¬ col A B C :=
λ ABC', nBC.symm ((ABC.eq_or_eq_of_col ABC').resolve_left nAB)

lemma l8_20_1 (ABC : per A B C) (PCD : midpoint P C' D) (ACC : midpoint A C' C)
  (BDC : midpoint B D C) : per B A P :=
begin
  obtain ⟨B', ABB⟩ := symmetric_point_construction A B,
  obtain ⟨D', ADD⟩ := symmetric_point_construction A D,
  obtain ⟨P', APP⟩ := symmetric_point_construction A P,
  rcases eq_or_ne A B with rfl | nAB,
  { apply per_trivial.symm },
  refine ⟨P', APP, _⟩,
  have BBC : per B' B C := ABC.of_col ABB.1.col nAB,
  have BBC' : per B B' C' :=
    BBC.of_congs (cong_pseudo_refl _ _) (l7_13 ABB ACC) (l7_13 ABB.symm ACC),
  have BDC' : midpoint B' D' C' := symmetry_preserves_midpoint ADD ABB ACC.symm BDC,
  have PCD' : midpoint P' C D' := symmetry_preserves_midpoint ACC APP ADD PCD,
  have ACAD : cong A C A D,
  { obtain ⟨D'', BDC'', ACAD⟩ := ABC,
    cases symmetric_point_uniqueness BDC'' BDC.symm,
    apply ACAD },
  have PCD'' : midpoint P C' D := symmetry_preserves_midpoint PCD.symm midpoint_refl PCD PCD.symm,
  have CD : cong C D C' D' := l7_13 ACC ADD.symm,
  have CD' : cong C' D C D' := l7_13 ACC.symm ADD.symm,
  have PD : cong P D P' D' := l7_13 APP.symm ADD.symm,
  have PDPC : cong P D P' C := cong.trans PD PCD'.symm.2.left_comm,
  apply (l4_2 PCD.1 PCD'.1.symm CD'.right_comm PDPC _ BDC.2.right_comm).comm,
  obtain ⟨D'', BCD'', BCBD⟩ := BBC',
  cases symmetric_point_uniqueness BCD'' BDC'.symm,
  apply BCBD.comm,
end

lemma l8_20_2 (PCD : midpoint P C' D) (ACC : midpoint A C' C)
  (BDC : midpoint B D C) (nBC : B ≠ C) : A ≠ P :=
begin
  rintro rfl,
  cases symmetric_point_uniqueness ACC PCD,
  apply nBC BDC.id'',
end

-- looking at the proof in the textbook, this could be simplified?
lemma l8_21_aux (nABC : ¬ col A B C) : ∃ P T, perp A B P A ∧ col A B T ∧ betw C T P :=
begin
  obtain ⟨X, ABX, ABCX⟩ := l8_18_existence nABC,
  have XABCX : perp_at X A B C X := l8_15_1 ABX ABCX,
  have AXC : per A X C := XABCX.2.2.2.2 _ _ col_id_left col_id_left,
  obtain ⟨C', XCC, AC⟩ := XABCX.2.2.2.2 _ _ col_id_left col_id_left,
  obtain ⟨C'', ACC'⟩ := symmetric_point_construction A C,
  obtain ⟨P, PCC⟩ := l7_25 (AC.symm.right_comm.trans ACC'.2),
  have XAP : per X A P := l8_20_1 AXC PCC.symm ACC'.symm XCC.symm,
  have nXC : X ≠ C,
  { rintro rfl,
    apply nABC ABX },
  have nAP : A ≠ P := l8_20_2 PCC.symm ACC'.symm XCC.symm nXC,
  obtain ⟨T, PTC : betw P T C, ATX : betw A T X⟩ := l3_17 ACC'.1.symm XCC.1.symm PCC.1.symm,
  refine ⟨P, T, _⟩,
  rcases eq_or_ne A X with rfl | nAX,
  { cases ATX.identity,
    refine ⟨_, col_id_mid, PTC.symm⟩,
    apply (perp.col ABCX.symm nAP.symm PTC.symm.col col_id_right).symm },
  refine ⟨⟨A, ne12_of_not_col nABC, nAP.symm, col_id_left, col_id_mid, _⟩, _, PTC.symm⟩,
  { intros U V UAB VPA,
    apply XAP.of_col_of_col nAX.symm nAP.symm _ VPA,
    apply (ABX.trans UAB.rotate (ne12_of_not_col nABC)).symm },
  apply ABX.right_symm.trans ATX.col.right_symm nAX,
end

lemma l8_21 (nAB : A ≠ B) : ∃ P T, perp A B P A ∧ col A B T ∧ betw C T P :=
begin
  by_cases ABC : col A B C,
  { obtain ⟨C', nABC⟩ := exists_not_col nAB,
    obtain ⟨P, T, ABPA, ABT, CTP⟩ := l8_21_aux nABC,
    exact ⟨P, C, ABPA, ABC, betw.id_left _ _⟩ },
  apply l8_21_aux ABC,
end

lemma perp.per1 (h : perp A B C A) : per B A C :=
h.perp_at.2.2.2.2 _ _ (by simp) (by simp)

lemma perp.per2 (h : perp A B A C) : per B A C :=
h.right_comm.per1

-- `per_cong`
lemma per.cong (BAP : per B A P) (ABR : per A B R) (nAB : A ≠ B) (nAP : A ≠ P)
  (APBR : cong A P B R) (ABX : col A B X) (PXR : betw P X R) :
  cong A R P B :=
begin
  have PAB : per P A B := BAP.symm,
  have PAX : per P A X := PAB.of_col' ABX nAB,
  have RBX : per R B X := (per.of_col ABR ABX.left_symm nAB).symm,
  rcases eq_or_ne B R with rfl | nBR,
  { cases APBR.identity,
    apply cong.refl },
  obtain ⟨Q, BRQ⟩ := symmetric_point_construction R B,
  have nBQ : B ≠ Q,
  { rintro rfl,
    apply nBR.symm BRQ.id'' },
  obtain ⟨P', APP⟩ := symmetric_point_construction A P,
  have ABQ : per A B Q := ABR.of_col' BRQ.1.col nBR,
  have nAX : A ≠ X,
  { rintro rfl,
    apply BAP.not_colp RBX.symm nAB nAP nBR PXR.col },
  obtain ⟨R', PXR', XR⟩ := segment_construction P' X X R,
  obtain ⟨M, MRR⟩ := l7_25 XR.symm,
  have XMR : per X M R := ⟨R', MRR, XR.symm⟩,
  have XP : cong X P X P',
  { obtain ⟨P'', APP', h⟩ := PAX.symm,
    cases symmetric_point_uniqueness APP APP',
    apply h },
  have nPP : P ≠ P',
  { rintro rfl,
    apply nAP APP.id'' },
  have nXP' : X ≠ P',
  { rintro rfl,
    apply nPP.symm XP.identity },
  have nXP : X ≠ P := XP.symm.diff nXP',
  have XPP : ¬ col X P P',
  { intro h,
    have : col P A X := (APP.1.col.right_symm.trans h.rotate nPP),
    obtain ⟨rfl | rfl⟩ := per.eq_or_eq_of_col PAX this,
    { apply nAP rfl },
    { apply nAX h_1.symm } },
  have AXM : betw A X M := l7_22 PXR PXR' XP XR.symm APP MRR,
  have nXR : X ≠ R,
  { rintro rfl,
    apply nBR RBX.identity.symm },
  have nXR' : X ≠ R' := XR.symm.diff nXR,
  have nMX : M ≠ X,
  { rintro rfl,
    apply XPP (PXR.col.rotate.trans (MRR.1.col.rotate.trans PXR'.col.rotate nXR') nXR) },
  have AXR : ¬ col A X R,
  { intro AXR,
    apply ABR.not_col nAB nBR (ABX.right_symm.trans AXR nAX) },
  have : M = B,
  { apply l8_18_uniqueness AXR AXM.col _ ABX.right_symm,
    apply ((ABR.perp nAB nBR).col nAX.symm ABX col_id_mid).comm,
    apply (XMR.perp nMX.symm _).comm.col nAX AXM.col.symm col_id_right,
    rintro rfl,
    apply AXR AXM.col },
  subst M,
  have RP : cong R P' R' P :=
    five_segment XP.comm XR.symm (cong_pseudo_refl _ _) XP.symm PXR PXR' nXP.symm,
  apply (l4_2_bis APP.1.symm MRR.1.symm _ APBR RP.left_comm (cong_pseudo_refl _ _)).right_comm,
  apply APP.2.symm.comm.trans (APBR.trans MRR.2.comm),
end

lemma perp.cong (nAB : A ≠ B) (nAP : A ≠ P) (ABPA : perp A B P A) (ABRB : perp A B R B)
  (APBR : cong A P B R) (ABX : col A B X) (PXR : betw P X R) :
  cong A R P B :=
per.cong ABPA.per1 ABRB.left_comm.per1 nAB nAP APBR ABX PXR

lemma l8_24 (PAAB : perp P A A B) (QBAB : perp Q B A B) (ABT : col A B T) (PTQ : betw P T Q)
  (BRQ : betw B R Q) (APBR : cong A P B R) :
  ∃ X, midpoint X A B ∧ midpoint X P R :=
begin
  obtain ⟨X, TXB, RXP⟩ := inner_pasch PTQ BRQ,
  have ABX : col A B X,
  { rcases eq_or_ne T B with rfl | nTB,
    { cases TXB.identity,
      assumption },
    apply (ABT.symm.trans' TXB.col.right_symm nTB).left_symm },
  have nBR : B ≠ R,
  { rintro rfl,
    apply PAAB.ne_left.symm APBR.identity },
  have ABQ : ¬ col A B Q,
  { intro h,
    have : A = B ∨ Q = B := per.eq_or_eq_of_col QBAB.symm.comm.per2 h,
    rcases this with rfl | rfl,
    { apply PAAB.ne_right rfl, },
    { apply QBAB.ne_left rfl } },
  have ABR : ¬ col A B R,
  { intro h,
    apply ABQ (h.rotate.trans BRQ.col nBR).left_symm },
  have nPR : P ≠ R,
  { rintro rfl,
    cases RXP.identity,
    apply ABR ABX },
  have nAP : A ≠ P,
  { rintro rfl,
    apply PAAB.ne_left rfl },
  have : perp A B R B := (perp.col QBAB nBR.symm BRQ.col.rotate' col_id_right).symm,
  have ARPB : cong A R P B := perp.cong QBAB.ne_right nAP PAAB.symm this APBR ABX RXP.symm,
  have APB : ¬col A P B,
  { intro APB,
    apply nAP.symm ((PAAB.symm.per1.eq_or_eq_of_col APB.rotate').resolve_left PAAB.ne_right.symm) },
  refine ⟨X, l7_21 APB nPR APBR ARPB.symm.right_comm ABX.right_symm RXP.symm.col⟩,
end

lemma midpoint_existence_aux (ABQB : perp A B Q B) (ABPA : perp A B P A)
  (ABT : col A B T) (QTP : betw Q T P) (APBQ : le A P B Q) :
  ∃ X, midpoint X A B :=
begin
  obtain ⟨R, BRQ, APBR⟩ := APBQ,
  obtain ⟨X, XAB, -⟩ := l8_24 ABPA.symm ABQB.symm ABT QTP.symm BRQ APBR,
  exact ⟨X, XAB⟩
end

lemma midpoint_existence (A B : α) : ∃ X, midpoint X A B :=
begin
  rcases eq_or_ne A B with rfl | nAB,
  { exact ⟨A, midpoint_refl⟩ },
  obtain ⟨Q, -, ABQA, -, - : betw A _ Q⟩ := l8_21 nAB.symm,
  obtain ⟨P, T, ABPA, ABT, QTP : betw Q T P⟩ := l8_21 nAB,
  cases le.cases A P B Q,
  { apply midpoint_existence_aux ABQA.left_comm ABPA ABT QTP h, },
  { obtain ⟨X, h⟩ := midpoint_existence_aux ABPA.left_comm ABQA ABT.left_symm QTP.symm h,
    exact ⟨X, h.symm⟩ },
end

end tarski

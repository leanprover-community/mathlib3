import tactic.tauto
import geometry.tarski.ch08

variables {α : Type*} [tarski α]
variables {A B C D E F A' B' C' D' P Q R S U V X Y : α}

namespace tarski

-- P and Q are on opposite sides of the line A,B
def two_sides (A B P Q : α) := ¬ col P A B ∧ ¬ col Q A B ∧ ∃ T, col T A B ∧ betw P T Q
def one_side (A B P Q : α) := ∃ R, two_sides A B P R ∧ two_sides A B Q R

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

-- l9_3
-- l9_4_1

lemma l9_4_2_aux (SCRA : le S C R A) (PQAC : two_sides P Q A C) (RPQ : col R P Q)
  (PQAR : perp P Q A R) (SPQ : col S P Q) (PQCS : perp P Q C S) (RUA : out R U A)
  (SVC : out S V C) : two_sides P Q U V :=
sorry

lemma l9_4_2 (tsPQAC : two_sides P Q A C) (RPQ : col R P Q) (pPQAC : perp P Q A R)
  (SPQ : col S P Q) (PQCS : perp P Q C S) (RUA : out R U A) (SVC : out S V C) :
  two_sides P Q U V :=
sorry

lemma l9_5 (PQAC : two_sides P Q A C) (RPQ : col R P Q) (RAB : out R A B) :
  two_sides P Q B C :=
sorry

lemma outer_pasch (ACP : betw A C P) (BQC : betw B Q C) :
  ∃ X, betw A X B ∧ betw P Q X :=
sorry


end tarski

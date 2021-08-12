import tactic.tauto
import geometry.tarski.ch10

variables {α : Type*} [tarski α]
variables {A B C D E F A' B' C' D' P Q X Y : α}

namespace tarski

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


end

end tarski

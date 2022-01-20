import tactic

example : ¬Π {α} (P : α → α → Prop),
  (∃! (x y : α), P x y) ↔
  (∃! (xy : α × α), P xy.fst xy.snd) :=
begin
  intros h,
  specialize (@h Prop (∨)),
  obtain this := h.1,
  rw ← @not_not (∃! (xy : Prop × Prop), xy.fst ∨ xy.snd) at this,
  refine this _ _,
  refine ⟨false, ⟨true, ⟨by simp, λ j, by simp⟩⟩, λ j hj, _⟩,

  simp at hj,
  rcases hj with ⟨P, Q | hP, hPP⟩,
  simp [Q] at hPP,
  exact (not_iff.mpr (hPP (¬j)) (hPP j)).elim,
  simp at hPP,
  exfalso,
  obtain F := hPP (¬ P),
  simp [hP] at F,
  apply F,
  fconstructor,
  simp,
  refine this ⟨(true, true), by simpa using λ a b, and.intro⟩ _,
  simp,

  by_contra at this,

  sorry
end

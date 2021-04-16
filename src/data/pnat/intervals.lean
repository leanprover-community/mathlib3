/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.pnat.basic
import data.finset.intervals

namespace pnat

/-- `Ico l u` is the set of positive natural numbers `l ≤ k < u`. -/
def Ico (l u : ℕ+) : finset ℕ+ :=
(finset.Ico l u).attach.map
  { to_fun := λ n, ⟨(n : ℕ), lt_of_lt_of_le l.2 (finset.Ico.mem.1 n.2).1⟩,
    -- why can't we do this directly?
    inj' := λ n m h, subtype.eq (by { replace h := congr_arg subtype.val h, exact h }) }

@[simp] lemma Ico.mem : ∀ {n m l : ℕ+}, l ∈ Ico n m ↔ n ≤ l ∧ l < m :=
by { rintro ⟨n, hn⟩ ⟨m, hm⟩ ⟨l, hl⟩, simp [pnat.Ico] }

@[simp] lemma Ico.card (l u : ℕ+) : (Ico l u).card = u - l := by simp [pnat.Ico]

end pnat

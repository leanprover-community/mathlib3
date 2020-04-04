/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison
-/
import data.pnat.basic
import data.finset

namespace pnat

/-- `Ico l u` is the set of positive natural numbers `l ≤ k < u`. -/
def Ico (l u : ℕ+) : finset ℕ+ :=
(finset.Ico l u).attach.map
  { to_fun := λ n, ⟨(n : ℕ), lt_of_lt_of_le l.2 (finset.Ico.mem.1 n.2).1⟩,
    inj := λ n m h, subtype.ext.2 (by { replace h := congr_arg subtype.val h, exact h }) } -- why can't we do this directly?

@[simp] lemma Ico.mem {n m l : ℕ+} : l ∈ Ico n m ↔ n ≤ l ∧ l < m :=
begin
  dsimp [Ico],
  simp only [finset.mem_attach, finset.mem_map, function.embedding.coe_fn_mk, exists_prop_of_true, subtype.exists],
  split,
  { rintro ⟨a, ⟨h, rfl⟩⟩,
    simp at h,
    exact ⟨h.1, h.2⟩ },
  { rintro ⟨h₁, h₂⟩,
    use l,
    split; simp,
    exact ⟨h₁, h₂⟩ }
end

@[simp] lemma Ico.card (l u : ℕ+) : (Ico l u).card = u - l := by simp [pnat.Ico]

end pnat

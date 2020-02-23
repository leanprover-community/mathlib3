/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.set.intervals
import data.set.finite
import data.fintype
import data.pnat.basic

/-!
# fintype instances for intervals

We provide `fintype` instances for `Ico l u`, for `l u : ℕ`, and for `l u : ℤ`.
-/

namespace pnat

/-- `Ico_ℕ+ l u` is the set of positive natural numbers `l ≤ k < u`. -/
def Ico (l u : ℕ+) : finset ℕ+ :=
(finset.Ico l u).attach.map
  { to_fun := λ n, ⟨n.1, lt_of_lt_of_le l.2 (finset.Ico.mem.1 n.2).1⟩,
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

end pnat

namespace set

instance Ico_ℕ_fintype (l u : ℕ) : fintype (Ico l u) :=
fintype.of_finset (finset.Ico l u) $
  (λ n, by { simp only [mem_Ico, finset.Ico.mem], })

instance Ico_pnat_fintype (l u : ℕ+) : fintype (Ico l u) :=
fintype_of_finset (pnat.Ico l u) $
  (λ n, by { simp only [mem_Ico, pnat.Ico.mem], })

instance Ico_ℤ_fintype (l u : ℤ) : fintype (Ico l u) :=
fintype.of_finset (finset.Ico_ℤ l u) $
  (λ n, by { simp only [mem_Ico, finset.Ico_ℤ.mem], })

-- TODO other useful instances: fin n, zmod?

end set

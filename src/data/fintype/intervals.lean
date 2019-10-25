/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.set.intervals
import data.fintype
import tactic

/-!
# fintype instances for intervals

We provide `fintype` instances for `Ico l u`, for `l u : ℕ`, and for `l u : ℤ`.
-/

universe u

namespace finset

@[simp] lemma mem_to_set {α : Type u} {s : finset α} {a : α} : a ∈ s.to_set ↔ a ∈ s :=
by { dsimp [finset.to_set], simp, }

def Ico_int (l u : ℤ) : finset ℤ :=
(finset.range (u - l).to_nat).map
  { to_fun := λ n, n + l,
    inj := λ n m h, by simpa using h }

namespace Ico_int

@[simp] lemma mem {n m l : ℤ} : l ∈ Ico_int n m ↔ n ≤ l ∧ l < m :=
begin
  dsimp [Ico_int],
  simp only [int.lt_to_nat, exists_prop, mem_range, add_comm, function.embedding.coe_fn_mk, mem_map],
  split,
  { rintro ⟨a, ⟨h, rfl⟩⟩,
    exact ⟨int.le.intro rfl, lt_sub_iff_add_lt'.mp h⟩ },
  { rintro ⟨h₁, h₂⟩,
    use (l - n).to_nat,
    split; simp [h₁, h₂], }
end

end Ico_int

end finset

namespace set

-- `T` is an explicit argument for readability at the call site.
def fintype_of_eq_finset_to_set {α : Type u} {S : set α} (T : finset α) (h : S = T.to_set) : fintype S :=
{ elems := T.attach.map
  { to_fun := λ v, ⟨v.1, begin rw h, simp only [finset.mem_to_set], exact v.2, end⟩,
    inj := λ a b h, subtype.ext.2 (by simpa using h) },
  complete := λ v,
  begin
    simp only [finset.mem_attach, finset.mem_map, exists_prop_of_true],
    use v.1,
    have t := v.2,
    conv at t { congr, skip, rw h, },
    simp only [finset.mem_to_set] at t,
    use t,
    apply subtype.ext.2,
    refl,
  end }

instance Ico_ℕ_fintype (l u : ℕ) : fintype (Ico l u) :=
fintype_of_eq_finset_to_set (finset.Ico l u) $
  set.ext (λ n, by { simp only [finset.mem_to_set, mem_Ico, finset.Ico.mem], })

instance Ico_ℤ_fintype (l u : ℤ) : fintype (Ico l u) :=
fintype_of_eq_finset_to_set (finset.Ico_int l u) $
  set.ext (λ n, begin simp only [finset.mem_to_set, mem_Ico, finset.Ico_int.mem], end)

-- TODO other useful instances: pnat, fin n, zmod?

end set

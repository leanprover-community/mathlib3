/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.set.intervals
import data.set.finite
import data.pnat.intervals

/-!
# fintype instances for intervals

We provide `fintype` instances for `Ico l u`, for `l u : ℕ`, and for `l u : ℤ`.
-/

namespace set

instance Ico_ℕ_fintype (l u : ℕ) : fintype (Ico l u) :=
fintype.of_finset (finset.Ico l u) $
  (λ n, by { simp only [mem_Ico, finset.Ico.mem], })

@[simp] lemma Ico_ℕ_card (l u : ℕ) : fintype.card (Ico l u) = u - l :=
calc fintype.card (Ico l u) = (finset.Ico l u).card : fintype.card_of_finset _ _
                        ... = u - l                 : finset.Ico.card l u

instance Ico_pnat_fintype (l u : ℕ+) : fintype (Ico l u) :=
fintype.of_finset (pnat.Ico l u) $
  (λ n, by { simp only [mem_Ico, pnat.Ico.mem], })

@[simp] lemma Ico_pnat_card (l u : ℕ+) : fintype.card (Ico l u) = u - l :=
calc fintype.card (Ico l u) = (pnat.Ico l u).card : fintype.card_of_finset _ _
                        ... = u - l               : pnat.Ico.card l u

instance Ico_ℤ_fintype (l u : ℤ) : fintype (Ico l u) :=
fintype.of_finset (finset.Ico_ℤ l u) $
  (λ n, by { simp only [mem_Ico, finset.Ico_ℤ.mem], })

@[simp] lemma Ico_ℤ_card (l u : ℤ) : fintype.card (Ico l u) = (u - l).to_nat :=
calc fintype.card (Ico l u) = (finset.Ico_ℤ l u).card : fintype.card_of_finset _ _
                        ... = (u - l).to_nat          : finset.Ico_ℤ.card l u

lemma Ico_ℤ_finite (l u : ℤ) : set.finite (Ico l u) := ⟨set.Ico_ℤ_fintype l u⟩
lemma Ioo_ℤ_finite (l u : ℤ) : set.finite (Ioo l u) := Ico_ℤ_finite (l + 1) u
lemma Icc_ℤ_finite (l u : ℤ) : set.finite (Icc l u) :=
begin
  convert Ico_ℤ_finite l (u + 1),
  ext,
  simp only [int.lt_add_one_iff, iff_self, mem_Ico, mem_Icc],
end
lemma Ioc_ℤ_finite (l u : ℤ) : set.finite (Ioc l u) := Icc_ℤ_finite (l + 1) u

instance (l u : ℤ) : fintype (Ioo l u) :=
fintype.of_finset (finset.Ico_ℤ (l+1) u) $ λ n,
  by simp only [mem_Ioo, finset.Ico_ℤ.mem, int.add_one_le_iff, iff_self, implies_true_iff]

instance (l u : ℤ) : fintype (Icc l u) :=
fintype.of_finset (finset.Ico_ℤ l (u+1)) $ λ n,
  by simp only [mem_Icc, finset.Ico_ℤ.mem, int.lt_add_one_iff, iff_self, implies_true_iff]

instance (l u : ℤ) : fintype (Ioc l u) :=
fintype.of_finset (finset.Ico_ℤ (l+1) (u+1)) $ λ n,
  by simp only [mem_Ioc, finset.Ico_ℤ.mem, int.add_one_le_iff, int.lt_add_one_iff,
    iff_self, implies_true_iff]

-- TODO other useful instances: fin n, zmod?

end set

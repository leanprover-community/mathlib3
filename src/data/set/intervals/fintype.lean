/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.set.intervals
import data.fintype

namespace set

local attribute [simp] list.mem_range

lemma mem_Ico_iff_mem_list_Ico {l u n : ℕ} : n ∈ Ico l u ↔ n ∈ list.Ico l u :=
by simp

instance Ico_ℕ_fintype (l u : ℕ) : fintype (Ico l u) :=
fintype.of_list
  ((list.Ico l u).attach.map (λ v, ⟨v, mem_Ico_iff_mem_list_Ico.mpr v.2⟩))
  (λ x, begin
          simp only [list.mem_map, list.mem_attach, true_and, subtype.exists],
          exact ⟨x, mem_Ico_iff_mem_list_Ico.mp x.2, subtype.ext.2 rfl⟩,
        end)

instance Ico_ℤ_fintype (l u : ℤ) : fintype (Ico l u) :=
let ls : list (Ico l u) :=
(list.range (u - l).to_nat).attach.map (λ n,
  ⟨(n : ℤ) + l,
   begin
     cases n,
     simp only [add_comm, le_add_iff_nonneg_right, mem_Ico],
     simp only [list.mem_range, int.lt_to_nat] at n_property,
     exact ⟨trivial, lt_sub_iff_add_lt'.mp n_property⟩,
   end⟩) in
fintype.mk ls.to_finset
begin
  rintro ⟨x,⟨hl,hu⟩⟩,
  simp only [list.mem_map, list.mem_to_finset, list.mem_attach,
    subtype.mk_eq_mk, subtype.exists, subtype.coe_mk, coe_coe],
  exact ⟨(x - l).to_nat, by simpa [hl], by simp [hl]⟩,
end

end set

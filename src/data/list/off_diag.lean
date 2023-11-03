/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.list.perm
import data.list.join

/-
# The off-diagonal list

This file defines `list.off_diag`, the list of pair of elements taken from non-equal indices.
-/

variables {α : Type*}

namespace list

-- private def off_diag_aux : list α → list α → list (α × α)
-- | as [] := []
-- | as (x :: xs) := (as ++ xs).map (prod.mk x) ++ off_diag_aux (as ++ [x]) xs

-- /-- The list of pairs taken from unequal indices in a list-/
-- def off_diag : list α → list (α × α) := off_diag_aux []

def off_diag_aux : list α → list (list (α × α))
| [] := []
| (x :: xs) := xs.map (λ y, (x, y)) ::
  zip_with(λ x' l, (x', x) :: l) xs (off_diag_aux xs)

def off_diag (l : list α) : list (α × α) := (off_diag_aux l).join

#eval [1, 2, 3].off_diag

@[simp] lemma off_diag_nil : off_diag ([] : list α) = [] := rfl

lemma perm.off_diag {l₁ l₂ : list α} (h : l₁ ~ l₂) : l₁.off_diag ~ l₂.off_diag :=
begin
  simp only [off_diag],
  induction h with x xs₁ xs₂ hxs ih x₁ x₂ xs xs₁ xs₂ xs₃ h₁₂ h₂₃ ih₁₂ ih₂₃,
  { simp [off_diag_aux] },
  { simp [off_diag_aux],
    refine (hxs.map _).append _,
    refine perm.join _,
    sorry },
  { simp only [off_diag_aux, map_cons, zip_with, join, ←append_assoc, zip_with],
    refine perm_append_comm.append _,
    rw [zip_with_zip_with_right, zip_with_zip_with_right, zip_with3_same_left, zip_with3_same_left],
    apply perm.join_congr _,
    rw forall₂_iff_nth_le,
    split,
    { simp },
    { intros i hi hj,
      simpa using perm.swap _ _ _, } },
  { refine ih₁₂.trans ih₂₃}
end

#check list.zip

lemma nodup.off_diag {l : list α} (h : l.nodup) : l.off_diag.nodup :=
sorry

-- bonus, likely needs some assumptions on `r`
lemma sorted.off_diag (r : α → α → Prop) {l : list α} (h : l.sorted r) :
  l.off_diag.sorted (prod.lex r r) :=
sorry

end list

def multiset.off_diag : multiset α → multiset (α × α) :=
quotient.map list.off_diag $ λ l₁ l₂, list.perm.off_diag

lemma multiset.nodup.off_diag {s : multiset α} (h : s.nodup) : s.off_diag.nodup :=
begin
  induction s using quotient.induction_on,
  exact list.nodup.off_diag h,
end

def finset.off_diag (s : finset α) : finset (α × α) := ⟨_, s.nodup.off_diag⟩

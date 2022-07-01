/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import data.fin.interval

/-!
# The structure of `fintype (fin n)`

This file contains some basic results about the `fintype` instance for `fin`,
especially properties of `finset.univ : finset (fin n)`.
-/


open finset
open fintype

namespace fin

@[simp] lemma Ioi_zero_eq_map {n : ℕ} :
  Ioi (0 : fin n.succ) = univ.map (fin.succ_embedding _).to_embedding :=
begin
  ext i,
  simp only [mem_Ioi, mem_map, mem_univ, function.embedding.coe_fn_mk, exists_true_left],
  split,
  { refine cases _ _ i,
    { rintro ⟨⟨⟩⟩ },
    { intros j _, exact ⟨j, rfl⟩ } },
  { rintro ⟨i, _, rfl⟩,
    exact succ_pos _ },
end

@[simp] lemma Ioi_succ {n : ℕ} (i : fin n) :
  Ioi i.succ = (Ioi i).map (fin.succ_embedding _).to_embedding :=
begin
  ext i,
  simp only [mem_filter, mem_Ioi, mem_map, mem_univ, true_and,
  function.embedding.coe_fn_mk, exists_true_left],
  split,
  { refine cases _ _ i,
    { rintro ⟨⟨⟩⟩ },
    { intros i hi,
      refine ⟨i, succ_lt_succ_iff.mp hi, rfl⟩ } },
  { rintro ⟨i, hi, rfl⟩, simpa },
end

end fin

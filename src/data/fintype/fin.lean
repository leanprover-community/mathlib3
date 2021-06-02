/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import data.fin
import data.fintype.basic
/-!
# The structure of `fintype (fin n)`

This file contains some basic results about the `fintype` instance for `fin`,
especially properties of `finset.univ : finset (fin n)`.
-/


open finset
open fintype

namespace fin

@[simp]
lemma univ_filter_zero_lt {n : ℕ} :
  (univ : finset (fin n.succ)).filter (λ i, 0 < i) =
    univ.map (fin.succ_embedding _).to_embedding :=
begin
  ext i,
  simp only [mem_filter, mem_map, mem_univ, true_and,
  function.embedding.coe_fn_mk, exists_true_left],
  split,
  { refine cases _ _ i,
    { rintro ⟨⟨⟩⟩ },
    { intros i _, exact ⟨i, mem_univ _, rfl⟩ } },
  { rintro ⟨i, _, rfl⟩,
    exact succ_pos _ },
end

@[simp]
lemma univ_filter_succ_lt {n : ℕ} (j : fin n) :
  (univ : finset (fin n.succ)).filter (λ i, j.succ < i) =
    (univ.filter (λ i, j < i)).map (fin.succ_embedding _).to_embedding :=
begin
  ext i,
  simp only [mem_filter, mem_map, mem_univ, true_and,
  function.embedding.coe_fn_mk, exists_true_left],
  split,
  { refine cases _ _ i,
    { rintro ⟨⟨⟩⟩ },
    { intros i hi,
      exact ⟨i, mem_filter.mpr ⟨mem_univ _, succ_lt_succ_iff.mp hi⟩, rfl⟩ } },
  { rintro ⟨i, hi, rfl⟩,
    exact succ_lt_succ_iff.mpr (mem_filter.mp hi).2 },
end

end fin

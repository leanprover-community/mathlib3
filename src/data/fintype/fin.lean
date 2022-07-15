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

variables {α β : Type*} {n : ℕ}

@[simp] lemma Ioi_zero_eq_map :
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

@[simp] lemma Ioi_succ (i : fin n) :
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

lemma card_filter_univ_fin (p : (fin (n + 1)) → Prop) [decidable_pred p] :
  (univ.filter p).card = (ite (p 0) 1 0) + (univ.filter (p ∘ fin.succ)).card :=
let s : finset (fin (n + 1)) := (univ.map $ (succ_embedding n).to_embedding) in
have this : ∀ a, a ∈ ({0} : finset (fin (n + 1))) → a ∉ s,
{ refine λ a ha ha', _,
  have : ∃ b, fin.succ b = a := by simpa using ha',
  exact let ⟨b, hb⟩ := this in fin.succ_ne_zero b (hb.trans (finset.mem_singleton.1 ha)) },
calc (filter p univ).card = (filter p (disj_union {0} s this)).card :
    by { congr, exact finset.ext (λ x, by simpa [@eq_comm _ x] using fin.eq_zero_or_eq_succ x) }
  ... = ite (p 0) 1 0 + (filter p s).card :
    by { rw [filter_disj_union, card_disj_union, filter_singleton], split_ifs; simp }
  ... =  ite (p 0) 1 0 + (filter (p ∘ fin.succ) univ).card :
    by { simp only [s, finset.map_filter, finset.card_map], refl }

lemma card_filter_univ_eq_nth_eq_count [decidable_eq α] (a : α) (v : vector α n) :
  (univ.filter $ λ i, a = v.nth i).card = v.to_list.count a :=
begin
  refine vector.induction_on v (by simp) (_),
  intros n' x xs hxs,
  simp_rw [card_filter_univ_fin, vector.nth_cons_zero, vector.to_list_cons,
    function.comp, vector.nth_cons_succ, hxs, list.count_cons', add_comm (ite (a = x) 1 0)]
end

end fin

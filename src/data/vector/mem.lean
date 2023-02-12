/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.vector.basic
/-!
# Theorems about membership of elements in vectors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains theorems for membership in a `v.to_list` for a vector `v`.
Having the length available in the type allows some of the lemmas to be
  simpler and more general than the original version for lists.
In particular we can avoid some assumptions about types being `inhabited`,
  and make more general statements about `head` and `tail`.
-/

namespace vector
variables {α β : Type*} {n : ℕ} (a a' : α)

@[simp] lemma nth_mem (i : fin n) (v : vector α n) : v.nth i ∈ v.to_list :=
by { rw nth_eq_nth_le,  exact list.nth_le_mem _ _ _ }

lemma mem_iff_nth (v : vector α n) : a ∈ v.to_list ↔ ∃ i, v.nth i = a :=
by simp only [list.mem_iff_nth_le, fin.exists_iff, vector.nth_eq_nth_le];
  exact ⟨λ ⟨i, hi, h⟩, ⟨i, by rwa to_list_length at hi, h⟩,
    λ ⟨i, hi, h⟩, ⟨i, by rwa to_list_length, h⟩⟩

lemma not_mem_nil : a ∉ (vector.nil : vector α 0).to_list := id

lemma not_mem_zero (v : vector α 0) : a ∉ v.to_list :=
(vector.eq_nil v).symm ▸ (not_mem_nil a)

lemma mem_cons_iff (v : vector α n) :
  a' ∈ (a ::ᵥ v).to_list ↔ a' = a ∨ a' ∈ v.to_list :=
by rw [vector.to_list_cons, list.mem_cons_iff]

lemma mem_succ_iff (v : vector α (n + 1)) :
  a ∈ v.to_list ↔ a = v.head ∨ a ∈ v.tail.to_list :=
begin
  obtain ⟨a', v', h⟩ := exists_eq_cons v,
  simp_rw [h, vector.mem_cons_iff, vector.head_cons, vector.tail_cons],
end

lemma mem_cons_self (v : vector α n) : a ∈ (a ::ᵥ v).to_list :=
(vector.mem_iff_nth a (a ::ᵥ v)).2 ⟨0, vector.nth_cons_zero a v⟩

@[simp] lemma head_mem (v : vector α (n + 1)) : v.head ∈ v.to_list :=
(vector.mem_iff_nth v.head v).2 ⟨0, vector.nth_zero v⟩

lemma mem_cons_of_mem (v : vector α n) (ha' : a' ∈ v.to_list) : a' ∈ (a ::ᵥ v).to_list :=
(vector.mem_cons_iff a a' v).2 (or.inr ha')

lemma mem_of_mem_tail (v : vector α n) (ha : a ∈ v.tail.to_list) : a ∈ v.to_list :=
begin
  induction n with n hn,
  { exact false.elim (vector.not_mem_zero a v.tail ha) },
  { exact (mem_succ_iff a v).2 (or.inr ha) }
end

lemma mem_map_iff (b : β) (v : vector α n) (f : α → β) :
  b ∈ (v.map f).to_list ↔ ∃ (a : α), a ∈ v.to_list ∧ f a = b :=
by rw [vector.to_list_map, list.mem_map]

lemma not_mem_map_zero (b : β) (v : vector α 0) (f : α → β) : b ∉ (v.map f).to_list :=
by simpa only [vector.eq_nil v, vector.map_nil, vector.to_list_nil] using list.not_mem_nil b

lemma mem_map_succ_iff (b : β) (v : vector α (n + 1)) (f : α → β) :
  b ∈ (v.map f).to_list ↔ f v.head = b ∨ ∃ (a : α), a ∈ v.tail.to_list ∧ f a = b :=
by rw [mem_succ_iff, head_map, tail_map, mem_map_iff, @eq_comm _ b]

end vector

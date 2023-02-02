/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Scott Morrison
-/
import data.list.of_fn
import data.list.perm

/-!
# Lists of elements of `fin n`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file develops some results on `fin_range n`.
-/

universe u

namespace list
variables {α : Type u}

@[simp] lemma map_coe_fin_range (n : ℕ) : (fin_range n).map coe = list.range n :=
begin
  simp_rw [fin_range, map_pmap, fin.coe_mk, pmap_eq_map],
  exact list.map_id _
end

lemma fin_range_succ_eq_map (n : ℕ) :
  fin_range n.succ = 0 :: (fin_range n).map fin.succ :=
begin
  apply map_injective_iff.mpr fin.coe_injective,
  rw [map_cons, map_coe_fin_range, range_succ_eq_map, fin.coe_zero, ←map_coe_fin_range, map_map,
    map_map, function.comp, function.comp],
  congr' 2 with x,
  exact (fin.coe_succ _).symm,
end

@[simp] lemma map_nth_le (l : list α) :
  (fin_range l.length).map (λ n, l.nth_le n n.2) = l :=
ext_le (by rw [length_map, length_fin_range]) $ λ n _ h,
by { rw ← nth_le_map_rev, congr, { rw nth_le_fin_range, refl }, { rw length_fin_range, exact h } }

theorem of_fn_eq_pmap {α n} {f : fin n → α} :
  of_fn f = pmap (λ i hi, f ⟨i, hi⟩) (range n) (λ _, mem_range.1) :=
by rw [pmap_eq_map_attach]; from ext_le (by simp)
  (λ i hi1 hi2, by { simp at hi1, simp [nth_le_of_fn f ⟨i, hi1⟩, -subtype.val_eq_coe] })

theorem of_fn_id (n) : of_fn id = fin_range n := of_fn_eq_pmap

theorem of_fn_eq_map {α n} {f : fin n → α} :
  of_fn f = (fin_range n).map f :=
by rw [← of_fn_id, map_of_fn, function.right_id]

theorem nodup_of_fn_of_injective {α n} {f : fin n → α} (hf : function.injective f) :
  nodup (of_fn f) :=
by { rw of_fn_eq_pmap, exact (nodup_range n).pmap (λ _ _ _ _ H, fin.veq_of_eq $ hf H) }

theorem nodup_of_fn {α n} {f : fin n → α} :
  nodup (of_fn f) ↔ function.injective f :=
begin
  refine ⟨_, nodup_of_fn_of_injective⟩,
  refine fin.cons_induction _ (λ n x₀ xs ih, _) f,
  { intro h,
    exact function.injective_of_subsingleton _ },
  { intro h,
    rw fin.cons_injective_iff,
    simp_rw [of_fn_succ, fin.cons_succ, nodup_cons, fin.cons_zero, mem_of_fn] at h,
    exact h.imp_right ih }
end

end list

open list

lemma equiv.perm.map_fin_range_perm {n : ℕ} (σ : equiv.perm (fin n)) :
  map σ (fin_range n) ~ fin_range n :=
begin
  rw [perm_ext ((nodup_fin_range n).map σ.injective) $ nodup_fin_range n],
  simpa only [mem_map, mem_fin_range, true_and, iff_true] using σ.surjective
end

/-- The list obtained from a permutation of a tuple `f` is permutation equivalent to
the list obtained from `f`. -/
lemma equiv.perm.of_fn_comp_perm {n : ℕ} {α : Type u} (σ : equiv.perm (fin n)) (f : fin n → α) :
  of_fn (f ∘ σ) ~ of_fn f :=
begin
  rw [of_fn_eq_map, of_fn_eq_map, ←map_map],
  exact σ.map_fin_range_perm.map f,
end

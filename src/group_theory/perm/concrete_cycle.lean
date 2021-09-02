/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import group_theory.perm.list
import data.list.cycle
import group_theory.perm.cycle_type

/-!

# Properties of cyclic permutations constructed from lists

## Main results

In the following, `{α : Type*} [fintype α] [decidable_eq α]`.

* `list.is_cycle_form_perm`: a nontrivial list without duplicates, when interpreted as
  a permutation, is cyclic

-/

open equiv equiv.perm list

namespace list

variables {α : Type*} [decidable_eq α] {l l' : list α}

lemma form_perm_disjoint_iff (hl : nodup l) (hl' : nodup l')
  (hn : 2 ≤ l.length) (hn' : 2 ≤ l'.length) :
  perm.disjoint (form_perm l) (form_perm l') ↔ l.disjoint l' :=
begin
  rw [disjoint_iff_eq_or_eq, list.disjoint],
  split,
  { rintro h x hx hx',
    specialize h x,
    rw [form_perm_apply_mem_eq_self_iff _ hl _ hx,
        form_perm_apply_mem_eq_self_iff _ hl' _ hx'] at h,
    rcases h with hl | hl'; linarith },
  { intros h x,
    by_cases hx : x ∈ l; by_cases hx' : x ∈ l',
    { exact (h hx hx').elim },
    all_goals { have := form_perm_eq_self_of_not_mem _ _ ‹_›, tauto } }
end

lemma is_cycle_form_perm (hl : nodup l) (hn : 2 ≤ l.length) :
  is_cycle (form_perm l) :=
begin
  cases l with x l,
  { norm_num at hn },
  induction l with y l IH generalizing x,
  { norm_num at hn },
  { use x,
    split,
    { rwa form_perm_apply_mem_ne_self_iff _ hl _ (mem_cons_self _ _) },
    { intros w hw,
      have : w ∈ (x :: y :: l) := mem_of_form_perm_ne_self _ _ hw,
      obtain ⟨k, hk, rfl⟩ := nth_le_of_mem this,
      use k,
      simp only [gpow_coe_nat, form_perm_pow_apply_head _ _ hl k, nat.mod_eq_of_lt hk] } }
end

lemma pairwise_same_cycle_form_perm (hl : nodup l) (hn : 2 ≤ l.length) :
  pairwise (l.form_perm.same_cycle) l :=
pairwise.imp_mem.mpr (pairwise_of_forall (λ x y hx hy, (is_cycle_form_perm hl hn).same_cycle
  ((form_perm_apply_mem_ne_self_iff _ hl _ hx).mpr hn)
  ((form_perm_apply_mem_ne_self_iff _ hl _ hy).mpr hn)))

lemma cycle_of_form_perm (hl : nodup l) (hn : 2 ≤ l.length) (x) :
  cycle_of l.attach.form_perm x = l.attach.form_perm :=
have hn : 2 ≤ l.attach.length := by rwa ← length_attach at hn,
have hl : l.attach.nodup := by rwa ← nodup_attach at hl,
(is_cycle_form_perm hl hn).cycle_of_eq
  ((form_perm_apply_mem_ne_self_iff _ hl _ (mem_attach _ _)).mpr hn)

lemma cycle_type_form_perm (hl : nodup l) (hn : 2 ≤ l.length) :
  cycle_type l.attach.form_perm = {l.length} :=
begin
  rw ←length_attach at hn,
  rw ←nodup_attach at hl,
  rw cycle_type_eq [l.attach.form_perm],
  { simp only [map, function.comp_app],
    rw [support_form_perm_of_nodup _ hl, card_to_finset, erase_dup_eq_self.mpr hl],
    { simpa },
    { intros x h,
      simpa [h, nat.succ_le_succ_iff] using hn } },
  { simp },
  { simpa using is_cycle_form_perm hl hn },
  { simp }
end

lemma form_perm_apply_mem_eq_next (hl : nodup l) (x : α) (hx : x ∈ l) :
  form_perm l x = next l x hx :=
begin
  obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx,
  rw [next_nth_le _ hl, form_perm_apply_nth_le _ hl]
end

end list

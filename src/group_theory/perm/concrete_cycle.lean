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

In the following, `{α : Type*} [fintype α] [decidable_eq α]`.

## Main definitions

* `cycle.form_perm`: the cyclic permutation created by looping over a `cycle α`

## Main results

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

namespace cycle

variables {α : Type*} [decidable_eq α] (s s' : cycle α)

/--
A cycle `s : cycle α` , given `nodup s` can be interpreted as a `equiv.perm α`
where each element in the list is permuted to the next one, defined as `form_perm`.
-/
def form_perm : Π (s : cycle α) (h : nodup s), equiv.perm α :=
λ s, quot.hrec_on s (λ l h, form_perm l)
  (λ l₁ l₂ (h : l₁ ~r l₂),
    begin
      ext,
      { exact h.nodup_iff },
      { intros h₁ h₂ _,
        exact heq_of_eq (form_perm_eq_of_is_rotated h₁ h) }
    end)

@[simp] lemma form_perm_coe (l : list α) (hl : l.nodup) :
  form_perm (l : cycle α) hl = l.form_perm := rfl

lemma form_perm_subsingleton (s : cycle α) (h : subsingleton s) :
  form_perm s h.nodup = 1 :=
begin
  induction s using quot.induction_on,
  simp only [form_perm_coe, mk_eq_coe],
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe] at h,
  cases s with hd tl,
  { simp },
  { simp only [length_eq_zero, add_le_iff_nonpos_left, list.length, nonpos_iff_eq_zero] at h,
    simp [h] }
end

lemma is_cycle_form_perm (s : cycle α) (h : nodup s) (hn : nontrivial s) :
  is_cycle (form_perm s h) :=
begin
  induction s using quot.induction_on,
  exact list.is_cycle_form_perm h (length_nontrivial hn)
end

lemma support_form_perm [fintype α] (s : cycle α) (h : nodup s) (hn : nontrivial s) :
  support (form_perm s h) = s.to_finset :=
begin
  induction s using quot.induction_on,
  refine support_form_perm_of_nodup s h _,
  rintro _ rfl,
  simpa [nat.succ_le_succ_iff] using length_nontrivial hn
end

lemma form_perm_eq_self_of_not_mem (s : cycle α) (h : nodup s) (x : α) (hx : x ∉ s) :
  form_perm s h x = x :=
begin
  induction s using quot.induction_on,
  simpa using list.form_perm_eq_self_of_not_mem _ _ hx
end

lemma form_perm_apply_mem_eq_next (s : cycle α) (h : nodup s) (x : α) (hx : x ∈ s) :
  form_perm s h x = next s h x hx :=
begin
  induction s using quot.induction_on,
  simpa using list.form_perm_apply_mem_eq_next h _ _
end

lemma form_perm_reverse (s : cycle α) (h : nodup s) :
  form_perm s.reverse (nodup_reverse_iff.mpr h) = (form_perm s h)⁻¹ :=
begin
  induction s using quot.induction_on,
  simpa using form_perm_reverse _ h
end

lemma form_perm_eq_form_perm_iff {α : Type*} [decidable_eq α]
  {s s' : cycle α} {hs : s.nodup} {hs' : s'.nodup} :
  s.form_perm hs = s'.form_perm hs' ↔ s = s' ∨ s.subsingleton ∧ s'.subsingleton :=
begin
  rw [cycle.length_subsingleton_iff, cycle.length_subsingleton_iff],
  revert s s',
  intros s s',
  apply quotient.induction_on₂' s s',
  intros l l',
  simpa using form_perm_eq_form_perm_iff
end

end cycle

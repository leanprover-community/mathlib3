/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.list.rotate
import group_theory.perm.support

/-!
# Permutations from a list

A list `l : list α` can be interpreted as a `equiv.perm α` where each element in the list
is permuted to the next one, defined as `form_perm`. When we have that `nodup l`,
we prove that `equiv.perm.support (form_perm l) = l.to_finset`, and that
`form_perm l` is rotationally invariant, in `form_perm_rotate`.

-/

namespace list

variables {α β : Type*}

section form_perm

variables [decidable_eq α] (l : list α)

open equiv equiv.perm

/-
A list `l : list α` can be interpreted as a `equiv.perm α` where each element in the list
is permuted to the next one, defined as `form_perm`. When we have that `nodup l`,
we prove that `equiv.perm.support (form_perm l) = l.to_finset`, and that
`form_perm l` is rotationally invariant, in `form_perm_rotate`.
-/
def form_perm : equiv.perm α :=
(zip_with equiv.swap l (l.rotate 1)).tail.prod

@[simp] lemma form_perm_nil : form_perm ([] : list α) = 1 := rfl

@[simp] lemma form_perm_singleton (x : α) : form_perm [x] = 1 := rfl

@[simp] lemma form_perm_pair (x y : α) : form_perm [x, y] = swap y x := rfl

lemma form_perm_cons_cons_cons (x y z : α) (xs : list α) :
  form_perm (x :: y :: z :: xs) = swap y z * form_perm (x :: z :: xs) :=
begin
  cases xs with w xs,
  { simp [form_perm] },
  { rw [form_perm, zip_with_rotate_one, tail_cons, cons_append, zip_with_cons_cons,
        ←tail_cons x (z :: w :: xs), ←tail_cons z (w :: xs ++ [x]),
        ←rotate_zero (z :: (w :: xs ++ [x])), ←cons_append, ←rotate_cons_succ,
        ←zip_with_distrib_tail, prod_cons, ←form_perm, tail_cons] }
end

lemma form_perm_apply_last_concat (x y : α) (xs : list α) (h : nodup (x :: (xs ++ [y]))) :
  form_perm (x :: (xs ++ [y])) y = x :=
begin
  cases xs with z xs,
  { simp },
  induction xs with w xs IH generalizing x y z,
  { simp only [mem_cons_iff, cons_append, nodup_nil, and_true, not_mem_nil, singleton_append,
               nodup_cons, not_false_iff, and_self, mem_singleton] at h,
    push_neg at h,
    simp [form_perm, swap_apply_of_ne_of_ne, h] },
  { simp only [mem_cons_iff, cons_append, nodup_nil, and_true, not_mem_nil, singleton_append,
               nodup_cons, not_false_iff, and_self, mem_singleton] at h,
    push_neg at h,
    simp_rw [cons_append],
    rw [form_perm_cons_cons_cons, mul_apply, ←cons_append, IH],
    { simp [swap_apply_of_ne_of_ne, h] },
    { simp [h] } }
end

lemma form_perm_apply_last (x : α) (xs : list α) (h : nodup (x :: xs)) :
  form_perm (x :: xs) ((x :: xs).last (cons_ne_nil x xs)) = x :=
begin
  induction xs using list.reverse_rec_on with xs y IH generalizing x,
  { simp },
  { simpa using form_perm_apply_last_concat x y xs h }
end

lemma form_perm_apply_nth_le_length (x : α) (xs : list α) (h : nodup (x :: xs)) :
  form_perm (x :: xs) ((x :: xs).nth_le xs.length (by simp)) = x :=
begin
  rw nth_le_cons_length,
  exact form_perm_apply_last x xs h
end

@[simp] lemma form_perm_apply_head (x y : α) (xs : list α) :
  form_perm (x :: y :: xs) x = y :=
begin
  induction xs with z xs IH generalizing x y,
  { simp },
  { rw [form_perm_cons_cons_cons, mul_apply, IH, swap_apply_right] }
end

lemma form_perm_apply_concat (x y : α) (xs : list α) (h : nodup (x :: (xs ++ [y]))) :
  form_perm (x :: (xs ++ [y])) y = x :=
begin
  convert form_perm_apply_last x (xs ++ [y]) h,
  simp
end

lemma zip_with_swap_prod_support (l l' : list α) :
  (zip_with swap l l').prod.support ≤ l.to_finset ⊔ l'.to_finset :=
begin
  refine (support_prod_le (zip_with swap l l')).trans _,
  rw map_zip_with,
  induction l with hd tl hl generalizing l',
  { simp },
  { cases l' with hd' tl',
    { simp },
    { simp only [set.union_subset_iff, mem_cons_iff, set.sup_eq_union, set.bot_eq_empty,
                 zip_with_cons_cons, foldr, set.le_eq_subset],
      split,
      { by_cases h : hd = hd',
        { simp [h] },
        { rw support_swap h,
          intros x hx,
          simp only [set.mem_insert_iff, set.mem_singleton_iff] at hx,
          rcases hx with (rfl | rfl);
          simp } },
      { refine (hl _).trans _,
        intros x hx,
        simp only [set.sup_eq_union, set.mem_union_eq, finset.mem_coe, mem_to_finset] at hx,
        cases hx with hx hx;
        simp [hx] } } }
end

lemma support_form_perm_le : support (form_perm l) ≤ l.to_finset :=
begin
  rw [form_perm, zip_with_distrib_tail],
  refine (zip_with_swap_prod_support l.tail _).trans _,
  rintro x (hx | hx),
  { simp only [finset.mem_coe, mem_to_finset] at hx ⊢,
    exact tail_subset _ hx },
  { simp only [finset.mem_coe, mem_to_finset] at hx ⊢,
    refine (list.subset.trans (tail_subset _) (perm.subset _)) hx,
    exact rotate_perm l 1 }
end

lemma support_form_perm_finite : (support (form_perm l)).finite :=
set.finite.subset (l.to_finset.finite_to_set) (support_form_perm_le _)

lemma form_perm_not_mem_apply (x : α) (l : list α) (h : x ∉ l) :
  form_perm l x = x :=
begin
  have : x ∉ support (form_perm l),
    { intro H,
      refine h _,
      simpa using support_form_perm_le l H },
  simpa
end

lemma form_perm_apply_lt (xs : list α) (h : nodup xs) (n : ℕ) (hn : n + 1 < xs.length) :
  form_perm xs (xs.nth_le n ((nat.lt_succ_self n).trans hn)) = xs.nth_le (n + 1) hn :=
begin
  induction n with n IH generalizing xs,
  { cases xs with x xs,
    { simp },
    cases xs with y xs,
    { simp },
    { simp } },
  { cases xs with x xs,
    { simp },
    cases xs with y xs,
    { simp },
    cases xs with z xs,
    { simpa [nat.succ_lt_succ_iff] using hn },
    { rw [form_perm_cons_cons_cons],
      simp only [mem_cons_iff, cons_append, nodup_nil, and_true, not_mem_nil, singleton_append,
                nodup_cons, not_false_iff, and_self, mem_singleton] at h,
      push_neg at h,
      cases n,
      { have : y ∉ (x :: z :: xs),
        { simp [h, h.left.left.symm] },
        simp [form_perm_not_mem_apply _ _ this] },
      { rw [mul_apply],
        have : ∀ (hz), (x :: y :: z :: xs).nth_le n.succ.succ hz =
          (x :: z :: xs).nth_le n.succ (by simpa [nat.succ_lt_succ_iff] using hz),
          { simp },
        have hn' : n.succ + 1 < (x :: z :: xs).length,
          { simpa [nat.succ_lt_succ_iff] using hn },
        rw [this, IH _ _ hn', swap_apply_of_ne_of_ne],
        { simp },
        { have : y ∉ xs := by simp [h],
          simp only [ne.def, nth_le],
          rintro rfl,
          exact this (nth_le_mem _ _ _) },
        { have : z ∉ xs := by simp [h],
          simp only [ne.def, nth_le],
          intro hz,
          rw [←hz] at this,
          exact this (nth_le_mem _ _ _) },
        { simp [h] } } } }
end

-- useful for rewrites
lemma form_perm_apply_lt' (xs : list α) (h : nodup xs) (x : α) (n : ℕ) (hn : n + 1 < xs.length)
  (hx : x = (xs.nth_le n ((nat.lt_succ_self n).trans hn))) :
  (form_perm xs) x = xs.nth_le (n + 1) hn :=
by { rw hx, exact form_perm_apply_lt _ h _ _ }

lemma form_perm_apply_nth_le (xs : list α) (h : nodup xs) (n : ℕ) (hn : n < xs.length) :
  form_perm xs (xs.nth_le n hn) = xs.nth_le ((n + 1) % xs.length)
    (by { cases xs, { simpa using hn }, { refine nat.mod_lt _ _, simp }}) :=
begin
  cases xs with x xs,
  { simp },
  { have : n ≤ xs.length,
      { refine nat.le_of_lt_succ _,
        simpa using hn },
    rcases this.eq_or_lt with rfl|hn',
    { simp [form_perm_apply_nth_le_length _ _ h] },
    { simp [form_perm_apply_lt, h, nat.mod_eq_of_lt, nat.succ_lt_succ hn'] } }
end

-- useful for rewrites
lemma form_perm_apply_nth_le' (xs : list α) (h : nodup xs) (x : α) (n : ℕ) (hn : n < xs.length)
  (hx : x = xs.nth_le n hn) :
  form_perm xs x = xs.nth_le ((n + 1) % xs.length)
    (by { cases xs, { simpa using hn }, { refine nat.mod_lt _ _, simp }}) :=
by { simp_rw hx, exact form_perm_apply_nth_le _ h _ _ }

lemma support_form_perm_of_nodup (l : list α) (h : nodup l) (h' : ∀ (x : α), l ≠ [x]) :
  support (form_perm l) = l.to_finset :=
begin
  apply le_antisymm,
  { exact support_form_perm_le l },
  { intros x hx,
    simp only [finset.mem_coe, mem_to_finset] at hx,
    obtain ⟨n, hn, rfl⟩ := nth_le_of_mem hx,
    cases l with x xs,
    { simpa using hn },
    cases xs with y xs,
    { simpa using h' x },
    { have nle : n ≤ (y :: xs).length,
        { refine nat.le_of_lt_succ _,
          simpa using hn },
      simp only [mem_support],
      rcases nle.eq_or_lt with rfl|hn',
      { rw form_perm_apply_nth_le_length _ _ h,
        simp only [mem_cons_iff, cons_append, nodup_nil, and_true, not_mem_nil, singleton_append,
                   nodup_cons, not_false_iff, and_self, mem_singleton] at h,
        push_neg at h,
        have : x ∉ (y :: xs) := by simp [h],
        simp only [length, ne.def, nth_le],
        intro hx,
        rw [hx] at this,
        exact this (nth_le_mem _ _ _) },
      { have nsle : n + 1 < (x :: y :: xs).length,
          { simpa using hn' },
        rw [form_perm_apply_lt _ h n nsle],
        intro H,
        exact nth_le_eq_of_ne_imp_not_nodup _ _ _ _ _ H (nat.lt_succ_self n).ne' h } } }
end

lemma form_perm_rotate_one (l : list α) (h : nodup l) :
  form_perm (l.rotate 1) = form_perm l :=
begin
  have h' : nodup (l.rotate 1),
    { simpa using h },
  by_cases hl : ∀ (x : α), l ≠ [x],
  { have hl' : ∀ (x : α), l.rotate 1 ≠ [x],
      { intro,
        rw [ne.def, rotate_eq_iff],
        simpa using hl _ },
    apply support_congr,
    { rw [support_form_perm_of_nodup _ h hl, support_form_perm_of_nodup _ h' hl',
          finset.coe_inj],
      exact to_finset_eq_of_perm _ _ (rotate_perm _ _) },
    { intros x hx,
      simp only [support_form_perm_of_nodup _ h' hl', finset.mem_coe, mem_to_finset] at hx,
      obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx,
      rw form_perm_apply_nth_le' _ h' _ k hk rfl,
      simp_rw nth_le_rotate l,
      rw form_perm_apply_nth_le' _ h,
      { simp },
      { cases l,
        { simpa using hk },
        { simpa using nat.mod_lt _ nat.succ_pos' } } } },
  { push_neg at hl,
    obtain ⟨x, rfl⟩ := hl,
    simp }
end

lemma form_perm_rotate (l : list α) (h : nodup l) (n : ℕ) :
  form_perm (l.rotate n) = form_perm l :=
begin
  induction n with n hn,
  { simp },
  { rw [nat.succ_eq_add_one, ←rotate_rotate, form_perm_rotate_one, hn],
    refine h.is_rotated _,
    exact (is_rotated.forall l n).symm }
end

lemma form_perm_eq_of_is_rotated {l l' : list α} (hd : nodup l) (h : l ~r l') :
  form_perm l = form_perm l' :=
begin
  obtain ⟨n, rfl⟩ := h,
  exact (form_perm_rotate l hd n).symm
end

lemma form_perm_reverse (l : list α) (h : nodup l) :
  form_perm l.reverse = (form_perm l)⁻¹ :=
begin
  ext x,
  by_cases hx : x ∈ l,
  { obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx,
    cases l with x xs,
    { simp },
    cases xs with y xs,
    { simp },
    rw [form_perm_apply_nth_le' _ _ _ ((x :: y :: xs).length - 1 - k), nth_le_reverse', inv_def,
          eq_symm_apply, form_perm_apply_nth_le _ h],
    { congr,
      rcases k with _|_|k,
      { simp },
      { simp [nat.mod_eq_of_lt] },
      { have hk' : k < xs.length,
          { simpa [nat.succ_lt_succ_iff] using hk },
        suffices : xs.length.succ + 1 - (xs.length - k) = k.succ.succ,
          { simpa [←nat.sub_add_comm (nat.succ_le_of_lt hk'), nat.mod_eq_of_lt,
                   ←nat.sub_add_comm ((nat.sub_le_self _ _).trans (nat.lt_succ_self _).le),
                   nat.sub_lt_self nat.succ_pos' (nat.sub_pos_of_lt hk'),
                   (nat.sub_lt_succ xs.length k).trans (nat.lt_succ_self _), ←add_assoc] },
        rw nat.sub_sub_assoc ((nat.lt_succ_self xs.length).trans_le (nat.le_add_right _ _)).le
          hk'.le,
        simp [add_comm, nat.succ_sub] } },
    { simpa using nat.sub_lt_succ _ _ },
    { rw nth_le_reverse',
      { congr,
        rcases k with _|_|k,
        { simp },
        { simp },
        { simp only [nat.succ_sub_succ_eq_sub, length, nat.succ_add_sub_one],
          rw nat.sub_sub_assoc (nat.le_add_right _ _),
          { simp [add_comm] },
          { refine nat.succ_le_of_lt _,
            simpa [nat.succ_lt_succ_iff] using hk } } },
      { simpa using nat.sub_lt_succ _ _ } },
    { simpa [←add_assoc] using nat.sub_lt_succ _ _ },
    { exact (reverse_perm _).nodup_iff.mpr h } },
  { have hxs : x ∉ support (form_perm l)⁻¹,
      { intro H,
        rw support_inv at H,
        simpa using support_form_perm_le l H },
    have hxs' : x ∉ support (form_perm l.reverse),
      { intro H ,
        simpa using support_form_perm_le l.reverse H },
    rw not_mem_support at hxs hxs',
    simp [hxs, hxs'] }
end

lemma form_perm_pow_apply_nth_le (l : list α) (h : nodup l) (n k : ℕ) (hk : k < l.length) :
  (form_perm l ^ n) (l.nth_le k hk) = l.nth_le ((k + n) % l.length)
    (by { cases l, { simpa using hk }, { refine nat.mod_lt _ _, simp }}) :=
begin
  induction n with n hn,
  { simp [nat.mod_eq_of_lt hk] },
  { simp [pow_succ, mul_apply, hn, form_perm_apply_nth_le _ h, nat.succ_eq_add_one,
          ←nat.add_assoc] }
end

lemma form_perm_ext_iff {x y x' y' : α} {l l' : list α}
  (hd : nodup (x :: y :: l)) (hd' : nodup (x' :: y' :: l')) :
  form_perm (x :: y :: l) = form_perm (x' :: y' :: l') ↔ (x :: y :: l) ~r (x' :: y' :: l') :=
begin
  refine ⟨λ h, _, λ hr, form_perm_eq_of_is_rotated hd hr⟩,
  rw equiv.perm.ext_iff at h,
  have hs : support (form_perm (x :: y :: l)) = support (form_perm (x' :: y' :: l')),
    { ext z,
      rw [mem_support, mem_support, h] },
  have hx : x' ∈ (x :: y :: l),
    { have : x' ∈ support (form_perm (x :: y :: l)),
        { rw [mem_support, h x', form_perm_apply_head],
          simp only [mem_cons_iff, nodup_cons] at hd',
          push_neg at hd',
          exact hd'.left.left.symm },
      simpa using support_form_perm_le _ this },
  obtain ⟨n, hn, hx'⟩ := nth_le_of_mem hx,
  have hl : (x :: y :: l).length = (x' :: y' :: l').length,
    { rw [support_form_perm_of_nodup _ hd (by simp),
          support_form_perm_of_nodup _ hd' (by simp), finset.coe_inj] at hs,
      have := congr_arg finset.card hs,
      rwa [card_to_finset, card_to_finset, erase_dup_eq_self.mpr hd, erase_dup_eq_self.mpr hd'] at
        this },
  use n,
  apply list.ext_le,
  { rw [length_rotate, hl] },
  { intros k hk hk',
    rw nth_le_rotate,
    induction k with k IH,
    { simp_rw [nat.zero_add, nat.mod_eq_of_lt hn],
      simpa },
    { have : k.succ = (k + 1) % (x' :: y' :: l').length,
        { rw [←nat.succ_eq_add_one, nat.mod_eq_of_lt hk'] },
      simp_rw this,
      rw [←form_perm_apply_nth_le _ hd' k (k.lt_succ_self.trans hk'),
          ←IH (k.lt_succ_self.trans hk), ←h, form_perm_apply_nth_le _ hd],
      congr' 1,
      have h1 : 1 = 1 % (x' :: y' :: l').length := by simp,
      rw [hl, nat.mod_eq_of_lt hk', h1, ←nat.add_mod, nat.succ_add] } }
end

end form_perm

end list

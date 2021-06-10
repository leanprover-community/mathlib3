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

/--
A list `l : list α` can be interpreted as a `equiv.perm α` where each element in the list
is permuted to the next one, defined as `form_perm`. When we have that `nodup l`,
we prove that `equiv.perm.support (form_perm l) = l.to_finset`, and that
`form_perm l` is rotationally invariant, in `form_perm_rotate`.
-/
def form_perm : equiv.perm α :=
(zip_with equiv.swap l l.tail).prod

@[simp] lemma form_perm_nil : form_perm ([] : list α) = 1 := rfl
@[simp] lemma form_perm_singleton (x : α) : form_perm [x] = 1 := rfl
@[simp] lemma form_perm_pair (x y : α) : form_perm [x, y] = swap x y := rfl
@[simp] lemma form_perm_cons_cons (x y : α) :
  form_perm (x :: y :: l) = swap x y * form_perm (y :: l) :=
prod_cons

lemma form_perm_apply_of_not_mem {xs : list α} {x : α} (h : x ∉ xs) :
  form_perm xs x = x :=
begin
  induction xs with y ys ih,
  { simp },
  cases ys with z zs,
  { simp },
  { have h' : x ∉ z :: zs := mt (mem_cons_of_mem y) h,
    rw [form_perm_cons_cons, mul_apply, ih h', swap_apply_of_ne_of_ne],
    { exact ne_of_not_mem_cons h },
    { exact ne_of_not_mem_cons h' } }
end

lemma form_perm_apply_mem_of_mem {xs : list α} {x : α} (h : x ∈ xs) :
  form_perm xs x ∈ xs :=
begin
  induction xs with y ys ih generalizing x, { simpa },
  cases ys with z zs, { simpa using h },
  rw [form_perm_cons_cons, mul_apply],
  by_cases hz : x ∈ z :: zs,
  { rw swap_apply_def, split_ifs; simp [*] },
  { have : x = y := ((mem_cons_iff _ _ _).mp h).resolve_right hz,
    rw [form_perm_apply_of_not_mem hz, this, swap_apply_left],
    exact mem_cons_of_mem _ (mem_cons_self _ _) }
end

@[simp] lemma form_perm_apply_last_append (x y : α) (xs : list α) :
  form_perm (x :: (xs ++ [y])) y = x :=
begin
  induction xs with z xs IH generalizing x y,
  { simp },
  { simp [IH] }
end

@[simp] lemma form_perm_apply_last (x : α) (xs : list α) :
  form_perm (x :: xs) ((x :: xs).last (cons_ne_nil x xs)) = x :=
begin
  induction xs using list.reverse_rec_on with xs y IH generalizing x,
  { simp },
  { simp [form_perm_apply_last_append x y xs] }
end

@[simp] lemma form_perm_apply_nth_le_length (x : α) (xs : list α) :
  form_perm (x :: xs) ((x :: xs).nth_le xs.length (by simp)) = x :=
by rw [nth_le_cons_length, form_perm_apply_last]

@[simp] lemma form_perm_apply_head (x y : α) (xs : list α) (h : nodup (x :: y :: xs)) :
  form_perm (x :: y :: xs) x = y :=
by simp [form_perm_apply_of_not_mem (not_mem_of_nodup_cons h)]

@[simp] lemma form_perm_apply_nth_le_zero (h : nodup l) (lt : 1 < l.length) :
  form_perm l (l.nth_le 0 (lt_trans zero_lt_one lt)) = l.nth_le 1 lt :=
begin
  cases l with x xs, { simp },
  cases xs with y ys, { simp },
  exact form_perm_apply_head x y ys h
end

lemma form_perm_eq_head_iff_eq_last (x y : α) (h : nodup (y :: l)) :
  form_perm (y :: l) x = y ↔ x = last (y :: l) (cons_ne_nil _ _) :=
iff.trans (by rw form_perm_apply_last) (form_perm (y :: l)).injective.eq_iff

lemma zip_with_swap_prod_support' (l l' : list α) :
  {x | (zip_with swap l l').prod x ≠ x} ≤ l.to_finset ⊔ l'.to_finset :=
begin
  simp only [set.sup_eq_union, set.le_eq_subset],
  induction l with y l hl generalizing l',
  { simp },
  { cases l' with z l',
    { simp },
    { intro x,
      simp only [set.union_subset_iff, mem_cons_iff, zip_with_cons_cons, foldr, prod_cons,
                 mul_apply],
      intro hx,
      by_cases h : x ∈ {x | (zip_with swap l l').prod x ≠ x},
      { specialize hl l' h,
        refine set.mem_union.elim hl (λ hm, _) (λ hm, _);
        { simp only [finset.coe_insert, set.mem_insert_iff, finset.mem_coe, to_finset_cons,
                     mem_to_finset] at hm ⊢,
          simp [hm] } },
      { simp only [not_not, set.mem_set_of_eq] at h,
        simp only [h, set.mem_set_of_eq] at hx,
        rw swap_apply_ne_self_iff at hx,
        rcases hx with ⟨hyz, rfl|rfl⟩;
        simp } } }
end

lemma zip_with_swap_prod_support [fintype α] (l l' : list α) :
  (zip_with swap l l').prod.support ≤ l.to_finset ⊔ l'.to_finset :=
begin
  intros x hx,
  have hx' : x ∈ {x | (zip_with swap l l').prod x ≠ x} := by simpa using hx,
  simpa using zip_with_swap_prod_support' _ _ hx'
end

lemma support_form_perm_le' : {x | form_perm l x ≠ x} ≤ l.to_finset :=
begin
  refine (zip_with_swap_prod_support' l l.tail).trans _,
  rintro x (hx | hx); simp only [finset.mem_coe, mem_to_finset] at hx ⊢,
  { assumption },
  { exact l.tail_subset hx }
end

lemma support_form_perm_le [fintype α] : support (form_perm l) ≤ l.to_finset :=
begin
  intros x hx,
  have hx' : x ∈ {x | form_perm l x ≠ x} := by simpa using hx,
  simpa using support_form_perm_le' _ hx'
end

lemma form_perm_apply_lt (xs : list α) (h : nodup xs) (n : ℕ) (hn : n + 1 < xs.length) :
  form_perm xs (xs.nth_le n ((nat.lt_succ_self n).trans hn)) = xs.nth_le (n + 1) hn :=
begin
  induction n with n ih generalizing xs,
  { apply form_perm_apply_nth_le_zero _ h },
  cases xs with x xs, { simp },
  cases xs with y xs, { simp },
  have h' : nodup (y :: xs) := pairwise_of_pairwise_cons h,
  rw [form_perm_cons_cons, mul_apply, swap_apply_of_ne_of_ne],
  exact ih (y :: xs) h' _,
  { exact mt (λ h, (h ▸ form_perm_apply_mem_of_mem (nth_le_mem _ n _) : x ∈ y :: xs))
             (not_mem_of_nodup_cons h) },
  { simp only [nth_le, ne.def, form_perm_eq_head_iff_eq_last _ _ _ h', last_eq_nth_le],
    rw nodup_iff_nth_le_inj at h',
    exact mt (h' _ _ _ _) (nat.succ_lt_succ_iff.mp (nat.succ_lt_succ_iff.mp hn)).ne }
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
    { simp },
    { simp [form_perm_apply_lt, h, nat.mod_eq_of_lt, nat.succ_lt_succ hn'] } }
end

-- useful for rewrites
lemma form_perm_apply_nth_le' (xs : list α) (h : nodup xs) (x : α) (n : ℕ) (hn : n < xs.length)
  (hx : x = xs.nth_le n hn) :
  form_perm xs x = xs.nth_le ((n + 1) % xs.length)
    (by { cases xs, { simpa using hn }, { refine nat.mod_lt _ _, simp }}) :=
by { simp_rw hx, exact form_perm_apply_nth_le _ h _ _ }

lemma support_form_perm_of_nodup' (l : list α) (h : nodup l) (h' : ∀ (x : α), l ≠ [x]) :
  {x | form_perm l x ≠ x} = l.to_finset :=
begin
  apply le_antisymm,
  { exact support_form_perm_le' l },
  intros x hx,
  simp only [finset.mem_coe, mem_to_finset] at hx,
  obtain ⟨n, hn, rfl⟩ := nth_le_of_mem hx,
  show form_perm l (l.nth_le n hn) ≠ l.nth_le n hn,
  rw [form_perm_apply_nth_le _ h],
  refine mt (nodup_iff_nth_le_inj.mp h _ _ _ _) (λ eq_n, _),
  by_cases hsucc : n + 1 = l.length,
  { rw [hsucc, nat.mod_self] at eq_n,
    rw [← eq_n, zero_add] at hsucc,
    obtain ⟨x, hx⟩ := length_eq_one.mp hsucc.symm,
    exact h' x hx },
  { rw nat.mod_eq_of_lt (lt_of_le_of_ne hn hsucc) at eq_n,
    exact nat.succ_ne_self n eq_n },
end

lemma support_form_perm_of_nodup [fintype α] (l : list α) (h : nodup l) (h' : ∀ (x : α), l ≠ [x]) :
  support (form_perm l) = l.to_finset :=
begin
  rw ←finset.coe_inj,
  convert support_form_perm_of_nodup' _ h h',
  simp [set.ext_iff]
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
    ext x,
    by_cases hx : x ∈ l.rotate 1,
    { obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx,
      rw form_perm_apply_nth_le' _ h' _ k hk rfl,
      simp_rw nth_le_rotate l,
      rw form_perm_apply_nth_le' _ h,
      { simp },
      { cases l,
        { simpa using hk },
        { simpa using nat.mod_lt _ nat.succ_pos' } } },
    { rw [form_perm_apply_of_not_mem hx, form_perm_apply_of_not_mem],
      simpa using hx } },
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
    rwa is_rotated.nodup_iff,
    exact is_rotated.forall l n }
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
  -- Let's show `form_perm l` is an inverse to `form_perm l.reverse`.
  rw [eq_comm, inv_eq_iff_mul_eq_one],
  ext x,
  rw [mul_apply, one_apply],
  -- We only have to check for `x ∈ l` that `form_perm l (form_perm l.reverse x)`
  by_cases hx : x ∈ l,
  swap, { rw [form_perm_apply_of_not_mem (mt mem_reverse.mp hx), form_perm_apply_of_not_mem hx] },
  have hl : 0 < l.length := length_pos_of_mem hx,
  have hx' : x ∈ l.reverse := mem_reverse.mpr hx,
  obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx',
  have hk' : k < l.length := by rwa length_reverse at hk,
  -- We check this by tracking the index of `x` as it gets mapped.
  rw [form_perm_apply_nth_le _ (nodup_reverse.mpr h), nth_le_reverse',
      form_perm_apply_nth_le _ h, nth_le_reverse'],
  -- Now it's just a case of manipulating `nat`s.
  congr,
  { rw [length_reverse, nat.sub_sub, nat.sub_sub, add_comm 1 k, add_comm 1, ← nat.sub_sub],
    by_cases hk : k + 1 = l.length,
    { rw [hk, nat.mod_self, nat.sub_zero, nat.sub_add_cancel hl, nat.mod_self, nat.sub_self] },
    { rw [nat.mod_eq_of_lt (lt_of_le_of_ne hk' hk), nat.sub_add_cancel, nat.mod_eq_of_lt],
      { exact nat.sub_lt (lt_of_lt_of_le zero_lt_one hl) (nat.succ_pos k) },
      { exact nat.lt_sub_left_of_add_lt (lt_of_le_of_ne hk' hk) } } },
  { rw [nat.sub_sub, add_comm], exact nat.sub_lt (lt_of_lt_of_le zero_lt_one hl) (nat.succ_pos _) },
  { rw [nat.sub_sub, add_comm], exact nat.sub_lt (lt_of_lt_of_le zero_lt_one hl) (nat.succ_pos _) },
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
  have hx : x' ∈ (x :: y :: l),
  { have : x' ∈ {z | form_perm (x :: y :: l) z ≠ z},
    { rw [set.mem_set_of_eq, h x', form_perm_apply_head _ _ _ hd'],
      simp only [mem_cons_iff, nodup_cons] at hd',
      push_neg at hd',
      exact hd'.left.left.symm },
    simpa using support_form_perm_le' _ this },
  obtain ⟨n, hn, hx'⟩ := nth_le_of_mem hx,
  have hl : (x :: y :: l).length = (x' :: y' :: l').length,
  { rw [←erase_dup_eq_self.mpr hd, ←erase_dup_eq_self.mpr hd',
        ←card_to_finset, ←card_to_finset],
    refine congr_arg finset.card _,
    rw [←finset.coe_inj, ←support_form_perm_of_nodup' _ hd (by simp),
        ←support_form_perm_of_nodup' _ hd' (by simp)],
    simp only [h] },
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

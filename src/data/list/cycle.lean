/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import data.list.rotate
import data.list.erase_dup
import group_theory.perm.sign
import group_theory.perm.cycles
import dynamics.fixed_points.basic

/-!
# Cycles of a list

Lists have an equivalence relation of whether they are rotational permutations of one another.
This relation is defined as `is_rotated`.

A list `l : list α` can be interpreted as a `equiv.perm α` where each element in the list
is permuted to the next one, defined as `form_perm`. When we have that `nodup l`,
we prove that `equiv.perm.support (form_perm l) = l.to_finset`, and that
`form_perm l` is rotationally invariant, in `form_perm_rotate`.

Based on this, we define the quotient of lists by the rotation relation, called `cycle`.
We define a permutation from a `s : cycle α` by lifting `form_perm` into the quotient.

-/

namespace list

variables {α β : Type*}

lemma exists_mem_of_ne_nil (l : list α) (h : l ≠ []) : ∃ x, x ∈ l :=
exists_mem_of_length_pos (length_pos_of_ne_nil h)

lemma ne_singleton_iff_of_nodup {l : list α} (h : nodup l) (x : α) :
  l ≠ [x] ↔ l = [] ∨ ∃ y ∈ l, y ≠ x :=
begin
  induction l with hd tl hl,
  { simp },
  { specialize hl (nodup_of_nodup_cons h),
    by_cases hx : tl = [x],
    { simpa [hx, and.comm, and_or_distrib_left] using h },
    { rw [←ne.def, hl] at hx,
      rcases hx with rfl | ⟨y, hy, hx⟩,
      { simp },
      { have : tl ≠ [] := ne_nil_of_mem hy,
        suffices : ∃ (y : α) (H : y ∈ hd :: tl), y ≠ x,
          { simpa [ne_nil_of_mem hy] },
        exact ⟨y, mem_cons_of_mem _ hy, hx⟩ } } }
end

lemma tail_append_of_ne_nil (l l' : list α) (h : l ≠ []) :
  (l ++ l').tail = l.tail ++ l' :=
begin
  cases l,
  { simpa using h },
  { simp }
end

lemma nth_le_cons_length (x : α) (xs : list α) (n : ℕ) (h : n = xs.length) :
  (x :: xs).nth_le n (by simp [h]) = (x :: xs).last (cons_ne_nil x xs) :=
begin
  induction xs with y xs IH generalizing x n,
  { simp },
  { cases n,
    { simpa using h },
    { simp [nat.succ_inj'] at h,
      simpa using IH y n h } }
end

lemma nth_le_eq_of_ne_imp_not_nodup (xs : list α) (n m : ℕ) (hn : n < xs.length)
  (hm : m < xs.length) (h : xs.nth_le n hn = xs.nth_le m hm) (hne : n ≠ m) :
  ¬ nodup xs :=
begin
  induction xs with hd tl hl generalizing n m,
  { simpa using hm },
  { cases n;
    cases m,
    { simpa using hne },
    { have : hd ∈ tl,
        { convert nth_le_mem tl _ _ },
      simpa },
    { have : hd ∈ tl,
        { convert nth_le_mem tl _ _,
          simpa using h.symm },
      simpa },
    { rw [nth_le, nth_le] at h,
      simp only [ne.def] at hne,
      rw [nodup_cons, not_and],
      exact λ _, hl _ _ _ _ h hne } }
end

lemma reverse_eq_iff {l l' : list α} :
  l.reverse = l' ↔ l = l'.reverse :=
by rw [←reverse_reverse l', reverse_inj, reverse_reverse]

lemma nth_le_reverse' (l : list α) (n : ℕ) (hn : n < l.reverse.length) (hn') :
  l.reverse.nth_le n hn = l.nth_le (l.length - 1 - n) hn' :=
begin
  rw eq_comm,
  convert nth_le_reverse l.reverse _ _ _ using 1,
  { simp },
  { simpa }
end

@[elab_as_eliminator]
def reverse_induction
  {C : list α → Sort*}
  (hn : C [])
  (ha : ∀ (xs : list α) (x : α), C xs → C (xs ++ [x])) :
  Π (l : list α), C l :=
begin
  intro l,
  induction h : l.reverse with hd tl hl generalizing l,
  { simp only [reverse_eq_nil] at h,
    rwa h },
  { have : l = tl.reverse ++ [hd] := by simpa using congr_arg list.reverse h,
    rw this,
    apply ha,
    apply hl,
    simp }
end

@[elab_as_eliminator]
def reverse_induction_on (l : list α) {C : list α → Sort*}
  (hn : C [])
  (ha : ∀ (xs : list α) (x : α), C xs → C (xs ++ [x])) :
  C l :=
reverse_induction hn ha l

local attribute [simp] rotate_cons_succ

lemma nth_le_rotate_one (l : list α) (k : ℕ) (hk : k < (l.rotate 1).length) :
  (l.rotate 1).nth_le k hk = l.nth_le ((k + 1) % l.length)
    (by { cases l, { simpa using hk }, { refine nat.mod_lt _ _, simp }}) :=
begin
  cases l with hd tl,
  { simp },
  { have : k ≤ tl.length,
      { refine nat.le_of_lt_succ _,
        simpa using hk },
    rcases this.eq_or_lt with rfl|hk',
    { simp [nth_le_append_right (le_refl _)] },
    { simpa [nth_le_append _ hk', length_cons, nat.mod_eq_of_lt (nat.succ_lt_succ hk')] } }
end

lemma nth_le_rotate (l : list α) (n k : ℕ) (hk : k < (l.rotate n).length) :
  (l.rotate n).nth_le k hk = l.nth_le ((k + n) % l.length)
    (by { cases l, { simpa using hk }, { refine nat.mod_lt _ _, simp }}) :=
begin
  induction n with n hn generalizing l k,
  { have hk' : k < l.length := by simpa using hk,
    simp [nat.mod_eq_of_lt hk'] },
  { simp [nat.succ_eq_add_one, ←rotate_rotate, nth_le_rotate_one, hn l, add_comm, add_left_comm] }
end

lemma rotate_eq_iff {l l' : list α} {n : ℕ} :
  l.rotate n = l' ↔ l = l'.rotate (l'.length - n % l.length) :=
begin
  cases l' with x xs,
  { simp },
  split,
  { intro hl,
    have h : 0 < l.length,
      { simp [←length_rotate l n, hl] },
    rw [←hl, rotate_rotate, ←rotate_mod, nat.add_mod],
    rcases (nat.zero_le (n % l.length)).eq_or_lt with hn|hn,
    { simp [←hn] },
    { have : l.length - n % l.length < l.length := nat.sub_lt h hn,
      simp [nat.mod_eq_of_lt this, nat.add_sub_cancel' (nat.mod_lt _ h).le] } },
  { intro hl,
    set l' := (x :: xs) with hx,
    have : l.length = (x :: xs).length,
      { rw hl,
        simp },
    rw [hl, this, rotate_rotate, ←rotate_mod, nat.add_mod],
    rcases (nat.zero_le (n % l'.length)).eq_or_lt with hn|hn,
    { rw ←hn,
      simp },
    { have h : 0 < l'.length := by simp,
      have : l'.length - n % l'.length < l'.length := nat.sub_lt h hn,
      rw [nat.mod_eq_of_lt this, nat.sub_add_cancel (nat.mod_lt _ h).le],
      simp } },
end

def is_rotated (l l' : list α) : Prop := ∃ n, l.rotate n = l'

infixr ` ~r `:1000 := is_rotated

lemma is_rotated.def {l l' : list α} (h : l ~r l') : ∃ n, l.rotate n = l' := h

lemma is_rotated_iff {l l' : list α} : l ~r l' ↔ ∃ n, l.rotate n = l' := iff.rfl

@[refl] lemma is_rotated.refl (l : list α) : l ~r l :=
⟨0, by simp⟩

@[symm] lemma is_rotated.symm {l l' : list α} (h : l ~r l') : l' ~r l :=
begin
  obtain ⟨n, rfl⟩ := h,
  cases l with hd tl,
  { simp },
  { use (hd :: tl).length * n - n,
    rw [rotate_rotate, nat.add_sub_cancel', rotate_length_mul],
    exact nat.le_mul_of_pos_left (by simp) }
end

lemma is_rotated.symm_iff {l l' : list α} : l ~r l' ↔ l' ~r l :=
⟨is_rotated.symm, is_rotated.symm⟩

@[simp] protected lemma is_rotated.forall (l : list α) (n : ℕ) : l.rotate n ~r l :=
is_rotated.symm ⟨n, rfl⟩

@[trans] lemma is_rotated.trans {l l' l'' : list α} (h : l ~r l') (h' : l' ~r l'') :
  l ~r l'' :=
begin
  obtain ⟨n, rfl⟩ := h.def,
  obtain ⟨m, rfl⟩ := h'.def,
  rw rotate_rotate,
  use (n + m)
end

lemma is_rotated.eqv : equivalence (@is_rotated α) :=
mk_equivalence _ is_rotated.refl (λ _ _, is_rotated.symm) (λ _ _ _, is_rotated.trans)

def is_rotated.setoid : setoid (list α) :=
{ r := is_rotated, iseqv := is_rotated.eqv }

lemma is_rotated.perm {l l' : list α} (h : l ~r l') : l ~ l' :=
exists.elim h (λ _ hl, hl ▸ (rotate_perm _ _).symm)

lemma is_rotated.nodup_iff {l l' : list α} (h : l ~r l') : nodup l ↔ nodup l' :=
h.perm.nodup_iff

lemma nodup.is_rotated {l l' : list α} (h : nodup l) (h' : l ~r l') : nodup l' :=
h'.nodup_iff.mp h

lemma is_rotated.mem_iff {l l' : list α} (h : l ~r l') {a : α} : a ∈ l ↔ a ∈ l' :=
h.perm.mem_iff

@[simp] lemma is_rotated_nil_iff {l : list α} : l ~r [] ↔ l = [] :=
⟨λ ⟨n, hn⟩, by simpa using hn, λ h, h ▸ by refl⟩

@[simp] lemma is_rotated_nil_iff' {l : list α} : [] ~r l ↔ l = [] :=
by rw [is_rotated.symm_iff, is_rotated_nil_iff]

lemma is_rotated_concat (hd : α) (tl : list α) :
  (tl ++ [hd]) ~r (hd :: tl) :=
is_rotated.symm ⟨1, by simp⟩

section form_perm

@[simp] lemma zip_with_rotate_one (f : α → α → β) (x y : α) (l : list α) :
  zip_with f (x :: y :: l) ((x :: y :: l).rotate 1) =
  f x y :: zip_with f (y :: l) (l ++ [x]) :=
by simp

variables [decidable_eq α] (l : list α)

lemma to_finset_eq_iff_perm_erase_dup {l l' : list α} :
  l.to_finset = l'.to_finset ↔ l.erase_dup ~ l'.erase_dup :=
by simp [finset.ext_iff, perm_ext (nodup_erase_dup _) (nodup_erase_dup _)]

lemma to_finset_eq_of_perm (l l' : list α) (h : l ~ l') :
  l.to_finset = l'.to_finset :=
to_finset_eq_iff_perm_erase_dup.mpr h.erase_dup

@[simp] lemma to_finset_append {l l' : list α} :
  to_finset (l ++ l') = l.to_finset ∪ l'.to_finset :=
begin
  induction l with hd tl hl,
  { simp },
  { simp [hl] }
end

@[simp] lemma to_finset_reverse {l : list α} :
  to_finset l.reverse = l.to_finset :=
to_finset_eq_of_perm _ _ (reverse_perm l)

@[simp] lemma card_to_finset (l : list α) : finset.card l.to_finset = l.erase_dup.length := rfl

open equiv equiv.perm

lemma support_swap_mul_swap {x y z : α} (h : nodup [x, y, z]) :
  support (swap x y * swap y z) = {x, y, z} :=
begin
  simp at h,
  push_neg at h,
  apply le_antisymm,
  { convert support_mul_le _ _,
    rw [support_swap h.left.left, support_swap h.right],
    ext,
    simp [or.comm, or.left_comm] },
  { rintro w (rfl | rfl | rfl | _);
    simp [swap_apply_of_ne_of_ne, h.left.left, h.left.left.symm, h.left.right, h.left.right.symm,
          h.right.symm] }
end

instance {α : Type*} : mul_action (equiv.perm α) α :=
{ smul := λ e x, e x,
  one_smul := λ _, by simp,
  mul_smul := λ _, by simp }

def form_perm : equiv.perm α :=
(zip_with equiv.swap l (l.rotate 1)).tail.prod

@[simp] lemma form_perm_nil : form_perm ([] : list α) = 1 := rfl

@[simp] lemma form_perm_singleton (x : α) : form_perm [x] = 1 := rfl

@[simp] lemma form_perm_pair (x y : α) : form_perm [x, y] = swap y x := rfl

lemma map_zip_with {α β γ δ : Type*} (f : α → β) (g : γ → δ → α) (l : list γ) (l' : list δ) :
  map f (zip_with g l l') = zip_with (λ x y, f (g x y)) l l' :=
begin
  induction l with hd tl hl generalizing l',
  { simp },
  { cases l',
    { simp },
    { simp [hl] } }
end

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
  induction xs using list.reverse_induction with xs y IH generalizing x,
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

def to_set {α : Type*} (l : list α) : set α := {x | x ∈ l}

@[simp] lemma mem_to_set {α : Type*} {x : α} {l : list α} : x ∈ l.to_set ↔ x ∈ l := iff.rfl

@[simp] lemma to_set_nil {α : Type*} : (@nil α).to_set = ∅ := rfl

@[simp] lemma to_set_cons {α : Type*} {x : α} {l : list α} : (x :: l).to_set = {x} ∪ l.to_set := rfl

@[simp] lemma to_set_eq_empty_iff {α : Type*} {l : list α} : l.to_set = ∅ ↔ l = [] :=
by { cases l; simp [set.ext_iff] }

@[simp] lemma to_set_mono {α : Type*} {l l' : list α} : l.to_set ⊆ l'.to_set ↔ l ⊆ l' := iff.rfl

lemma to_set_finite {α : Type*} (l : list α) : l.to_set.finite :=
begin
  classical,
  exact ⟨subtype.fintype l⟩
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
  (form_perm xs) (xs.nth_le n ((nat.lt_succ_self n).trans hn)) = xs.nth_le (n + 1) hn :=
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
  obtain ⟨n, rfl⟩ := h.def,
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
      { intro H ,
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

lemma is_cycle_form_perm (x y : α) (xs : list α) (h : nodup (x :: y :: xs)) :
  is_cycle (form_perm (x :: y :: xs)) :=
begin
  use x,
  split,
  { simp only [mem_cons_iff, nodup_cons] at h,
    push_neg at h,
    simp [h.left.left.symm] },
  { intros z hz,
    rw [←mem_support, support_form_perm_of_nodup _ h, finset.mem_coe, mem_to_finset] at hz,
    { obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hz,
      have : ∀ (f : equiv.perm α), f x = f ((x :: y :: xs).nth_le 0 (by simp)) := by simp,
      use k,
      rw [gpow_coe_nat, this, form_perm_pow_apply_nth_le _ h, nat.zero_add],
      simp_rw nat.mod_eq_of_lt hk },
    { simp } }
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

open list

def cycle (α : Type*) : Type* := quotient (@is_rotated.setoid α)

namespace cycle

variables {α β : Type*}

instance : has_coe (list α) (cycle α) := ⟨quot.mk _⟩

@[simp] theorem coe_eq_coe {l₁ l₂ : list α} : (l₁ : cycle α) = l₂ ↔ (l₁ ~r l₂) :=
@quotient.eq _ (is_rotated.setoid) _ _

def mem (a : α) (s : cycle α) : Prop :=
quot.lift_on s (λ l, a ∈ l) (λ l₁ l₂ (e : l₁ ~r l₂), propext $ e.mem_iff)

instance : has_mem α (cycle α) := ⟨mem⟩

def nodup (s : cycle α) : Prop :=
quot.lift_on s nodup (λ l₁ l₂ (e : l₁ ~r l₂), propext $ e.nodup_iff)

section perm

variable [decidable_eq α]

instance {s : cycle α} : decidable (nodup s) :=
quot.rec_on_subsingleton s (λ (l : list α), list.nodup_decidable l)

def perm_aux : Π (s : cycle α) (h : nodup s), equiv.perm α :=
λ s, quot.hrec_on s (λ l h, form_perm l)
  (λ l₁ l₂ (h : l₁ ~r l₂), by {
    ext,
    { exact is_rotated.nodup_iff h },
    { intros h1 h2 he,
      refine heq_of_eq _,
      rw form_perm_eq_of_is_rotated _ h,
      exact h1 } })

def perm (s : cycle α) (h : nodup s . tactic.exact_dec_trivial) : equiv.perm α :=
s.perm_aux h

end perm

end cycle


variables {α : Type*} [nonempty α]

@[irreducible] noncomputable def arbitrary' (n : name) (α : Type*) [nonempty α] : α :=
classical.arbitrary α

example {x y : α} (hx : x = arbitrary' `x _) (hy : y = arbitrary' `y _) (h : "x" = "y") : x = y :=
by rw [hx, hy, h]

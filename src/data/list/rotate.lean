/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.list.perm
import data.list.range

variables {α : Type*}

open nat

namespace list

lemma rotate_mod (l : list α) (n : ℕ) : l.rotate (n % l.length) = l.rotate n :=
by simp [rotate]

@[simp] lemma rotate_nil (n : ℕ) : ([] : list α).rotate n = [] := by cases n; refl

@[simp] lemma rotate_zero (l : list α) : l.rotate 0 = l := by simp [rotate]

@[simp] lemma rotate'_nil (n : ℕ) : ([] : list α).rotate' n = [] := by cases n; refl

@[simp] lemma rotate'_zero (l : list α) : l.rotate' 0 = l := by cases l; refl

lemma rotate'_cons_succ (l : list α) (a : α) (n : ℕ) :
  (a :: l : list α).rotate' n.succ = (l ++ [a]).rotate' n := by simp [rotate']

@[simp] lemma length_rotate' : ∀ (l : list α) (n : ℕ), (l.rotate' n).length = l.length
| []     n     := rfl
| (a::l) 0     := rfl
| (a::l) (n+1) := by rw [list.rotate', length_rotate' (l ++ [a]) n]; simp

lemma rotate'_eq_take_append_drop : ∀ {l : list α} {n : ℕ}, n ≤ l.length →
  l.rotate' n = l.drop n ++ l.take n
| []     n     h := by simp [drop_append_of_le_length h]
| l      0     h := by simp [take_append_of_le_length h]
| (a::l) (n+1) h :=
have hnl : n ≤ l.length, from le_of_succ_le_succ h,
have hnl' : n ≤ (l ++ [a]).length,
  by rw [length_append, length_cons, list.length, zero_add];
    exact (le_of_succ_le h),
by rw [rotate'_cons_succ, rotate'_eq_take_append_drop hnl', drop, take,
     drop_append_of_le_length hnl, take_append_of_le_length hnl];
   simp

lemma rotate'_rotate' : ∀ (l : list α) (n m : ℕ), (l.rotate' n).rotate' m = l.rotate' (n + m)
| (a::l) 0     m := by simp
| []     n     m := by simp
| (a::l) (n+1) m := by rw [rotate'_cons_succ, rotate'_rotate', add_right_comm, rotate'_cons_succ]

@[simp] lemma rotate'_length (l : list α) : rotate' l l.length = l :=
by rw rotate'_eq_take_append_drop (le_refl _); simp

@[simp] lemma rotate'_length_mul (l : list α) : ∀ n : ℕ, l.rotate' (l.length * n) = l
| 0     := by simp
| (n+1) :=
calc l.rotate' (l.length * (n + 1)) =
  (l.rotate' (l.length * n)).rotate' (l.rotate' (l.length * n)).length :
    by simp [-rotate'_length, nat.mul_succ, rotate'_rotate']
... = l : by rw [rotate'_length, rotate'_length_mul]

lemma rotate'_mod (l : list α) (n : ℕ) : l.rotate' (n % l.length) = l.rotate' n :=
calc l.rotate' (n % l.length) = (l.rotate' (n % l.length)).rotate'
    ((l.rotate' (n % l.length)).length * (n / l.length)) : by rw rotate'_length_mul
... = l.rotate' n : by rw [rotate'_rotate', length_rotate', nat.mod_add_div]

lemma rotate_eq_rotate' (l : list α) (n : ℕ) : l.rotate n = l.rotate' n :=
if h : l.length = 0 then by simp [length_eq_zero, *] at *
else by
  rw [← rotate'_mod, rotate'_eq_take_append_drop (le_of_lt (nat.mod_lt _ (nat.pos_of_ne_zero h)))];
  simp [rotate]

lemma rotate_cons_succ (l : list α) (a : α) (n : ℕ) :
  (a :: l : list α).rotate n.succ = (l ++ [a]).rotate n :=
by rw [rotate_eq_rotate', rotate_eq_rotate', rotate'_cons_succ]

@[simp] lemma mem_rotate : ∀ {l : list α} {a : α} {n : ℕ}, a ∈ l.rotate n ↔ a ∈ l
| []     _ n     := by simp
| (a::l) _ 0     := by simp
| (a::l) _ (n+1) := by simp [rotate_cons_succ, mem_rotate, or.comm]

@[simp] lemma length_rotate (l : list α) (n : ℕ) : (l.rotate n).length = l.length :=
by rw [rotate_eq_rotate', length_rotate']

lemma rotate_eq_take_append_drop {l : list α} {n : ℕ} : n ≤ l.length →
  l.rotate n = l.drop n ++ l.take n :=
by rw rotate_eq_rotate'; exact rotate'_eq_take_append_drop

lemma rotate_rotate (l : list α) (n m : ℕ) : (l.rotate n).rotate m = l.rotate (n + m) :=
by rw [rotate_eq_rotate', rotate_eq_rotate', rotate_eq_rotate', rotate'_rotate']

@[simp] lemma rotate_length (l : list α) : rotate l l.length = l :=
by rw [rotate_eq_rotate', rotate'_length]

@[simp] lemma rotate_length_mul (l : list α) (n : ℕ) : l.rotate (l.length * n) = l :=
by rw [rotate_eq_rotate', rotate'_length_mul]

lemma prod_rotate_eq_one_of_prod_eq_one [group α] : ∀ {l : list α} (hl : l.prod = 1) (n : ℕ),
  (l.rotate n).prod = 1
| []     _  _ := by simp
| (a::l) hl n :=
have n % list.length (a :: l) ≤ list.length (a :: l), from le_of_lt (nat.mod_lt _ dec_trivial),
by rw ← list.take_append_drop (n % list.length (a :: l)) (a :: l) at hl;
  rw [← rotate_mod, rotate_eq_take_append_drop this, list.prod_append, mul_eq_one_iff_inv_eq,
    ← one_mul (list.prod _)⁻¹, ← hl, list.prod_append, mul_assoc, mul_inv_self, mul_one]

lemma rotate_perm (l : list α) (n : ℕ) : l.rotate n ~ l :=
begin
  rw rotate_eq_rotate',
  induction n with n hn generalizing l,
  { simp },
  { cases l with hd tl,
    { simp },
    { rw rotate'_cons_succ,
      exact (hn _).trans (perm_append_singleton _ _) } }
end

@[simp] lemma nodup_rotate {l : list α} {n : ℕ} : nodup (l.rotate n) ↔ nodup l :=
(rotate_perm l n).nodup_iff

@[simp] lemma rotate_eq_nil_iff {l : list α} {n : ℕ} : l.rotate n = [] ↔ l = [] :=
begin
  induction n with n hn generalizing l,
  { simp },
  { cases l with hd tl,
    { simp },
    { simp [rotate_cons_succ, hn] } }
end

@[simp] lemma rotate_singleton (x : α) (n : ℕ) :
  [x].rotate n = [x] :=
begin
  induction n with n hn,
  { simp },
  { rwa [rotate_cons_succ] }
end

lemma zip_with_rotate_distrib {α β γ : Type*} (f : α → β → γ) (l : list α) (l' : list β) (n : ℕ)
  (h : l.length = l'.length) :
  (zip_with f l l').rotate n = zip_with f (l.rotate n) (l'.rotate n) :=
begin
  cases l.length.zero_le.eq_or_lt with hl hl,
  { simp [eq_nil_of_length_eq_zero hl.symm] },
  { have : n = n % l.length + l.length * (n / l.length) := (nat.mod_add_div _ _).symm,
    have hn : n % l.length < l.length := nat.mod_lt _ hl,
    rw [this, ←rotate_rotate, ←rotate_rotate, ←rotate_rotate, rotate_length_mul',
        rotate_length_mul', rotate_length_mul',
        rotate_eq_take_append_drop, rotate_eq_take_append_drop,
        rotate_eq_take_append_drop, zip_with_append, ←zip_with_distrib_drop,
        ←zip_with_distrib_take],
    all_goals { simp [←h, hn.le] } }
end

local attribute [simp] rotate_cons_succ

@[simp] lemma zip_with_rotate_one {β : Type*} (f : α → α → β) (x y : α) (l : list α) :
  zip_with f (x :: y :: l) ((x :: y :: l).rotate 1) =
  f x y :: zip_with f (y :: l) (l ++ [x]) :=
by simp

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
  l.rotate n = l' ↔ l = l'.rotate (l'.length - n % l'.length) :=
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
    have : l'.length = (x :: xs).length := congr_arg length hx,
    rw [hl, this, rotate_rotate, ←rotate_mod, nat.add_mod],
    rcases (nat.zero_le (n % l'.length)).eq_or_lt with hn|hn,
    { rw ←hn,
      simp },
    { have h : 0 < l'.length := by simp,
      have : l'.length - n % l'.length < l'.length := nat.sub_lt h hn,
      rw [nat.mod_eq_of_lt this, nat.sub_add_cancel (nat.mod_lt _ h).le],
      simp } }
end

lemma reverse_rotate (l : list α) (n : ℕ) :
  (l.rotate n).reverse = l.reverse.rotate (l.length - (n % l.length)) :=
begin
  rw [←length_reverse l, ←rotate_eq_iff],
  induction n with n hn generalizing l,
  { simp },
  { cases l with hd tl,
    { simp },
    { rw [rotate_cons_succ, nat.succ_eq_add_one, ←rotate_rotate, hn],
      simp } }
end

section is_rotated

variables (l l' : list α)

def is_rotated : Prop := ∃ n, l.rotate n = l'

infixr ` ~r `:1000 := is_rotated

variables {l l'}

lemma is_rotated.def (h : l ~r l') : ∃ n, l.rotate n = l' := h

lemma is_rotated_iff : l ~r l' ↔ ∃ n, l.rotate n = l' := iff.rfl

@[refl] lemma is_rotated.refl (l : list α) : l ~r l :=
⟨0, by simp⟩

@[symm] lemma is_rotated.symm (h : l ~r l') : l' ~r l :=
begin
  obtain ⟨n, rfl⟩ := h,
  cases l with hd tl,
  { simp },
  { use (hd :: tl).length * n - n,
    rw [rotate_rotate, nat.add_sub_cancel', rotate_length_mul],
    exact nat.le_mul_of_pos_left (by simp) }
end

lemma is_rotated_symm_iff : l ~r l' ↔ l' ~r l :=
⟨is_rotated.symm, is_rotated.symm⟩

@[simp] protected lemma is_rotated.forall (l : list α) (n : ℕ) : l.rotate n ~r l :=
is_rotated.symm ⟨n, rfl⟩

@[trans] lemma is_rotated.trans {l'' : list α} (h : l ~r l') (h' : l' ~r l'') :
  l ~r l'' :=
begin
  obtain ⟨n, rfl⟩ := h.def,
  obtain ⟨m, rfl⟩ := h'.def,
  rw rotate_rotate,
  use (n + m)
end

lemma is_rotated.eqv : equivalence (@is_rotated α) :=
mk_equivalence _ is_rotated.refl (λ _ _, is_rotated.symm) (λ _ _ _, is_rotated.trans)

def is_rotated.setoid (α : Type*) : setoid (list α) :=
{ r := is_rotated, iseqv := is_rotated.eqv }

lemma is_rotated.perm (h : l ~r l') : l ~ l' :=
exists.elim h (λ _ hl, hl ▸ (rotate_perm _ _).symm)

lemma is_rotated.nodup_iff (h : l ~r l') : nodup l ↔ nodup l' :=
h.perm.nodup_iff

lemma nodup.is_rotated (h : nodup l) (h' : l ~r l') : nodup l' :=
h'.nodup_iff.mp h

lemma is_rotated.mem_iff (h : l ~r l') {a : α} : a ∈ l ↔ a ∈ l' :=
h.perm.mem_iff

@[simp] lemma is_rotated_nil_iff : l ~r [] ↔ l = [] :=
⟨λ ⟨n, hn⟩, by simpa using hn, λ h, h ▸ by refl⟩

@[simp] lemma is_rotated_nil_iff' : [] ~r l ↔ l = [] :=
by rw [is_rotated_symm_iff, is_rotated_nil_iff]

lemma is_rotated_concat (hd : α) (tl : list α) :
  (tl ++ [hd]) ~r (hd :: tl) :=
is_rotated.symm ⟨1, by simp⟩

lemma is_rotated.reverse (h : l ~r l') : l.reverse ~r l'.reverse :=
begin
  rw is_rotated_iff at h ⊢,
  obtain ⟨n, rfl⟩ := h,
  exact ⟨_, (reverse_rotate _ _).symm⟩
end

lemma is_rotated_reverse_comm_iff :
  l.reverse ~r l' ↔ l ~r l'.reverse :=
begin
  split;
  { intro h,
    simpa using h.reverse }
end

@[simp] lemma is_rotated_reverse_iff :
  l.reverse ~r l'.reverse ↔ l ~r l' :=
by simp [is_rotated_reverse_comm_iff]

lemma is_rotated_iff_mod : l ~r l' ↔ ∃ n ≤ l.length, l.rotate n = l' :=
begin
  refine ⟨λ h, _, λ ⟨n, _, h⟩, ⟨n, h⟩⟩,
  obtain ⟨n, rfl⟩ := h.def,
  cases l with hd tl,
  { simp },
  { refine ⟨n % (hd :: tl).length, _, rotate_mod _ _⟩,
    refine (nat.mod_lt _ _).le,
    simp }
end

lemma is_rotated_iff_mem_map_range : l ~r l' ↔ l' ∈ (list.range (l.length + 1)).map l.rotate :=
begin
  simp_rw [mem_map, mem_range, is_rotated_iff_mod],
  exact ⟨λ ⟨n, hn, h⟩, ⟨n, nat.lt_succ_of_le hn, h⟩, λ ⟨n, hn, h⟩, ⟨n, nat.le_of_lt_succ hn, h⟩⟩
end

section decidable

variables [decidable_eq α]

instance is_rotated_decidable (l l' : list α) : decidable (l ~r l') :=
decidable_of_iff' _ is_rotated_iff_mem_map_range

instance {l l' : list α} : decidable (@setoid.r _ (is_rotated.setoid α) l l') :=
list.is_rotated_decidable _ _

end decidable

end is_rotated

end list

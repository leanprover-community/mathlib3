/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yakov Pechersky
-/
import data.list.perm
import data.list.range

/-!
# List rotation

This file proves basic results about `list.rotate`, the list rotation.

## Main declarations

* `is_rotated l₁ l₂`: States that `l₁` is a rotated version of `l₂`.
* `cyclic_permutations l`: The list of all cyclic permutants of `l`, up to the length of `l`.

## Tags

rotated, rotation, permutation, cycle
-/

universe u
variables {α : Type u}

open nat

namespace list

lemma rotate_mod (l : list α) (n : ℕ) : l.rotate (n % l.length) = l.rotate n :=
by simp [rotate]

@[simp] lemma rotate_nil (n : ℕ) : ([] : list α).rotate n = [] := by cases n; simp [rotate]

@[simp] lemma rotate_zero (l : list α) : l.rotate 0 = l := by simp [rotate]

@[simp] lemma rotate'_nil (n : ℕ) : ([] : list α).rotate' n = [] := by cases n; refl

@[simp] lemma rotate'_zero (l : list α) : l.rotate' 0 = l := by cases l; refl

lemma rotate'_cons_succ (l : list α) (a : α) (n : ℕ) :
  (a :: l : list α).rotate' n.succ = (l ++ [a]).rotate' n := by simp [rotate']

@[simp] lemma length_rotate' : ∀ (l : list α) (n : ℕ), (l.rotate' n).length = l.length
| []     n     := rfl
| (a::l) 0     := rfl
| (a::l) (n+1) := by rw [list.rotate', length_rotate' (l ++ [a]) n]; simp

lemma rotate'_eq_drop_append_take : ∀ {l : list α} {n : ℕ}, n ≤ l.length →
  l.rotate' n = l.drop n ++ l.take n
| []     n     h := by simp [drop_append_of_le_length h]
| l      0     h := by simp [take_append_of_le_length h]
| (a::l) (n+1) h :=
have hnl : n ≤ l.length, from le_of_succ_le_succ h,
have hnl' : n ≤ (l ++ [a]).length,
  by rw [length_append, length_cons, list.length, zero_add];
    exact (le_of_succ_le h),
by rw [rotate'_cons_succ, rotate'_eq_drop_append_take hnl', drop, take,
     drop_append_of_le_length hnl, take_append_of_le_length hnl];
   simp

lemma rotate'_rotate' : ∀ (l : list α) (n m : ℕ), (l.rotate' n).rotate' m = l.rotate' (n + m)
| (a::l) 0     m := by simp
| []     n     m := by simp
| (a::l) (n+1) m := by rw [rotate'_cons_succ, rotate'_rotate', add_right_comm, rotate'_cons_succ]

@[simp] lemma rotate'_length (l : list α) : rotate' l l.length = l :=
by rw rotate'_eq_drop_append_take (le_refl _); simp

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
  rw [← rotate'_mod, rotate'_eq_drop_append_take (le_of_lt (nat.mod_lt _ (nat.pos_of_ne_zero h)))];
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

lemma rotate_eq_drop_append_take {l : list α} {n : ℕ} : n ≤ l.length →
  l.rotate n = l.drop n ++ l.take n :=
by rw rotate_eq_rotate'; exact rotate'_eq_drop_append_take

lemma rotate_eq_drop_append_take_mod {l : list α} {n : ℕ} :
  l.rotate n = l.drop (n % l.length) ++ l.take (n % l.length) :=
begin
  cases l.length.zero_le.eq_or_lt with hl hl,
  { simp [eq_nil_of_length_eq_zero hl.symm ] },
  rw [←rotate_eq_drop_append_take (n.mod_lt hl).le, rotate_mod]
end

@[simp] lemma rotate_append_length_eq (l l' : list α) : (l ++ l').rotate l.length = l' ++ l :=
begin
  rw rotate_eq_rotate',
  induction l generalizing l',
  { simp, },
  { simp [rotate', l_ih] },
end

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
  rw [← rotate_mod, rotate_eq_drop_append_take this, list.prod_append, mul_eq_one_iff_inv_eq,
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

@[simp] lemma nil_eq_rotate_iff {l : list α} {n : ℕ} : [] = l.rotate n ↔ [] = l :=
by rw [eq_comm, rotate_eq_nil_iff, eq_comm]

@[simp] lemma rotate_singleton (x : α) (n : ℕ) :
  [x].rotate n = [x] :=
begin
  induction n with n hn,
  { simp },
  { rwa [rotate_cons_succ] }
end

@[simp] lemma rotate_eq_singleton_iff {l : list α} {n : ℕ} {x : α} : l.rotate n = [x] ↔ l = [x] :=
begin
  induction n with n hn generalizing l,
  { simp },
  { cases l with hd tl,
    { simp },
    { simp [rotate_cons_succ, hn, append_eq_cons_iff, and_comm] } }
end

@[simp] lemma singleton_eq_rotate_iff {l : list α} {n : ℕ} {x : α} : [x] = l.rotate n ↔ [x] = l :=
by rw [eq_comm, rotate_eq_singleton_iff, eq_comm]

lemma zip_with_rotate_distrib {α β γ : Type*} (f : α → β → γ) (l : list α) (l' : list β) (n : ℕ)
  (h : l.length = l'.length) :
  (zip_with f l l').rotate n = zip_with f (l.rotate n) (l'.rotate n) :=
begin
  rw [rotate_eq_drop_append_take_mod, rotate_eq_drop_append_take_mod,
      rotate_eq_drop_append_take_mod, h, zip_with_append, ←zip_with_distrib_drop,
      ←zip_with_distrib_take, list.length_zip_with, h, min_self],
  rw [length_drop, length_drop, h]
end

local attribute [simp] rotate_cons_succ

@[simp] lemma zip_with_rotate_one {β : Type*} (f : α → α → β) (x y : α) (l : list α) :
  zip_with f (x :: y :: l) ((x :: y :: l).rotate 1) =
  f x y :: zip_with f (y :: l) (l ++ [x]) :=
by simp

lemma nth_le_rotate_one (l : list α) (k : ℕ) (hk : k < (l.rotate 1).length) :
  (l.rotate 1).nth_le k hk = l.nth_le ((k + 1) % l.length)
    (mod_lt _ (length_rotate l 1 ▸ k.zero_le.trans_lt hk)) :=
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
    (mod_lt _ (length_rotate l n ▸ k.zero_le.trans_lt hk)) :=
begin
  induction n with n hn generalizing l k,
  { have hk' : k < l.length := by simpa using hk,
    simp [nat.mod_eq_of_lt hk'] },
  { simp [nat.succ_eq_add_one, ←rotate_rotate, nth_le_rotate_one, hn l, add_comm, add_left_comm] }
end

/-- A variant of `nth_le_rotate` useful for rewrites. -/
lemma nth_le_rotate' (l : list α) (n k : ℕ) (hk : k < l.length) :
  (l.rotate n).nth_le ((l.length - n % l.length + k) % l.length)
      ((nat.mod_lt _ (k.zero_le.trans_lt hk)).trans_le (length_rotate _ _).ge) = l.nth_le k hk :=
begin
  rw nth_le_rotate,
  congr,
  set m := l.length,
  rw [mod_add_mod, add_assoc, add_left_comm, add_comm, add_mod, add_mod _ n],
  cases (n % m).zero_le.eq_or_lt with hn hn,
  { simpa [←hn] using nat.mod_eq_of_lt hk },
  { have mpos : 0 < m := k.zero_le.trans_lt hk,
    have hm : m - n % m < m := nat.sub_lt_self mpos hn,
    have hn' : n % m < m := nat.mod_lt _ mpos,
    simpa [mod_eq_of_lt hm, nat.sub_add_cancel hn'.le] using nat.mod_eq_of_lt hk }
end

lemma rotate_injective (n : ℕ) : function.injective (λ l : list α, l.rotate n) :=
begin
  rintros l l' (h : l.rotate n = l'.rotate n),
  have hle : l.length = l'.length := (l.length_rotate n).symm.trans (h.symm ▸ l'.length_rotate n),
  rw [rotate_eq_drop_append_take_mod, rotate_eq_drop_append_take_mod] at h,
  obtain ⟨hd, ht⟩ := append_inj h _,
  { rw [←take_append_drop _ l, ht, hd, take_append_drop] },
  { rw [length_drop, length_drop, hle] }
end

-- possibly easier to find in doc-gen, otherwise not that useful.
lemma rotate_eq_rotate {l l' : list α} {n : ℕ} :
  l.rotate n = l'.rotate n ↔ l = l' :=
(rotate_injective n).eq_iff

lemma rotate_eq_iff {l l' : list α} {n : ℕ} :
  l.rotate n = l' ↔ l = l'.rotate (l'.length - n % l'.length) :=
begin
  rw [←@rotate_eq_rotate _ l _ n, rotate_rotate, ←rotate_mod l', add_mod],
  cases l'.length.zero_le.eq_or_lt with hl hl,
  { rw [eq_nil_of_length_eq_zero hl.symm, rotate_nil, rotate_eq_nil_iff] },
  { cases (nat.zero_le (n % l'.length)).eq_or_lt with hn hn,
    { simp [←hn] },
    { rw [mod_eq_of_lt (nat.sub_lt_self hl hn), nat.sub_add_cancel, mod_self, rotate_zero],
      exact (nat.mod_lt _ hl).le } }
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

lemma rotate_reverse (l : list α) (n : ℕ) :
  l.reverse.rotate n = (l.rotate (l.length - (n % l.length))).reverse :=
begin
  rw [←reverse_reverse l],
  simp_rw [reverse_rotate, reverse_reverse, rotate_eq_iff, rotate_rotate, length_rotate,
           length_reverse],
  rw [←length_reverse l],
  set k := n % l.reverse.length with hk,
  cases hk' : k with k',
  { simp [-length_reverse, ←rotate_rotate] },
  { cases l with x l,
    { simp },
    { have : k'.succ < (x :: l).length,
      { simp [←hk', hk, nat.mod_lt] },
      rw [nat.mod_eq_of_lt, nat.sub_add_cancel, rotate_length],
      { exact nat.sub_le_self _ _ },
      { exact nat.sub_lt_self (by simp) nat.succ_pos' } } }
end

lemma map_rotate {β : Type*} (f : α → β) (l : list α) (n : ℕ) :
  map f (l.rotate n) = (map f l).rotate n :=
begin
  induction n with n hn IH generalizing l,
  { simp },
  { cases l with hd tl,
    { simp },
    { simp [hn] } }
end

theorem nodup.rotate_eq_self_iff {l : list α} (hl : l.nodup) {n : ℕ} :
  l.rotate n = l ↔ n % l.length = 0 ∨ l = [] :=
begin
  split,
  { intro h,
    cases l.length.zero_le.eq_or_lt with hl' hl',
    { simp [←length_eq_zero, ←hl'] },
    left,
    rw nodup_iff_nth_le_inj at hl,
    refine hl _ _ (mod_lt _ hl') hl' _,
    rw ←nth_le_rotate' _ n,
    simp_rw [h, nat.sub_add_cancel (mod_lt _ hl').le, mod_self] },
  { rintro (h|h),
    { rw [←rotate_mod, h],
      exact rotate_zero l },
    { simp [h] } }
end

lemma nodup.rotate_congr {l : list α} (hl : l.nodup) (hn : l ≠ []) (i j : ℕ)
  (h : l.rotate i = l.rotate j) : i % l.length = j % l.length :=
begin
  have hi : i % l.length < l.length := mod_lt _ (length_pos_of_ne_nil hn),
  have hj : j % l.length < l.length := mod_lt _ (length_pos_of_ne_nil hn),
  refine (nodup_iff_nth_le_inj.mp hl) _ _ hi hj _,
  rw [←nth_le_rotate' l i, ←nth_le_rotate' l j],
  simp [nat.sub_add_cancel, hi.le, hj.le, h]
end

section is_rotated

variables (l l' : list α)

/-- `is_rotated l₁ l₂` or `l₁ ~r l₂` asserts that `l₁` and `l₂` are cyclic permutations
  of each other. This is defined by claiming that `∃ n, l.rotate n = l'`. -/
def is_rotated : Prop := ∃ n, l.rotate n = l'

infixr ` ~r `:1000 := is_rotated

variables {l l'}

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

lemma is_rotated_comm : l ~r l' ↔ l' ~r l :=
⟨is_rotated.symm, is_rotated.symm⟩

@[simp] protected lemma is_rotated.forall (l : list α) (n : ℕ) : l.rotate n ~r l :=
is_rotated.symm ⟨n, rfl⟩

@[trans] lemma is_rotated.trans {l'' : list α} (h : l ~r l') (h' : l' ~r l'') :
  l ~r l'' :=
begin
  obtain ⟨n, rfl⟩ := h,
  obtain ⟨m, rfl⟩ := h',
  rw rotate_rotate,
  use (n + m)
end

lemma is_rotated.eqv : equivalence (@is_rotated α) :=
mk_equivalence _ is_rotated.refl (λ _ _, is_rotated.symm) (λ _ _ _, is_rotated.trans)

/-- The relation `list.is_rotated l l'` forms a `setoid` of cycles. -/
def is_rotated.setoid (α : Type*) : setoid (list α) :=
{ r := is_rotated, iseqv := is_rotated.eqv }

lemma is_rotated.perm (h : l ~r l') : l ~ l' :=
exists.elim h (λ _ hl, hl ▸ (rotate_perm _ _).symm)

lemma is_rotated.nodup_iff (h : l ~r l') : nodup l ↔ nodup l' :=
h.perm.nodup_iff

lemma is_rotated.mem_iff (h : l ~r l') {a : α} : a ∈ l ↔ a ∈ l' :=
h.perm.mem_iff

@[simp] lemma is_rotated_nil_iff : l ~r [] ↔ l = [] :=
⟨λ ⟨n, hn⟩, by simpa using hn, λ h, h ▸ by refl⟩

@[simp] lemma is_rotated_nil_iff' : [] ~r l ↔ [] = l :=
by rw [is_rotated_comm, is_rotated_nil_iff, eq_comm]

@[simp] lemma is_rotated_singleton_iff {x : α} : l ~r [x] ↔ l = [x] :=
⟨λ ⟨n, hn⟩, by simpa using hn, λ h, h ▸ by refl⟩

@[simp] lemma is_rotated_singleton_iff' {x : α} : [x] ~r l ↔ [x] = l :=
by rw [is_rotated_comm, is_rotated_singleton_iff, eq_comm]

lemma is_rotated_concat (hd : α) (tl : list α) :
  (tl ++ [hd]) ~r (hd :: tl) :=
is_rotated.symm ⟨1, by simp⟩

lemma is_rotated_append : (l ++ l') ~r (l' ++ l) :=
⟨l.length, by simp⟩

lemma is_rotated.reverse (h : l ~r l') : l.reverse ~r l'.reverse :=
begin
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
  obtain ⟨n, rfl⟩ := h,
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

@[congr] theorem is_rotated.map {β : Type*} {l₁ l₂ : list α} (h : l₁ ~r l₂) (f : α → β) :
  map f l₁ ~r map f l₂ :=
begin
  obtain ⟨n, rfl⟩ := h,
  rw map_rotate,
  use n
end

/-- List of all cyclic permutations of `l`.
The `cyclic_permutations` of a nonempty list `l` will always contain `list.length l` elements.
This implies that under certain conditions, there are duplicates in `list.cyclic_permutations l`.
The `n`th entry is equal to `l.rotate n`, proven in `list.nth_le_cyclic_permutations`.
The proof that every cyclic permutant of `l` is in the list is `list.mem_cyclic_permutations_iff`.

     cyclic_permutations [1, 2, 3, 2, 4] =
       [[1, 2, 3, 2, 4], [2, 3, 2, 4, 1], [3, 2, 4, 1, 2],
        [2, 4, 1, 2, 3], [4, 1, 2, 3, 2]] -/
def cyclic_permutations : list α → list (list α)
| []         := [[]]
| l@(_ :: _) := init (zip_with (++) (tails l) (inits l))

@[simp] lemma cyclic_permutations_nil : cyclic_permutations ([] : list α) = [[]] := rfl

lemma cyclic_permutations_cons (x : α) (l : list α) :
  cyclic_permutations (x :: l) = init (zip_with (++) (tails (x :: l)) (inits (x :: l))) := rfl

lemma cyclic_permutations_of_ne_nil (l : list α) (h : l ≠ []) :
  cyclic_permutations l = init (zip_with (++) (tails l) (inits l)) :=
begin
  obtain ⟨hd, tl, rfl⟩ := exists_cons_of_ne_nil h,
  exact cyclic_permutations_cons _ _,
end

lemma length_cyclic_permutations_cons (x : α) (l : list α) :
  length (cyclic_permutations (x :: l)) = length l + 1 :=
by simp [cyclic_permutations_of_ne_nil]

@[simp] lemma length_cyclic_permutations_of_ne_nil (l : list α) (h : l ≠ []) :
  length (cyclic_permutations l) = length l :=
by simp [cyclic_permutations_of_ne_nil _ h]

@[simp] lemma nth_le_cyclic_permutations (l : list α) (n : ℕ)
  (hn : n < length (cyclic_permutations l)) :
  nth_le (cyclic_permutations l) n hn = l.rotate n :=
begin
  obtain rfl | h := eq_or_ne l [],
  { simp },
  { rw length_cyclic_permutations_of_ne_nil _ h at hn,
    simp [init_eq_take, cyclic_permutations_of_ne_nil _ h, nth_le_take',
          rotate_eq_drop_append_take hn.le] }
end

lemma mem_cyclic_permutations_self (l : list α) :
  l ∈ cyclic_permutations l :=
begin
  cases l with x l,
  { simp },
  { rw mem_iff_nth_le,
    refine ⟨0, by simp, _⟩,
    simp }
end

lemma length_mem_cyclic_permutations (l : list α) (h : l' ∈ cyclic_permutations l) :
  length l' = length l :=
begin
  obtain ⟨k, hk, rfl⟩ := nth_le_of_mem h,
  simp
end

@[simp] lemma mem_cyclic_permutations_iff {l l' : list α} :
  l ∈ cyclic_permutations l' ↔ l ~r l' :=
begin
  split,
  { intro h,
    obtain ⟨k, hk, rfl⟩ := nth_le_of_mem h,
    simp },
  { intro h,
    obtain ⟨k, rfl⟩ := h.symm,
    rw mem_iff_nth_le,
    simp only [exists_prop, nth_le_cyclic_permutations],
    cases l' with x l,
    { simp },
    { refine ⟨k % length (x :: l), _, rotate_mod _ _⟩,
      simpa using nat.mod_lt _ (zero_lt_succ _) } }
end

@[simp] lemma cyclic_permutations_eq_nil_iff {l : list α} :
  cyclic_permutations l = [[]] ↔ l = [] :=
begin
  refine ⟨λ h, _, λ h, by simp [h]⟩,
  rw [eq_comm, ←is_rotated_nil_iff', ←mem_cyclic_permutations_iff, h, mem_singleton]
end

@[simp] lemma cyclic_permutations_eq_singleton_iff {l : list α} {x : α} :
  cyclic_permutations l = [[x]] ↔ l = [x] :=
begin
  refine ⟨λ h, _, λ h, by simp [cyclic_permutations, h, init_eq_take]⟩,
  rw [eq_comm, ←is_rotated_singleton_iff', ←mem_cyclic_permutations_iff, h, mem_singleton]
end

/-- If a `l : list α` is `nodup l`, then all of its cyclic permutants are distinct. -/
lemma nodup.cyclic_permutations {l : list α} (hn : nodup l) :
  nodup (cyclic_permutations l) :=
begin
  cases l with x l,
  { simp },
  rw nodup_iff_nth_le_inj,
  intros i j hi hj h,
  simp only [length_cyclic_permutations_cons] at hi hj,
  rw [←mod_eq_of_lt hi, ←mod_eq_of_lt hj, ←length_cons x l],
  apply hn.rotate_congr,
  { simp },
  { simpa using h }
end

@[simp] lemma cyclic_permutations_rotate (l : list α) (k : ℕ) :
  (l.rotate k).cyclic_permutations = l.cyclic_permutations.rotate k :=
begin
  have : (l.rotate k).cyclic_permutations.length = length (l.cyclic_permutations.rotate k),
  { cases l,
    { simp },
    { rw length_cyclic_permutations_of_ne_nil;
      simp } },
  refine ext_le this (λ n hn hn', _),
  rw [nth_le_cyclic_permutations, nth_le_rotate, nth_le_cyclic_permutations,
      rotate_rotate, ←rotate_mod, add_comm],
  cases l;
  simp
end

lemma is_rotated.cyclic_permutations {l l' : list α} (h : l ~r l') :
  l.cyclic_permutations ~r l'.cyclic_permutations :=
begin
  obtain ⟨k, rfl⟩ := h,
  exact ⟨k, by simp⟩
end

@[simp] lemma is_rotated_cyclic_permutations_iff {l l' : list α} :
  l.cyclic_permutations ~r l'.cyclic_permutations ↔ l ~r l' :=
begin
  by_cases hl : l = [],
  { simp [hl, eq_comm] },
  have hl' : l.cyclic_permutations.length = l.length := length_cyclic_permutations_of_ne_nil _ hl,
  refine ⟨λ h, _, is_rotated.cyclic_permutations⟩,
  obtain ⟨k, hk⟩ := h,
  refine ⟨k % l.length, _⟩,
  have hk' : k % l.length < l.length := mod_lt _ (length_pos_of_ne_nil hl),
  rw [←nth_le_cyclic_permutations _ _ (hk'.trans_le hl'.ge), ←nth_le_rotate' _ k],
  simp [hk, hl', nat.sub_add_cancel hk'.le]
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

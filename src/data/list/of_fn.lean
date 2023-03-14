/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fin.tuple.basic
import data.list.join
import data.list.pairwise

/-!
# Lists from functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Theorems and lemmas for dealing with `list.of_fn`, which converts a function on `fin n` to a list
of length `n`.

## Main Statements

The main statements pertain to lists generated using `of_fn`

- `list.length_of_fn`, which tells us the length of such a list
- `list.nth_of_fn`, which tells us the nth element of such a list
- `list.array_eq_of_fn`, which interprets the list form of an array as such a list.
- `list.equiv_sigma_tuple`, which is an `equiv` between lists and the functions that generate them
  via `list.of_fn`.
-/

universes u

variables {α : Type u}

open nat
namespace list

lemma length_of_fn_aux {n} (f : fin n → α) :
  ∀ m h l, length (of_fn_aux f m h l) = length l + m
| 0        h l := rfl
| (succ m) h l := (length_of_fn_aux m _ _).trans (succ_add _ _)

/-- The length of a list converted from a function is the size of the domain. -/
@[simp] theorem length_of_fn {n} (f : fin n → α) : length (of_fn f) = n :=
(length_of_fn_aux f _ _ _).trans (zero_add _)

lemma nth_of_fn_aux {n} (f : fin n → α) (i) :
  ∀ m h l,
    (∀ i, nth l i = of_fn_nth_val f (i + m)) →
     nth (of_fn_aux f m h l) i = of_fn_nth_val f i
| 0        h l H := H i
| (succ m) h l H := nth_of_fn_aux m _ _ begin
  intro j, cases j with j,
  { simp only [nth, of_fn_nth_val, zero_add, dif_pos (show m < n, from h)] },
  { simp only [nth, H, add_succ, succ_add] }
end

/-- The `n`th element of a list -/
@[simp] theorem nth_of_fn {n} (f : fin n → α) (i) :
  nth (of_fn f) i = of_fn_nth_val f i :=
nth_of_fn_aux f _ _ _ _ $ λ i,
by simp only [of_fn_nth_val, dif_neg (not_lt.2 (nat.le_add_left n i))]; refl

theorem nth_le_of_fn {n} (f : fin n → α) (i : fin n) :
  nth_le (of_fn f) i ((length_of_fn f).symm ▸ i.2) = f i :=
option.some.inj $ by rw [← nth_le_nth];
  simp only [list.nth_of_fn, of_fn_nth_val, fin.eta, dif_pos i.is_lt]

@[simp] theorem nth_le_of_fn' {n} (f : fin n → α) {i : ℕ} (h : i < (of_fn f).length) :
  nth_le (of_fn f) i h = f ⟨i, ((length_of_fn f) ▸ h)⟩ :=
nth_le_of_fn f ⟨i, ((length_of_fn f) ▸ h)⟩

@[simp] lemma map_of_fn {β : Type*} {n : ℕ} (f : fin n → α) (g : α → β) :
  map g (of_fn f) = of_fn (g ∘ f) :=
ext_le (by simp) (λ i h h', by simp)

/-- Arrays converted to lists are the same as `of_fn` on the indexing function of the array. -/
theorem array_eq_of_fn {n} (a : array n α) : a.to_list = of_fn a.read :=
suffices ∀ {m h l}, d_array.rev_iterate_aux a
  (λ i, cons) m h l = of_fn_aux (d_array.read a) m h l, from this,
begin
  intros, induction m with m IH generalizing l, {refl},
  simp only [d_array.rev_iterate_aux, of_fn_aux, IH]
end

@[congr]
theorem of_fn_congr {m n : ℕ} (h : m = n) (f : fin m → α) :
  of_fn f = of_fn (λ i : fin n, f (fin.cast h.symm i)) :=
begin
  subst h,
  simp_rw [fin.cast_refl, order_iso.refl_apply],
end

/-- `of_fn` on an empty domain is the empty list. -/
@[simp] theorem of_fn_zero (f : fin 0 → α) : of_fn f = [] := rfl

@[simp] theorem of_fn_succ {n} (f : fin (succ n) → α) :
  of_fn f = f 0 :: of_fn (λ i, f i.succ) :=
suffices ∀ {m h l}, of_fn_aux f (succ m) (succ_le_succ h) l =
  f 0 :: of_fn_aux (λ i, f i.succ) m h l, from this,
begin
  intros, induction m with m IH generalizing l, {refl},
  rw [of_fn_aux, IH], refl
end

theorem of_fn_succ' {n} (f : fin (succ n) → α) :
  of_fn f = (of_fn (λ i, f i.cast_succ)).concat (f (fin.last _)) :=
begin
  induction n with n IH,
  { rw [of_fn_zero, concat_nil, of_fn_succ, of_fn_zero], refl },
  { rw [of_fn_succ, IH, of_fn_succ, concat_cons, fin.cast_succ_zero],
    congr' 3,
    simp_rw [fin.cast_succ_fin_succ], }
end

@[simp] lemma of_fn_eq_nil_iff {n : ℕ} {f : fin n → α} :
  of_fn f = [] ↔ n = 0 :=
by cases n; simp only [of_fn_zero, of_fn_succ, eq_self_iff_true, nat.succ_ne_zero]

lemma last_of_fn {n : ℕ} (f : fin n → α) (h : of_fn f ≠ [])
  (hn : n - 1 < n := nat.pred_lt $ of_fn_eq_nil_iff.not.mp h) :
  last (of_fn f) h = f ⟨n - 1, hn⟩ :=
by simp [last_eq_nth_le]

lemma last_of_fn_succ {n : ℕ} (f : fin n.succ → α)
  (h : of_fn f ≠ [] := mt of_fn_eq_nil_iff.mp (nat.succ_ne_zero _)) :
  last (of_fn f) h = f (fin.last _) :=
last_of_fn f h

/-- Note this matches the convention of `list.of_fn_succ'`, putting the `fin m` elements first. -/
theorem of_fn_add {m n} (f : fin (m + n) → α) :
  list.of_fn f = list.of_fn (λ i, f (fin.cast_add n i)) ++ list.of_fn (λ j, f (fin.nat_add m j)) :=
begin
  induction n with n IH,
  { rw [of_fn_zero, append_nil, fin.cast_add_zero, fin.cast_refl], refl },
  { rw [of_fn_succ', of_fn_succ', IH, append_concat], refl, },
end

@[simp] theorem of_fn_fin_append {m n} (a : fin m → α) (b : fin n → α) :
  list.of_fn (fin.append a b) = list.of_fn a ++ list.of_fn b :=
by simp_rw [of_fn_add, fin.append_left, fin.append_right]

/-- This breaks a list of `m*n` items into `m` groups each containing `n` elements. -/
theorem of_fn_mul {m n} (f : fin (m * n) → α) :
  list.of_fn f = list.join (list.of_fn $ λ i : fin m, list.of_fn $ λ j : fin n,
  f ⟨i * n + j,
    calc ↑i * n + j < (i + 1) *n : (add_lt_add_left j.prop _).trans_eq (add_one_mul _ _).symm
                ... ≤ _ : nat.mul_le_mul_right _ i.prop⟩) :=
begin
  induction m with m IH,
  { simp_rw [of_fn_zero, zero_mul, of_fn_zero, join], },
  { simp_rw [of_fn_succ', succ_mul, join_concat, of_fn_add, IH], refl, },
end

/-- This breaks a list of `m*n` items into `n` groups each containing `m` elements. -/
theorem of_fn_mul' {m n} (f : fin (m * n) → α) :
  list.of_fn f = list.join (list.of_fn $ λ i : fin n, list.of_fn $ λ j : fin m,
  f ⟨m * i + j,
    calc m * i + j < m * (i + 1) : (add_lt_add_left j.prop _).trans_eq (mul_add_one _ _).symm
               ... ≤ _ : nat.mul_le_mul_left _ i.prop⟩) :=
by simp_rw [mul_comm m n, mul_comm m, of_fn_mul, fin.cast_mk]

theorem of_fn_nth_le : ∀ l : list α, of_fn (λ i, nth_le l i i.2) = l
| [] := rfl
| (a::l) := by { rw of_fn_succ, congr, simp only [fin.coe_succ], exact of_fn_nth_le l }

-- not registered as a simp lemma, as otherwise it fires before `forall_mem_of_fn_iff` which
-- is much more useful
lemma mem_of_fn {n} (f : fin n → α) (a : α) :
  a ∈ of_fn f ↔ a ∈ set.range f :=
begin
  simp only [mem_iff_nth_le, set.mem_range, nth_le_of_fn'],
  exact ⟨λ ⟨i, hi, h⟩, ⟨_, h⟩, λ ⟨i, hi⟩, ⟨i.1, (length_of_fn f).symm ▸ i.2, by simpa using hi⟩⟩
end

@[simp] lemma forall_mem_of_fn_iff {n : ℕ} {f : fin n → α} {P : α → Prop} :
  (∀ i ∈ of_fn f, P i) ↔ ∀ j : fin n, P (f j) :=
by simp only [mem_of_fn, set.forall_range_iff]

@[simp] lemma of_fn_const (n : ℕ) (c : α) :
  of_fn (λ i : fin n, c) = replicate n c :=
nat.rec_on n (by simp) $ λ n ihn, by simp [ihn]

@[simp] theorem of_fn_fin_repeat {m} (a : fin m → α) (n : ℕ) :
  list.of_fn (fin.repeat n a) = (list.replicate n (list.of_fn a)).join :=
by simp_rw [of_fn_mul, ←of_fn_const, fin.repeat, fin.mod_nat, fin.coe_mk,
  add_comm, nat.add_mul_mod_self_right, nat.mod_eq_of_lt (fin.is_lt _), fin.eta]

@[simp] lemma pairwise_of_fn {R : α → α → Prop} {n} {f : fin n → α} :
  (of_fn f).pairwise R ↔ ∀ ⦃i j⦄, i < j → R (f i) (f j) :=
by { simp only [pairwise_iff_nth_le, fin.forall_iff, length_of_fn, nth_le_of_fn', fin.mk_lt_mk],
  exact ⟨λ h i hi j hj hij, h _ _ hj hij, λ h i j hj hij, h _ (hij.trans hj) _ hj hij⟩ }

/-- Lists are equivalent to the sigma type of tuples of a given length. -/
@[simps]
def equiv_sigma_tuple : list α ≃ Σ n, fin n → α :=
{ to_fun := λ l, ⟨l.length, λ i, l.nth_le ↑i i.2⟩,
  inv_fun := λ f, list.of_fn f.2,
  left_inv := list.of_fn_nth_le,
  right_inv := λ ⟨n, f⟩, fin.sigma_eq_of_eq_comp_cast (length_of_fn _) $ funext $ λ i,
    nth_le_of_fn' f i.prop }

/-- A recursor for lists that expands a list into a function mapping to its elements.

This can be used with `induction l using list.of_fn_rec`. -/
@[elab_as_eliminator]
def of_fn_rec {C : list α → Sort*} (h : Π n (f : fin n → α), C (list.of_fn f)) (l : list α) : C l :=
cast (congr_arg _ l.of_fn_nth_le) $ h l.length (λ i, l.nth_le ↑i i.2)

@[simp]
lemma of_fn_rec_of_fn {C : list α → Sort*} (h : Π n (f : fin n → α), C (list.of_fn f))
  {n : ℕ} (f : fin n → α) : @of_fn_rec _ C h (list.of_fn f) = h _ f :=
equiv_sigma_tuple.right_inverse_symm.cast_eq (λ s, h s.1 s.2) ⟨n, f⟩

lemma exists_iff_exists_tuple {P : list α → Prop} :
  (∃ l : list α, P l) ↔ ∃ n (f : fin n → α), P (list.of_fn f) :=
equiv_sigma_tuple.symm.surjective.exists.trans sigma.exists

lemma forall_iff_forall_tuple {P : list α → Prop} :
  (∀ l : list α, P l) ↔ ∀ n (f : fin n → α), P (list.of_fn f) :=
equiv_sigma_tuple.symm.surjective.forall.trans sigma.forall

/-- `fin.sigma_eq_iff_eq_comp_cast` may be useful to work with the RHS of this expression. -/
lemma of_fn_inj' {m n : ℕ} {f : fin m → α} {g : fin n → α} :
  of_fn f = of_fn g ↔ (⟨m, f⟩ : Σ n, fin n → α) = ⟨n, g⟩ :=
iff.symm $ equiv_sigma_tuple.symm.injective.eq_iff.symm

/-- Note we can only state this when the two functions are indexed by defeq `n`. -/
lemma of_fn_injective {n : ℕ} : function.injective (of_fn : (fin n → α) → list α) :=
λ f g h, eq_of_heq $ by injection of_fn_inj'.mp h

/-- A special case of `list.of_fn_inj'` for when the two functions are indexed by defeq `n`. -/
@[simp] lemma of_fn_inj {n : ℕ} {f g : fin n → α} : of_fn f = of_fn g ↔ f = g :=
of_fn_injective.eq_iff

end list

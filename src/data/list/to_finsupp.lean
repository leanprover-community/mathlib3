/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.list.nthd
import data.finsupp.basic

/-!

## Lists as finsupp

-/

namespace list

variables {M : Type*} [has_zero M] (l : list M)
  [decidable_pred (λ (i : ℕ), nthd 0 l i ≠ 0)] (n : ℕ)

/-- Indexing into a `l : list M`, as a finitely-supported function,
where the support are all the indices within the length of the list
that index to a non-zero value. -/
def to_finsupp : ℕ →₀ M :=
{ to_fun := nthd 0 l,
  support := (finset.range l.length).filter (λ i, nthd 0 l i ≠ 0),
  mem_support_to_fun := λ n, begin
    simp only [ne.def, finset.mem_filter, finset.mem_range, and_iff_right_iff_imp],
    contrapose!,
    exact nthd_eq_default _ _
  end }

lemma to_finsupp_coe : (l.to_finsupp : ℕ → M) = l.nthd 0 := rfl

lemma to_finsupp_support :
  l.to_finsupp.support = (finset.range l.length).filter (λ i, nthd 0 l i ≠ 0) :=
rfl

lemma to_finsupp_apply_lt (hn : n < l.length) :
  l.to_finsupp n = l.nth_le n hn :=
nthd_eq_nth_le _ _ _

lemma to_finsupp_apply_le (hn : l.length ≤ n) :
  l.to_finsupp n = 0 :=
nthd_eq_default _ _ hn

@[simp] lemma to_finsupp_nil : to_finsupp ([] : list M) = 0 :=
by { ext, simp [to_finsupp_coe] }

 lemma to_finsupp_singleton (x : M)
  [decidable_pred (λ (i : ℕ), nthd 0 [x] i ≠ 0)] :
  to_finsupp [x] = finsupp.single 0 x :=
begin
  ext ⟨_|i⟩;
  simp [to_finsupp_coe, finsupp.single_apply, (nat.zero_lt_succ _).ne]
end

@[simp] lemma to_finsupp_cons_apply_zero (x : M) (xs : list M)
  [decidable_pred (λ (i : ℕ), nthd 0 (x :: xs) i ≠ 0)] :
  (x :: xs).to_finsupp 0 = x := rfl

@[simp] lemma to_finsupp_cons_apply_succ (x : M) (xs : list M) (n : ℕ)
  [decidable_pred (λ (i : ℕ), nthd 0 (x :: xs) i ≠ 0)]
  [decidable_pred (λ (i : ℕ), nthd 0 xs i ≠ 0)] :
  (x :: xs).to_finsupp n.succ = xs.to_finsupp n := rfl

lemma to_finsupp_cons_eq_single_add_emb_domain
  {R : Type*} [add_zero_class R] (x : R) (xs : list R)
  [decidable_pred (λ (i : ℕ), nthd 0 (x :: xs) i ≠ 0)]
  [decidable_pred (λ (i : ℕ), nthd 0 xs i ≠ 0)] :
  to_finsupp (x :: xs) = finsupp.single 0 x +
    (to_finsupp xs).emb_domain ⟨nat.succ, nat.succ_injective⟩ :=
begin
  ext (_|i),
  { simp only [nat.nat_zero_eq_zero, to_finsupp_cons_apply_zero, finsupp.coe_add,
               pi.add_apply, finsupp.single_eq_same],
    rw finsupp.emb_domain_notin_range,
    { exact (add_zero _).symm },
    { simp } },
  { simp only [to_finsupp_cons_apply_succ, finsupp.coe_add, pi.add_apply],
    have hi : i.succ = (⟨nat.succ, nat.succ_injective⟩ : ℕ ↪ ℕ) i := rfl,
    rw [finsupp.single_apply_eq_zero.mpr, zero_add, hi, finsupp.emb_domain_apply],
    simp }
end

lemma to_finsupp_concat_eq_to_finsupp_add_single
  {R : Type*} [add_zero_class R] (x : R) (xs : list R)
  [decidable_pred (λ (i : ℕ), nthd 0 (xs ++ [x]) i ≠ 0)]
  [decidable_pred (λ (i : ℕ), nthd 0 xs i ≠ 0)] :
  to_finsupp (xs ++ [x]) = to_finsupp xs + finsupp.single xs.length x :=
begin
  ext i,
  simp only [finsupp.coe_add, pi.add_apply, finsupp.single_apply],
  rcases lt_trichotomy xs.length i with hi|rfl|hi,
  { rw [to_finsupp_apply_le _ _ hi.le, to_finsupp_apply_le,
        if_neg hi.ne, add_zero],
    simpa using nat.succ_le_of_lt hi },
  { rw [to_finsupp_apply_lt, to_finsupp_apply_le _ _ le_rfl,
        if_pos rfl, zero_add, nth_le_append_right le_rfl],
    { simp },
    { simp } },
  { rw [to_finsupp_apply_lt _ _ hi, to_finsupp_apply_lt, if_neg hi.ne', add_zero,
        nth_le_append],
    simpa using nat.lt_succ_of_lt hi }
end

lemma nthd_singleton_eq_update_const {α : Type*} (d x : α) :
  nthd d [x] = function.update (function.const _ d) 0 x :=
by { ext ⟨_|n⟩; simp }

lemma to_finsupp_eq_sum_map_enum_single {R : Type*} [add_monoid R] (l : list R)
  [decidable_pred (λ (i : ℕ), nthd 0 l i ≠ 0)] :
  to_finsupp l = (l.enum.map (λ (nr : ℕ × R), finsupp.single nr.1 nr.2)).sum :=
begin
  unfreezingI { induction l using list.reverse_rec_on with xs x IH },
  { convert to_finsupp_nil },
  { simp only [enum_append, map, enum_from_singleton, map_append, sum_append, sum_cons,
               sum_nil, add_zero],
    classical,
    convert to_finsupp_concat_eq_to_finsupp_add_single _ _,
    exact IH.symm }
end

end list

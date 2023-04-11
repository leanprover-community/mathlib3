/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.finsupp.basic

/-!

# Lists as finsupp

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

# Main definitions

- `list.to_finsupp`: Interpret a list as a finitely supported function, where the indexing type
is `ℕ`, and the values are either the elements of the list (accessing by indexing) or `0` outside
of the list.

# Main theorems

- `list.to_finsupp_eq_sum_map_enum_single`: A `l : list M` over `M` an `add_monoid`,
when interpreted as a finitely supported function, is equal to the sum of `finsupp.single`
produced by mapping over `list.enum l`.

## Implementation details

The functions defined here rely on a decidability predicate that each element in the list
can be decidably determined to be not equal to zero or that one can decide one is out of the
bounds of a list. For concretely defined lists that are made up of elements of decidable terms,
this holds. More work will be needed to support lists over non-dec-eq types like `ℝ`, where the
elements are beyond the dec-eq terms of casted values from `ℕ, ℤ, ℚ`.

-/

namespace list

variables {M : Type*} [has_zero M] (l : list M)
  [decidable_pred (λ i, nthd l i 0 ≠ 0)] (n : ℕ)

/-- Indexing into a `l : list M`, as a finitely-supported function,
where the support are all the indices within the length of the list
that index to a non-zero value. Indices beyond the end of the list are sent to 0.

This is a computable version of the `finsupp.on_finset` construction.
-/
def to_finsupp : ℕ →₀ M :=
{ to_fun := λ i, nthd l i 0,
  support := (finset.range l.length).filter (λ i, nthd l i 0 ≠ 0),
  mem_support_to_fun := λ n, begin
    simp only [ne.def, finset.mem_filter, finset.mem_range, and_iff_right_iff_imp],
    contrapose!,
    exact nthd_eq_default _ _
  end }

@[norm_cast] lemma coe_to_finsupp : (l.to_finsupp : ℕ → M) = λ i, l.nthd i 0 := rfl
@[simp, norm_cast] lemma to_finsupp_apply (i : ℕ) :
  (l.to_finsupp : ℕ → M) i = l.nthd i 0 := rfl

lemma to_finsupp_support :
  l.to_finsupp.support = (finset.range l.length).filter (λ i, nthd l i 0 ≠ 0) :=
rfl

lemma to_finsupp_apply_lt (hn : n < l.length) :
  l.to_finsupp n = l.nth_le n hn :=
nthd_eq_nth_le _ _ _

lemma to_finsupp_apply_le (hn : l.length ≤ n) :
  l.to_finsupp n = 0 :=
nthd_eq_default _ _ hn

@[simp] lemma to_finsupp_nil [decidable_pred (λ i, nthd ([] : list M) i 0 ≠ 0)] :
  to_finsupp ([] : list M) = 0 :=
by { ext, simp }

lemma to_finsupp_singleton (x : M)
  [decidable_pred (λ i, nthd [x] i 0 ≠ 0)] :
  to_finsupp [x] = finsupp.single 0 x :=
begin
  ext ⟨_|i⟩;
  simp [finsupp.single_apply, (nat.zero_lt_succ _).ne]
end

@[simp] lemma to_finsupp_cons_apply_zero (x : M) (xs : list M)
  [decidable_pred (λ i, nthd (x :: xs) i 0 ≠ 0)] :
  (x :: xs).to_finsupp 0 = x := rfl

@[simp] lemma to_finsupp_cons_apply_succ (x : M) (xs : list M) (n : ℕ)
  [decidable_pred (λ i, nthd (x :: xs) i 0 ≠ 0)]
  [decidable_pred (λ i, nthd xs i 0 ≠ 0)] :
  (x :: xs).to_finsupp n.succ = xs.to_finsupp n := rfl

lemma to_finsupp_cons_eq_single_add_emb_domain
  {R : Type*} [add_zero_class R] (x : R) (xs : list R)
  [decidable_pred (λ i, nthd (x :: xs) i 0 ≠ 0)]
  [decidable_pred (λ i, nthd xs i 0 ≠ 0)] :
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
  [decidable_pred (λ i, nthd (xs ++ [x]) i 0 ≠ 0)]
  [decidable_pred (λ i, nthd xs i 0 ≠ 0)] :
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

lemma to_finsupp_eq_sum_map_enum_single {R : Type*} [add_monoid R] (l : list R)
  [decidable_pred (λ i, nthd l i 0 ≠ 0)] :
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

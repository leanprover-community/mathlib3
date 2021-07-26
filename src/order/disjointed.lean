/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies
-/
import order.partial_sups

/-!
# Consecutive differences of sets

This file defines a way to make a sequence of sets into a sequence of disjoint sets.

## Main declarations

* `disjointed f`: Yields the sequence of sets `f 0`, `f 1 \ f 0`, `f 2 \ (f 0 ∪ f 1)`, ... This
  sequence has the same union as `f 0`, `f 1`, `f 2` but with disjoint sets.
-/

variables {α β : Type*}

section generalized_boolean_algebra
variables [generalized_boolean_algebra α]

/-- If `f : ℕ → α` is a sequence of elements, then `disjointed f` is the sequence formed by
subtracting each element from the nexts. This is the unique disjoint sequence whose partial sups
are the same as the original sequence. -/
def disjointed (f : ℕ → α) : ℕ → α
| 0       := f 0
| (n + 1) := f (n + 1) \ (partial_sups f n)

lemma disjointed_zero (f : ℕ → α) : disjointed f 0 = f 0 := rfl

lemma disjointed_succ (f : ℕ → α) (n : ℕ) :
  disjointed f (n + 1) = f (n + 1) \ (partial_sups f n) :=
rfl

lemma disjointed_le (f : ℕ → α) : disjointed f ≤ f :=
begin
  rintro n,
  cases n,
  { refl },
  { exact sdiff_le }
end

lemma disjoint_disjointed (f : ℕ → α) : pairwise (disjoint on disjointed f) :=
begin
  rw symmetric.pairwise_on disjoint.symm, swap, apply_instance,
  rintro m n h,
  cases n,
  { exact (h.not_le (nat.zero_le _)).elim },
  exact disjoint_sdiff_self_right.mono_left ((disjointed_le f m).trans
    (le_partial_sups_of_le f (nat.lt_add_one_iff.1 h))),
end

/-- An induction principle for `disjointed`. To define/prove something on `disjointed f n`, it's
enough to define/prove it for `f n` and being able to extend through diffs. -/
def disjointed_induct {f : ℕ → α} {p : α → Sort*} (hdiff : ∀ ⦃t i⦄, p t → p (t \ f i)) :
  ∀ ⦃n⦄, p (f n) → p (disjointed f n)
| 0       := id
| (n + 1) := λ h,
  begin
    rw disjointed_succ,
    suffices H : ∀ k, p (f (n + 1) \ partial_sups f k),
    { exact H n },
    rintro k,
    induction k with k ih,
    { rw partial_sups_zero,
      exact hdiff h },
    rw [partial_sups_succ, ←sdiff_sdiff_left],
    exact hdiff ih,
  end

lemma monotone.disjointed_eq {f : ℕ → α} (hf : monotone f) (n : ℕ) :
  disjointed f (n + 1) = f (n + 1) \ f n :=
by rw [disjointed_succ, hf.partial_sups_eq]

lemma partial_sups_disjointed_eq (f : ℕ → α) :
  partial_sups (disjointed f) = partial_sups f :=
begin
  ext n,
  induction n with k ih,
  { rw [partial_sups_zero, partial_sups_zero, disjointed_zero] },
  { rw [partial_sups_succ, partial_sups_succ, disjointed_succ, ih, sup_sdiff_self_right] }
end

end generalized_boolean_algebra

section complete_boolean_algebra
variables [complete_boolean_algebra α]

lemma le_supr_disjointed (f : ℕ → α) (n : ℕ) : f n ≤ ⨆ i ≤ n, disjointed f i :=
by { rw [←partial_sups_eq_supr, partial_sups_disjointed_eq], exact le_partial_sups _ _ }

lemma supr_disjointed_eq (f : ℕ → α) : (⨆ n, disjointed f n) = (⨆ n, f n) :=
(supr_le_supr (λ n, disjointed_le f n)).antisymm
  (supr_le (λ i, (le_supr_disjointed _ _).trans (bsupr_le_supr _ _)))

lemma disjointed_eq_inf_compl (f : ℕ → α) (n : ℕ) :
  disjointed f n = f n ⊓ (⨅ i < n, (f i)ᶜ) :=
begin
  cases n,
  { rw [disjointed_zero, eq_comm, inf_eq_left],
    simp_rw le_infi_iff,
    exact λ i hi, (i.not_lt_zero hi).elim },
  simp_rw [disjointed_succ, partial_sups_eq_supr, sdiff_eq, compl_supr],
  congr,
  ext i,
  sorry
end

end complete_boolean_algebra

/-! ### Set notation variants of lemmas -/

lemma disjointed_subset (f : ℕ → set α) (n : ℕ) : disjointed f n ⊆ f n :=
disjointed_le f n

lemma Union_disjointed_eq {f : ℕ → set α} : (⋃ n, disjointed f n) = (⋃ n, f n) :=
supr_disjointed_eq f

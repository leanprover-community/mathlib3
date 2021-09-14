/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies
-/
import order.partial_sups

/-!
# Consecutive differences of sets

This file defines the way to make a sequence of elements into a sequence of disjoint elements with
the same partial sups.

For a sequence `f : ℕ → α`, this new sequence will be `f 0`, `f 1 \ f 0`, `f 2 \ (f 0 ⊔ f 1)`.
It is actually unique, as `disjointed_unique` shows.

## Main declarations

* `disjointed f`: The sequence `f 0`, `f 1 \ f 0`, `f 2 \ (f 0 ⊔ f 1)`, ....
* `partial_sups_disjointed`: `disjointed f` has the same partial sups as `f`.
* `disjoint_disjointed`: The elements of `disjointed f` are pairwise disjoint.
* `disjointed_unique`: `disjointed f` is the only pairwise disjoint sequence having the same partial
  sups as `f`.
* `supr_disjointed`: `disjointed f` has the same supremum as `f`. Limiting case of
  `partial_sups_disjointed`.

We also provide set notation variants of some lemmas.

## TODO

Find a useful statement of `disjointed_rec_succ`.

One could generalize `disjointed` to any locally finite bot preorder domain, in place of `ℕ`.
Related to the TODO in the module docstring of `order.partial_sups`.
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

@[simp] lemma disjointed_zero (f : ℕ → α) : disjointed f 0 = f 0 := rfl

lemma disjointed_succ (f : ℕ → α) (n : ℕ) :
  disjointed f (n + 1) = f (n + 1) \ (partial_sups f n) :=
rfl

lemma disjointed_le_id : disjointed ≤ (id : (ℕ → α) → ℕ → α) :=
begin
  rintro f n,
  cases n,
  { refl },
  { exact sdiff_le }
end

lemma disjointed_le (f : ℕ → α) : disjointed f ≤ f := disjointed_le_id f

lemma disjoint_disjointed (f : ℕ → α) : pairwise (disjoint on disjointed f) :=
begin
  refine (symmetric.pairwise_on disjoint.symm _).2 (λ m n h, _),
  cases n,
  { exact (nat.not_lt_zero _ h).elim },
  exact disjoint_sdiff_self_right.mono_left ((disjointed_le f m).trans
    (le_partial_sups_of_le f (nat.lt_add_one_iff.1 h))),
end

/-- An induction principle for `disjointed`. To define/prove something on `disjointed f n`, it's
enough to define/prove it for `f n` and being able to extend through diffs. -/
def disjointed_rec {f : ℕ → α} {p : α → Sort*} (hdiff : ∀ ⦃t i⦄, p t → p (t \ f i)) :
  ∀ ⦃n⦄, p (f n) → p (disjointed f n)
| 0       := id
| (n + 1) := λ h,
  begin
    suffices H : ∀ k, p (f (n + 1) \ partial_sups f k),
    { exact H n },
    rintro k,
    induction k with k ih,
    { exact hdiff h },
    rw [partial_sups_succ, ←sdiff_sdiff_left],
    exact hdiff ih,
  end

@[simp] lemma disjointed_rec_zero {f : ℕ → α} {p : α → Sort*} (hdiff : ∀ ⦃t i⦄, p t → p (t \ f i))
  (h₀ : p (f 0)) :
  disjointed_rec hdiff h₀ = h₀ := rfl

-- TODO: Find a useful statement of `disjointed_rec_succ`.

lemma monotone.disjointed_eq {f : ℕ → α} (hf : monotone f) (n : ℕ) :
  disjointed f (n + 1) = f (n + 1) \ f n :=
by rw [disjointed_succ, hf.partial_sups_eq]

@[simp] lemma partial_sups_disjointed (f : ℕ → α) :
  partial_sups (disjointed f) = partial_sups f :=
begin
  ext n,
  induction n with k ih,
  { rw [partial_sups_zero, partial_sups_zero, disjointed_zero] },
  { rw [partial_sups_succ, partial_sups_succ, disjointed_succ, ih, sup_sdiff_self_right] }
end

/-- `disjointed f` is the unique sequence that is pairwise disjoint and has the same partial sups
as `f`. -/
lemma disjointed_unique {f d : ℕ → α} (hdisj : pairwise (disjoint on d))
  (hsups : partial_sups d = partial_sups f) : d = disjointed f :=
begin
  ext n,
  cases n,
  { rw [←partial_sups_zero d, hsups, partial_sups_zero, disjointed_zero] },
  suffices h : d n.succ = partial_sups d n.succ \ partial_sups d n,
  { rw [h, hsups, partial_sups_succ, disjointed_succ, sup_sdiff, sdiff_self, bot_sup_eq] },
  rw [partial_sups_succ, sup_sdiff, sdiff_self, bot_sup_eq, eq_comm, sdiff_eq_self_iff_disjoint],
  suffices h : ∀ m ≤ n, disjoint (partial_sups d m) (d n.succ),
  { exact h n le_rfl },
  rintro m hm,
  induction m with m ih,
  { exact hdisj _ _ (nat.succ_ne_zero _).symm },
  rw [partial_sups_succ, disjoint_iff, inf_sup_right, sup_eq_bot_iff, ←disjoint_iff, ←disjoint_iff],
  exact ⟨ih (nat.le_of_succ_le hm), hdisj _ _ (nat.lt_succ_of_le hm).ne⟩,
end

end generalized_boolean_algebra

section complete_boolean_algebra
variables [complete_boolean_algebra α]

lemma supr_disjointed (f : ℕ → α) : (⨆ n, disjointed f n) = (⨆ n, f n) :=
supr_eq_supr_of_partial_sups_eq_partial_sups (partial_sups_disjointed f)

lemma disjointed_eq_inf_compl (f : ℕ → α) (n : ℕ) :
  disjointed f n = f n ⊓ (⨅ i < n, (f i)ᶜ) :=
begin
  cases n,
  { rw [disjointed_zero, eq_comm, inf_eq_left],
    simp_rw le_infi_iff,
    exact λ i hi, (i.not_lt_zero hi).elim },
  simp_rw [disjointed_succ, partial_sups_eq_bsupr, sdiff_eq, compl_supr],
  congr,
  ext i,
  rw nat.lt_succ_iff,
end

end complete_boolean_algebra

/-! ### Set notation variants of lemmas -/

lemma disjointed_subset (f : ℕ → set α) (n : ℕ) : disjointed f n ⊆ f n :=
disjointed_le f n

lemma Union_disjointed {f : ℕ → set α} : (⋃ n, disjointed f n) = (⋃ n, f n) :=
supr_disjointed f

lemma disjointed_eq_inter_compl (f : ℕ → set α) (n : ℕ) :
  disjointed f n = f n ∩ (⋂ i < n, (f i)ᶜ) :=
disjointed_eq_inf_compl f n

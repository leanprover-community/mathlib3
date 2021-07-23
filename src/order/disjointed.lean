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

variables {α β γ : Type*} {ι : Sort*} [generalized_boolean_algebra α] {a b c : α}

/-- If `f : ℕ → α` is a sequence of sets, then `disjointed f` is
  the sequence formed with each set subtracted from the later ones
  in the sequence, to form a disjoint sequence. -/
def disjointed (f : ℕ → α) : ℕ → α
| 0       := f 0
| (n + 1) := f (n + 1) \ (partial_sups f n)

variables {f : ℕ → α} {n : ℕ}

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

lemma disjoint_disjointed : pairwise (disjoint on disjointed f) :=
begin
  rw symmetric.pairwise_on disjoint.symm, swap, apply_instance,
  rintro m n h,
  cases n,
  { exact (h.not_le (nat.zero_le _)).elim },
  exact disjoint_sdiff_self_right.mono_left ((disjointed_le f m).trans
    (le_partial_sups_of_le f (nat.lt_add_one_iff.1 h))),
end

lemma disjointed_induct {p : α → Prop} (hdiff : ∀ ⦃t i⦄, p t → p (t \ f i)) :
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

lemma monotone.disjointed_eq (hf : monotone f) :
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

/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.finset.lattice
import data.set.pairwise
import order.preorder_hom

/-!
# The monotone sequence of partial supremums of a sequence.

We define `partial_sups : (ℕ → α) → (ℕ →ₘ α)`, so `partial_sups f n = (finset.range (n+1)).sup f`.

## Future work

It might be nice to prove that `partial_sups` forms a `galois_insertion`
with the forgetful map from monotone sequences to sequences.

One might dispute whether this sequence should start at `f 0` or `⊥`.
If we started at `⊥` we wouldn't have this galois insertion.

One could also generalize the domain from `ℕ` to any `preorder`.
-/


variables {α : Type*}

/-- The monotone sequence whose value at `n` is the supremum of the `f m` where `m ≤ n`. -/
def partial_sups [semilattice_sup_bot α] (f : ℕ → α) : ℕ →ₘ α :=
⟨@nat.rec (λ _, α) (f 0) (λ (n : ℕ) (a : α), a ⊔ f (n+1)),
  monotone_of_monotone_nat (λ n, le_sup_left)⟩

@[simp] lemma partial_sups_zero [semilattice_sup_bot α] (f : ℕ → α) : partial_sups f 0 = f 0 := rfl
@[simp] lemma partial_sups_succ [semilattice_sup_bot α] (f : ℕ → α) (n : ℕ) :
  partial_sups f (n+1) = partial_sups f n ⊔ f (n+1) := rfl

lemma le_partial_sups [semilattice_sup_bot α] (f : ℕ → α) {m n : ℕ} (h : m ≤ n) :
  f m ≤ partial_sups f n :=
begin
  induction n with n ih,
  { cases h, apply le_refl, },
  { cases h with h h,
    { exact le_sup_right, },
    { exact (ih h).trans le_sup_left, } },
end

lemma partial_sups_le [semilattice_sup_bot α] (f : ℕ → α) (n : ℕ)
  (a : α) (w : ∀ m, m ≤ n → f m ≤ a) : partial_sups f n ≤ a :=
begin
  induction n with n ih,
  { apply w 0 (le_refl _), },
  { exact sup_le (ih (λ m p, w m (nat.le_succ_of_le p))) (w (n+1) (le_refl _)) }
end

lemma partial_sups_eq [semilattice_sup_bot α] (f : ℕ → α) (n : ℕ) :
  partial_sups f n = (finset.range (n+1)).sup f :=
begin
  induction n with n ih,
  { simp, },
  { dsimp [partial_sups] at ih ⊢,
    rw [finset.range_succ, finset.sup_insert, sup_comm, ih], },
end

-- Note this lemma requires a distributive lattice,
-- so is not useful (or true) in situations such as submodules.
lemma partial_sups_disjoint_of_disjoint [bounded_distrib_lattice α]
  (f : ℕ → α) (w : pairwise (disjoint on f)) {m n : ℕ} (h : m < n) :
  disjoint (partial_sups f m) (f n) :=
begin
  induction m with m ih,
  { exact w 0 n h.ne, },
  { dsimp [partial_sups],
    rw disjoint_sup_left,
    exact ⟨ih (nat.lt_of_succ_lt h), w (m+1) n h.ne⟩ },
end

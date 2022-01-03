/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.finset.lattice
import data.set.pairwise
import order.hom.basic

/-!
# The monotone sequence of partial supremums of a sequence

We define `partial_sups : (ℕ → α) → ℕ →o α` inductively. For `f : ℕ → α`, `partial_sups f` is
the sequence `f 0 `, `f 0 ⊔ f 1`, `f 0 ⊔ f 1 ⊔ f 2`, ... The point of this definition is that
* it doesn't need a `⨆`, as opposed to `⨆ (i ≤ n), f i`.
* it doesn't need a `⊥`, as opposed to `(finset.range (n + 1)).sup f`.
* it avoids needing to prove that `finset.range (n + 1)` is nonempty to use `finset.sup'`.

Equivalence with those definitions is shown by `partial_sups_eq_bsupr`, `partial_sups_eq_sup_range`,
`partial_sups_eq_sup'_range` and respectively.

## Notes

One might dispute whether this sequence should start at `f 0` or `⊥`. We choose the former because :
* Starting at `⊥` requires... having a bottom element.
* `λ f n, (finset.range n).sup f` is already effectively the sequence starting at `⊥`.
* If we started at `⊥` we wouldn't have the Galois insertion. See `partial_sups.gi`.

## TODO

One could generalize `partial_sups` to any locally finite bot preorder domain, in place of `ℕ`.
Necessary for the TODO in the module docstring of `order.disjointed`.
-/

variables {α : Type*}

section semilattice_sup
variables [semilattice_sup α]

/-- The monotone sequence whose value at `n` is the supremum of the `f m` where `m ≤ n`. -/
def partial_sups (f : ℕ → α) : ℕ →o α :=
⟨@nat.rec (λ _, α) (f 0) (λ (n : ℕ) (a : α), a ⊔ f (n + 1)),
  monotone_nat_of_le_succ (λ n, le_sup_left)⟩

@[simp] lemma partial_sups_zero (f : ℕ → α) : partial_sups f 0 = f 0 := rfl
@[simp] lemma partial_sups_succ (f : ℕ → α) (n : ℕ) :
  partial_sups f (n + 1) = partial_sups f n ⊔ f (n + 1) := rfl

lemma le_partial_sups_of_le (f : ℕ → α) {m n : ℕ} (h : m ≤ n) :
  f m ≤ partial_sups f n :=
begin
  induction n with n ih,
  { cases h, apply le_refl, },
  { cases h with h h,
    { exact le_sup_right, },
    { exact (ih h).trans le_sup_left, } },
end

lemma le_partial_sups (f : ℕ → α) :
  f ≤ partial_sups f :=
λ n, le_partial_sups_of_le f le_rfl

lemma partial_sups_le (f : ℕ → α) (n : ℕ)
  (a : α) (w : ∀ m, m ≤ n → f m ≤ a) : partial_sups f n ≤ a :=
begin
  induction n with n ih,
  { apply w 0 le_rfl, },
  { exact sup_le (ih (λ m p, w m (nat.le_succ_of_le p))) (w (n + 1) le_rfl) }
end

lemma monotone.partial_sups_eq {f : ℕ → α} (hf : monotone f) :
  (partial_sups f : ℕ → α) = f :=
begin
  ext n,
  induction n with n ih,
  { refl },
  { rw [partial_sups_succ, ih, sup_eq_right.2 (hf (nat.le_succ _))] }
end

lemma partial_sups_mono : monotone (partial_sups : (ℕ → α) → ℕ →o α) :=
begin
  rintro f g h n,
  induction n with n ih,
  { exact h 0 },
  { exact sup_le_sup ih (h _) }
end

/-- `partial_sups` forms a Galois insertion with the coercion from monotone functions to functions.
-/
def partial_sups.gi : galois_insertion (partial_sups : (ℕ → α) → ℕ →o α) coe_fn :=
{ choice := λ f h, ⟨f, begin
    convert (partial_sups f).monotone,
    exact (le_partial_sups f).antisymm h,
  end⟩,
  gc := λ f g, begin
    refine ⟨(le_partial_sups f).trans, λ h, _⟩,
    convert partial_sups_mono h,
    exact order_hom.ext _ _ g.monotone.partial_sups_eq.symm,
  end,
  le_l_u := λ f, le_partial_sups f,
  choice_eq := λ f h, order_hom.ext _ _ ((le_partial_sups f).antisymm h) }

lemma partial_sups_eq_sup'_range (f : ℕ → α) (n : ℕ) :
  partial_sups f n = (finset.range (n + 1)).sup' ⟨n, finset.self_mem_range_succ n⟩ f :=
begin
  induction n with n ih,
  { simp },
  { dsimp [partial_sups] at ih ⊢,
    simp_rw @finset.range_succ n.succ,
    rw [ih, finset.sup'_insert, sup_comm] }
end

end semilattice_sup

lemma partial_sups_eq_sup_range [semilattice_sup α] [order_bot α] (f : ℕ → α) (n : ℕ) :
  partial_sups f n = (finset.range (n + 1)).sup f :=
begin
  induction n with n ih,
  { simp },
  { dsimp [partial_sups] at ih ⊢,
    rw [finset.range_succ, finset.sup_insert, sup_comm, ih] }
end

/- Note this lemma requires a distributive lattice, so is not useful (or true) in situations such as
submodules. -/
lemma partial_sups_disjoint_of_disjoint [distrib_lattice α] [order_bot α]
  (f : ℕ → α) (h : pairwise (disjoint on f)) {m n : ℕ} (hmn : m < n) :
  disjoint (partial_sups f m) (f n) :=
begin
  induction m with m ih,
  { exact h 0 n hmn.ne, },
  { rw [partial_sups_succ, disjoint_sup_left],
    exact ⟨ih (nat.lt_of_succ_lt hmn), h (m + 1) n hmn.ne⟩ }
end

section complete_lattice
variables [complete_lattice α]

lemma partial_sups_eq_bsupr (f : ℕ → α) (n : ℕ) :
  partial_sups f n = ⨆ (i ≤ n), f i :=
begin
  rw [partial_sups_eq_sup_range, finset.sup_eq_supr],
  congr,
  ext a,
  exact supr_congr_Prop (by rw [finset.mem_range, nat.lt_succ_iff]) (λ _, rfl),
end

@[simp] lemma supr_partial_sups_eq (f : ℕ → α) :
  (⨆ n, partial_sups f n) = ⨆ n, f n :=
begin
  refine (supr_le $ λ n, _).antisymm (supr_le_supr $ le_partial_sups f),
  rw partial_sups_eq_bsupr,
  exact bsupr_le_supr _ _,
end

lemma supr_le_supr_of_partial_sups_le_partial_sups {f g : ℕ → α}
  (h : partial_sups f ≤ partial_sups g) :
  (⨆ n, f n) ≤ ⨆ n, g n :=
begin
  rw [←supr_partial_sups_eq f, ←supr_partial_sups_eq g],
  exact supr_le_supr h,
end

lemma supr_eq_supr_of_partial_sups_eq_partial_sups {f g : ℕ → α}
  (h : partial_sups f = partial_sups g) :
  (⨆ n, f n) = ⨆ n, g n :=
by simp_rw [←supr_partial_sups_eq f, ←supr_partial_sups_eq g, h]

end complete_lattice

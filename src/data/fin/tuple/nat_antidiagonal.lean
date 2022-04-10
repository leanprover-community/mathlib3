/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import data.fin.vec_notation
import algebra.big_operators.basic
import data.list.nat_antidiagonal
import data.multiset.nat_antidiagonal
import data.finset.nat_antidiagonal
import logic.equiv.fin

/-!
# Collections of tuples of naturals with the same sum

This file generalizes `list.nat.antidiagonal n`, `multiset.nat.antidiagonal n`, and
`finset.nat.antidiagonal n` from the pair of elements `x : ℕ × ℕ` such that `n = x.1 + x.2`, to
the sequence of elements `x : fin k → ℕ` such that `n = ∑ i, x i`.

## Main definitions

* `list.nat.antidiagonal_tuple`
* `multiset.nat.antidiagonal_tuple`
* `finset.nat.antidiagonal_tuple`

## Main results

* `antidiagonal_tuple 2 n` is analogous to `antidiagonal n`:

  * `list.nat.antidiagonal_tuple_two`
  * `multiset.nat.antidiagonal_tuple_two`
  * `finset.nat.antidiagonal_tuple_two`

## Implementation notes

While we could implement this by filtering `(fintype.pi_finset $ λ _, range (n + 1))` or similar,
this implementation would be much slower.
-/

open_locale big_operators

/-! ### Lists -/

namespace list.nat

/-- `list.antidiagonal_tuple k n` is a list of all `k`-tuples which sum to `n`.

This list contains no duplicates, and is sorted lexicographically, starting with `![0, ..., n]`
and ending with `![n, ..., 0]`.

```
#eval antidiagonal_tuple 3 2
-- [![0, 0, 2], ![0, 1, 1], ![0, 2, 0], ![1, 0, 1], ![1, 1, 0], ![2, 0, 0]]
```
-/
def antidiagonal_tuple : Π k, ℕ → list (fin k → ℕ)
| 0 0 := [![]]
| 0 (n + 1) := []
| (k + 1) n := (list.nat.antidiagonal n).bind $ λ ni,
  (antidiagonal_tuple k ni.2).map $ λ x, fin.cons (ni.1) x

@[simp] lemma antidiagonal_tuple_zero_zero : antidiagonal_tuple 0 0 = [![]] := rfl
@[simp] lemma antidiagonal_tuple_zero_succ (n : ℕ) : antidiagonal_tuple 0 n.succ = [] := rfl

lemma mem_antidiagonal_tuple {n : ℕ} {k : ℕ} {x : fin k → ℕ} :
  x ∈ antidiagonal_tuple k n ↔ ∑ i, x i = n :=
begin
  induction k with k ih generalizing n,
  { cases n,
    { simp },
    { simp [eq_comm] }, },
  { refine fin.cons_induction (λ x₀ x, _) x,
    have : (0 : fin k.succ) ∉ finset.image fin.succ (finset.univ : finset (fin k)) := by simp,
    simp_rw [antidiagonal_tuple, list.mem_bind, list.mem_map, list.nat.mem_antidiagonal,
      fin.univ_succ, finset.sum_insert this, fin.cons_zero,
      finset.sum_image (λ x hx y hy h, fin.succ_injective _ h), fin.cons_succ, fin.cons_eq_cons,
      exists_eq_right_right, ih, prod.exists],
    split,
    { rintros ⟨a, b, rfl, rfl, rfl⟩, refl },
    { rintro rfl, exact ⟨_, _, rfl, rfl, rfl⟩, } },
end

/-- The antidiagonal of `n` does not contain duplicate entries. -/
lemma nodup_antidiagonal_tuple (k n : ℕ) : list.nodup (antidiagonal_tuple k n) :=
begin
  induction k with k ih generalizing n,
  { cases n,
    { simp },
    { simp [eq_comm] }, },
  simp_rw [antidiagonal_tuple, list.nodup_bind],
  split,
  { intros i hi,
    exact (ih i.snd).map (fin.cons_right_injective (i.fst : (λ _, ℕ) 0)), },
  induction n,
  { exact list.pairwise_singleton _ _ },
  { rw list.nat.antidiagonal_succ,
    refine list.pairwise.cons (λ a ha x hx₁ hx₂, _) (n_ih.map _ (λ a b h x hx₁ hx₂, _)),
    { rw list.mem_map at hx₁ hx₂ ha,
      obtain ⟨⟨a, -, rfl⟩, ⟨x₁, -, rfl⟩, ⟨x₂, -, h⟩⟩ := ⟨ha, hx₁, hx₂⟩,
      rw fin.cons_eq_cons at h,
      injection h.1, },
    { rw list.mem_map at hx₁ hx₂,
      obtain ⟨⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, h₁₂⟩⟩ := ⟨hx₁, hx₂⟩,
      dsimp at h₁₂,
      rw [fin.cons_eq_cons, nat.succ_inj'] at h₁₂,
      obtain ⟨h₁₂, rfl⟩ := h₁₂,
      rw h₁₂ at h,
      exact h (list.mem_map_of_mem _ hx₁) (list.mem_map_of_mem _ hx₂) }, },
end

@[simp] lemma antidiagonal_tuple_one (n : ℕ) : antidiagonal_tuple 1 n = [![n]] :=
begin
  simp_rw [antidiagonal_tuple, antidiagonal, list.range_succ, list.map_append, list.map_singleton,
    tsub_self, list.bind_append, list.bind_singleton, antidiagonal_tuple_zero_zero,
    list.map_singleton, list.map_bind],
  conv_rhs { rw ← list.nil_append [![n]]},
  congr' 1,
  simp_rw [list.bind_eq_nil, list.mem_range, list.map_eq_nil],
  intros x hx,
  obtain ⟨m, rfl⟩ := nat.exists_eq_add_of_lt hx,
  rw [add_assoc, add_tsub_cancel_left, antidiagonal_tuple_zero_succ],
end

lemma antidiagonal_tuple_two (n : ℕ) :
  antidiagonal_tuple 2 n = (antidiagonal n).map (λ i, ![i.1, i.2]) :=
begin
  rw antidiagonal_tuple,
  simp_rw [antidiagonal_tuple_one, list.map_singleton],
  rw [list.map_eq_bind],
  refl,
end

end list.nat

/-! ### Multisets -/
namespace multiset.nat

/-- `multiset.antidiagonal_tuple k n` is a multiset of `k`-tuples summing to `n` -/
def antidiagonal_tuple (k n : ℕ) : multiset (fin k → ℕ) :=
list.nat.antidiagonal_tuple k n

@[simp] lemma antidiagonal_tuple_zero_zero : antidiagonal_tuple 0 0 = { ![]} := rfl
@[simp] lemma antidiagonal_tuple_zero_succ (n : ℕ) : antidiagonal_tuple 0 n.succ = 0 := rfl

lemma mem_antidiagonal_tuple {n : ℕ} {k : ℕ} {x : fin k → ℕ} :
  x ∈ antidiagonal_tuple k n ↔ ∑ i, x i = n :=
list.nat.mem_antidiagonal_tuple

lemma nodup_antidiagonal_tuple (k n : ℕ) : (antidiagonal_tuple k n).nodup :=
list.nat.nodup_antidiagonal_tuple _ _

@[simp] lemma antidiagonal_tuple_one (n : ℕ) : antidiagonal_tuple 1 n = { ![n]} :=
congr_arg _ (list.nat.antidiagonal_tuple_one n)

lemma antidiagonal_tuple_two (n : ℕ) :
  antidiagonal_tuple 2 n = (antidiagonal n).map (λ i, ![i.1, i.2]) :=
congr_arg _ (list.nat.antidiagonal_tuple_two n)

end multiset.nat

/-! ### Finsets -/
namespace finset.nat

/-- `finset.antidiagonal_tuple k n` is a finset of `k`-tuples summing to `n` -/
def antidiagonal_tuple (k n : ℕ) : finset (fin k → ℕ) :=
⟨multiset.nat.antidiagonal_tuple k n, multiset.nat.nodup_antidiagonal_tuple k n⟩

@[simp] lemma antidiagonal_tuple_zero_zero : antidiagonal_tuple 0 0 = { ![]} := rfl
@[simp] lemma antidiagonal_tuple_zero_succ (n : ℕ) : antidiagonal_tuple 0 n.succ = ∅ := rfl

lemma mem_antidiagonal_tuple {n : ℕ} {k : ℕ} {x : fin k → ℕ} :
  x ∈ antidiagonal_tuple k n ↔ ∑ i, x i = n :=
list.nat.mem_antidiagonal_tuple

@[simp] lemma antidiagonal_tuple_one (n : ℕ) : antidiagonal_tuple 1 n = { ![n]} :=
finset.eq_of_veq (multiset.nat.antidiagonal_tuple_one n)

lemma antidiagonal_tuple_two (n : ℕ) :
  antidiagonal_tuple 2 n = (antidiagonal n).map (pi_fin_two_equiv (λ _, ℕ)).symm.to_embedding :=
finset.eq_of_veq (multiset.nat.antidiagonal_tuple_two n)

section equiv_prod

/-- The disjoint union of antidiagonal tuples `Σ n, antidiagonal_tuple k n` is equivalent to the
`k`-tuple `fin k → ℕ`. This is such an equivalence, obtained by mapping `(n, x)` to `x`.

This is the tuple version of `finset.nat.sigma_antidiagonal_equiv_prod`. -/
@[simps] def sigma_antidiagonal_tuple_equiv_tuple (k : ℕ) :
  (Σ n, antidiagonal_tuple k n) ≃ (fin k → ℕ) :=
{ to_fun := λ x, x.2,
  inv_fun := λ x, ⟨∑ i, x i, x, mem_antidiagonal_tuple.mpr rfl⟩,
  left_inv := λ ⟨n, t, h⟩, sigma.subtype_ext (mem_antidiagonal_tuple.mp h) rfl,
  right_inv := λ x, rfl }

end equiv_prod

end finset.nat

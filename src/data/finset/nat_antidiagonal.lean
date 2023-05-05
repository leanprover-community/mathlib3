/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import data.finset.card
import data.multiset.nat_antidiagonal

/-!
# Antidiagonals in ℕ × ℕ as finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the antidiagonals of ℕ × ℕ as finsets: the `n`-th antidiagonal is the finset of
pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

This refines files `data.list.nat_antidiagonal` and `data.multiset.nat_antidiagonal`.
-/

namespace finset
namespace nat

/-- The antidiagonal of a natural number `n` is
    the finset of pairs `(i, j)` such that `i + j = n`. -/
def antidiagonal (n : ℕ) : finset (ℕ × ℕ) :=
⟨multiset.nat.antidiagonal n, multiset.nat.nodup_antidiagonal n⟩

/-- A pair (i, j) is contained in the antidiagonal of `n` if and only if `i + j = n`. -/
@[simp] lemma mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} :
  x ∈ antidiagonal n ↔ x.1 + x.2 = n :=
by rw [antidiagonal, mem_def, multiset.nat.mem_antidiagonal]

/-- The cardinality of the antidiagonal of `n` is `n + 1`. -/
@[simp] lemma card_antidiagonal (n : ℕ) : (antidiagonal n).card = n+1 :=
by simp [antidiagonal]

/-- The antidiagonal of `0` is the list `[(0, 0)]` -/
@[simp] lemma antidiagonal_zero : antidiagonal 0 = {(0, 0)} :=
rfl

lemma antidiagonal_succ (n : ℕ) :
  antidiagonal (n + 1) = cons (0, n + 1) ((antidiagonal n).map
  (function.embedding.prod_map ⟨nat.succ, nat.succ_injective⟩ (function.embedding.refl _)))
  (by simp) :=
begin
  apply eq_of_veq,
  rw [cons_val, map_val],
  { apply multiset.nat.antidiagonal_succ },
end

lemma antidiagonal_succ' (n : ℕ) :
  antidiagonal (n + 1) = cons (n + 1, 0) ((antidiagonal n).map
  (function.embedding.prod_map (function.embedding.refl _) ⟨nat.succ, nat.succ_injective⟩))
  (by simp) :=
begin
  apply eq_of_veq,
  rw [cons_val, map_val],
  exact multiset.nat.antidiagonal_succ',
end

lemma antidiagonal_succ_succ' {n : ℕ} :
  antidiagonal (n + 2) =
    cons (0, n + 2)
      (cons (n + 2, 0) ((antidiagonal n).map
        (function.embedding.prod_map ⟨nat.succ, nat.succ_injective⟩ ⟨nat.succ, nat.succ_injective⟩))
        $ by simp) (by simp) :=
by { simp_rw [antidiagonal_succ (n + 1), antidiagonal_succ', finset.map_cons, map_map], refl }

lemma map_swap_antidiagonal {n : ℕ} :
  (antidiagonal n).map ⟨prod.swap, prod.swap_right_inverse.injective⟩ = antidiagonal n :=
eq_of_veq $ by simp [antidiagonal, multiset.nat.map_swap_antidiagonal]

/-- A point in the antidiagonal is determined by its first co-ordinate. -/
lemma antidiagonal_congr {n : ℕ} {p q : ℕ × ℕ} (hp : p ∈ antidiagonal n)
  (hq : q ∈ antidiagonal n) : p = q ↔ p.fst = q.fst :=
begin
  refine ⟨congr_arg prod.fst, (λ h, prod.ext h ((add_right_inj q.fst).mp _))⟩,
  rw mem_antidiagonal at hp hq,
  rw [hq, ← h, hp],
end

lemma antidiagonal.fst_le {n : ℕ} {kl : ℕ × ℕ} (hlk : kl ∈ antidiagonal n) :
  kl.1 ≤ n :=
begin
  rw le_iff_exists_add,
  use kl.2,
  rwa [mem_antidiagonal, eq_comm] at hlk
end

lemma antidiagonal.snd_le {n : ℕ} {kl : ℕ × ℕ} (hlk : kl ∈ antidiagonal n) :
  kl.2 ≤ n :=
begin
  rw le_iff_exists_add,
  use kl.1,
  rwa [mem_antidiagonal, eq_comm, add_comm] at hlk
end

lemma filter_fst_eq_antidiagonal (n m : ℕ) :
  filter (λ x : ℕ × ℕ, x.fst = m) (antidiagonal n) = if m ≤ n then {(m, n - m)} else ∅ :=
begin
  ext ⟨x, y⟩,
  simp only [mem_filter, nat.mem_antidiagonal],
  split_ifs with h h,
  { simp [and_comm, eq_tsub_iff_add_eq_of_le h, add_comm] {contextual := tt} },
  { rw not_le at h,
    simp only [not_mem_empty, iff_false, not_and],
    exact λ hn, ne_of_lt (lt_of_le_of_lt (le_self_add.trans hn.le) h) }
end

lemma filter_snd_eq_antidiagonal (n m : ℕ) :
  filter (λ x : ℕ × ℕ, x.snd = m) (antidiagonal n) = if m ≤ n then {(n - m, m)} else ∅ :=
begin
  have : (λ (x : ℕ × ℕ), x.snd = m) ∘ prod.swap = (λ (x : ℕ × ℕ), x.fst = m),
  { ext, simp },
  rw ←map_swap_antidiagonal,
  simp [filter_map, this, filter_fst_eq_antidiagonal, apply_ite (finset.map _)]
end

section equiv_prod

/-- The disjoint union of antidiagonals `Σ (n : ℕ), antidiagonal n` is equivalent to the product
    `ℕ × ℕ`. This is such an equivalence, obtained by mapping `(n, (k, l))` to `(k, l)`. -/
@[simps] def sigma_antidiagonal_equiv_prod : (Σ (n : ℕ), antidiagonal n) ≃ ℕ × ℕ :=
{ to_fun := λ x, x.2,
  inv_fun := λ x, ⟨x.1 + x.2, x, mem_antidiagonal.mpr rfl⟩,
  left_inv :=
    begin
      rintros ⟨n, ⟨k, l⟩, h⟩,
      rw mem_antidiagonal at h,
      exact sigma.subtype_ext h rfl,
    end,
  right_inv := λ x, rfl }

end equiv_prod

end nat

end finset

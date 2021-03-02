/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import data.finset.basic
import data.multiset.nat_antidiagonal

/-!
# The "antidiagonal" {(0,n), (1,n-1), ..., (n,0)} as a finset.
-/

namespace finset

namespace nat

/-- The antidiagonal of a natural number `n` is
    the finset of pairs `(i,j)` such that `i+j = n`. -/
def antidiagonal (n : ℕ) : finset (ℕ × ℕ) :=
⟨multiset.nat.antidiagonal n, multiset.nat.nodup_antidiagonal n⟩

/-- A pair (i,j) is contained in the antidiagonal of `n` if and only if `i+j=n`. -/
@[simp] lemma mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} :
  x ∈ antidiagonal n ↔ x.1 + x.2 = n :=
by rw [antidiagonal, mem_def, multiset.nat.mem_antidiagonal]

/-- The cardinality of the antidiagonal of `n` is `n+1`. -/
@[simp] lemma card_antidiagonal (n : ℕ) : (antidiagonal n).card = n+1 :=
by simp [antidiagonal]

/-- The antidiagonal of `0` is the list `[(0,0)]` -/
@[simp] lemma antidiagonal_zero : antidiagonal 0 = {(0, 0)} :=
rfl

lemma antidiagonal_succ {n : ℕ} :
  antidiagonal (n + 1) = insert (0, n + 1) ((antidiagonal n).map
  (function.embedding.prod_map ⟨nat.succ, nat.succ_injective⟩ (function.embedding.refl _))) :=
begin
  apply eq_of_veq,
  rw [insert_val_of_not_mem, map_val],
  {apply multiset.nat.antidiagonal_succ},
  { intro con, rcases mem_map.1 con with ⟨⟨a,b⟩, ⟨h1, h2⟩⟩,
    simp only [prod.mk.inj_iff, function.embedding.coe_prod_map, prod.map_mk] at h2,
    apply nat.succ_ne_zero a h2.1, }
end

lemma map_swap_antidiagonal {n : ℕ} :
  (antidiagonal n).map ⟨prod.swap, prod.swap_right_inverse.injective⟩ = antidiagonal n :=
begin
  ext,
  simp only [exists_prop, mem_map, mem_antidiagonal, prod.exists],
  rw add_comm,
  split,
  { rintro ⟨b, c, ⟨rfl, rfl⟩⟩,
    simp },
  { rintro rfl,
    use [a.snd, a.fst],
    simp }
end

/-- A point in the antidiagonal is determined by its first co-ordinate. -/
lemma antidiagonal_congr {n : ℕ} {p q : ℕ × ℕ} (hp : p ∈ nat.antidiagonal n)
  (hq : q ∈ nat.antidiagonal n) : p = q ↔ p.fst = q.fst :=
begin
  refine ⟨congr_arg prod.fst, _⟩,
  intros h,
  refine prod.ext h _,
  rw nat.mem_antidiagonal at hp hq,
  rw [← hq, h] at hp,
  exact (add_right_inj q.fst).mp hp
end

end nat

end finset

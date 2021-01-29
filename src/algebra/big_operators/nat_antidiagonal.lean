/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import data.finset.nat_antidiagonal
import algebra.big_operators.basic

/-!
# Big operators for `nat_antidiagonal`

This file contains theorems relevant to big operators over `finset.nat.antidiagonal`.
-/

open_locale big_operators

variables {M N : Type*} [comm_monoid M] [add_comm_monoid N]

namespace finset
namespace nat

lemma prod_antidiagonal_succ {n : ℕ} {f : ℕ × ℕ → M} :
  ∏ p in antidiagonal (n + 1), f p = f (0, n + 1) * ∏ p in antidiagonal n, f (p.1 + 1, p.2) :=
begin
  rw [antidiagonal_succ, prod_insert, prod_map], refl,
  intro con, rcases mem_map.1 con with ⟨⟨a,b⟩, ⟨h1, h2⟩⟩,
  simp only [prod.mk.inj_iff, function.embedding.coe_prod_map, prod.map_mk] at h2,
  apply nat.succ_ne_zero a h2.1,
end

lemma sum_antidiagonal_succ {n : ℕ} {f : ℕ × ℕ → N} :
  ∑ p in antidiagonal (n + 1), f p = f (0, n + 1) + ∑ p in antidiagonal n, f (p.1 + 1, p.2) :=
@prod_antidiagonal_succ (multiplicative N) _ _ _

@[to_additive]
lemma prod_antidiagonal_swap {n : ℕ} {f : ℕ × ℕ → M} :
  ∏ p in antidiagonal n, f p.swap = ∏ p in antidiagonal n, f p :=
by { nth_rewrite 1 ← map_swap_antidiagonal, rw [prod_map], refl }

lemma prod_antidiagonal_succ' {n : ℕ} {f : ℕ × ℕ → M} :
  ∏ p in antidiagonal (n + 1), f p = f (n + 1, 0) * ∏ p in antidiagonal n, f (p.1, p.2 + 1) :=
begin
  rw [← prod_antidiagonal_swap, prod_antidiagonal_succ, ← prod_antidiagonal_swap],
  refl
end

lemma sum_antidiagonal_succ' {n : ℕ} {f : ℕ × ℕ → N} :
  ∑ p in antidiagonal (n + 1), f p = f (n + 1, 0) + ∑ p in antidiagonal n, f (p.1, p.2 + 1) :=
@prod_antidiagonal_succ' (multiplicative N) _ _ _

@[to_additive]
lemma prod_antidiagonal_subst {n : ℕ} {f : ℕ × ℕ → ℕ → M} :
  ∏ p in antidiagonal n, f p n = ∏ p in antidiagonal n, f p (p.1 + p.2) :=
prod_congr rfl $ λ p hp, by rw [nat.mem_antidiagonal.1 hp]

@[to_additive]
lemma prod_antidiagonal_eq_prod_range_succ {M : Type*} [comm_monoid M] (f : ℕ → ℕ → M) (n : ℕ) :
  ∏ ij in finset.nat.antidiagonal n, f ij.1 ij.2 = ∏ k in range n.succ, f k (n - k) :=
begin
  convert prod_map _ ⟨λ i, (i, n - i), λ x y h, (prod.mk.inj h).1⟩ _,
  refl,
end

@[to_additive]
lemma prod_range_succ_eq_prod_antidiagonal {M : Type*} [comm_monoid M]
  (f : ℕ → ℕ → M) (n : ℕ) : ∏ x in range n.succ, f x (n - x) =
    ∏ k in finset.nat.antidiagonal n, f k.1 k.2 :=
begin
  refine finset.prod_bij'
  (λ a _, (a, n - a) : Π (a : ℕ), a ∈ finset.range n.succ → ℕ × ℕ)
  _ (by simp)
  (λ (ij : ℕ × ℕ) _, ij.1)
  _ (by simp) _,
  { intros a ha, simp [nat.add_sub_cancel' (mem_range_succ_iff.1 ha)], },
  { intros _ ha, simp [mem_range_succ_iff.2 (nat.le.intro (nat.mem_antidiagonal.1 ha))], },
  { rintro ⟨i, j⟩ ha, ext, refl, rw ← (nat.mem_antidiagonal.1 ha),
  exact nat.add_sub_cancel_left _ _ },
end

@[to_additive]
lemma prod_antidiagonal {M : Type*} [comm_monoid M]
  (n : ℕ) (f : ℕ × ℕ → M) :
  ∏ (p : ℕ × ℕ) in finset.nat.antidiagonal n, f p =
  ∏ (i : ℕ) in finset.range (n.succ), f (i,(n - i)) :=
begin
  conv_rhs {apply_congr, skip, rw <-function.curry_apply f x (n-x), },
  rw [prod_range_succ_eq_prod_antidiagonal], simp only [prod.mk.eta, function.curry_apply],
end

end nat

end finset

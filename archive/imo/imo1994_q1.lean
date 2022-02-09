/-
Copyright (c) 2021 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import algebra.big_operators.basic
import algebra.big_operators.order
import data.fintype.card
import data.finset.sort
import data.fin.interval
import tactic.linarith
import tactic.by_contra

/-!
# IMO 1994 Q1

Let `m` and `n` be two positive integers.
Let `a₁, a₂, ..., aₘ` be `m` different numbers from the set `{1, 2, ..., n}`
such that for any two indices `i` and `j` with `1 ≤ i ≤ j ≤ m` and `aᵢ + aⱼ ≤ n`,
there exists an index `k` such that `aᵢ + aⱼ = aₖ`.
Show that `(a₁+a₂+...+aₘ)/m ≥ (n+1)/2`

# Sketch of solution

We can order the numbers so that `a₁ ≤ a₂ ≤ ... ≤ aₘ`.
The key idea is to pair the numbers in the sum and show that `aᵢ + aₘ₊₁₋ᵢ ≥ n+1`.
Indeed, if we had `aᵢ + aₘ₊₁₋ᵢ ≤ n`, then `a₁ + aₘ₊₁₋ᵢ, a₂ + aₘ₊₁₋ᵢ, ..., aᵢ + aₘ₊₁₋ᵢ`
would be `m` elements of the set of `aᵢ`'s all larger than `aₘ₊₁₋ᵢ`, which is impossible.
-/

open_locale big_operators

open finset

lemma tedious (m : ℕ) (k : fin (m+1)) : m - (m + (m + 1 - ↑k)) % (m + 1) = ↑k  :=
begin
  cases k with k hk,
  rw [nat.lt_succ_iff,le_iff_exists_add] at hk,
  rcases hk with ⟨c, rfl⟩,
  have : k + c + (k + c + 1 - k) = c + (k + c + 1),
  { simp only [add_assoc, add_tsub_cancel_left], ring_nf, },
  rw [fin.coe_mk, this, nat.add_mod_right, nat.mod_eq_of_lt, nat.add_sub_cancel],
  linarith
end

theorem imo1994_q1 (n : ℕ) (m : ℕ) (A : finset ℕ) (hm : A.card = m + 1)
  (hrange : ∀ a ∈ A, 0 < a ∧ a ≤ n) (hadd : ∀ (a b ∈ A), a + b ≤ n → a + b ∈ A) :
  (m+1)*(n+1) ≤ 2*(∑ x in A, x) :=
begin
  set a := order_emb_of_fin A hm,  -- We sort the elements of `A`
  have ha : ∀ i, a i ∈ A := λ i, order_emb_of_fin_mem A hm i,
  set rev := equiv.sub_left (fin.last m), -- `i ↦ m-i`

  -- We reindex the sum by fin (m+1)
  have : ∑ x in A, x = ∑ i : fin (m+1), a i,
  { convert sum_image (λ x hx y hy, (order_embedding.eq_iff_eq a).1),
    rw ←coe_inj, simp },
  rw this, clear this,

  -- The main proof is a simple calculation by rearranging one of the two sums
  suffices hpair : ∀ k ∈ univ, a k + a (rev k) ≥ n+1,
  calc 2 * ∑ i : fin (m+1), a i
      = ∑ i : fin (m+1), a i + ∑ i : fin (m+1), a i       : two_mul _
  ... = ∑ i : fin (m+1), a i + ∑ i : fin (m+1), a (rev i) : by rw equiv.sum_comp rev
  ... = ∑ i : fin (m+1), (a i + a (rev i))                : sum_add_distrib.symm
  ... ≥ ∑ i : fin (m+1), (n+1)                            : sum_le_sum hpair
  ... = (m+1) * (n+1)                                     : by simp,

  -- It remains to prove the key inequality, by contradiction
  rintros k -,
  by_contra' h : a k + a (rev k) < n + 1,

  -- We exhibit `k+1` elements of `A` greater than `a (rev k)`
  set f : fin (m+1) ↪ ℕ := ⟨λ i, a i + a (rev k),
  begin
    apply injective_of_le_imp_le,
    intros i j hij,
    rwa [add_le_add_iff_right, a.map_rel_iff] at hij,
  end⟩,

  -- Proof that the `f i` are greater than `a (rev k)` for `i ≤ k`
  have hf : map f (Icc 0 k) ⊆ map a.to_embedding (Ioc (rev k) (fin.last m)),
  { intros x hx,
    simp at h hx ⊢,
    rcases hx with ⟨i, ⟨hi, rfl⟩⟩,
    have h1 : a i + a (fin.last m - k) ≤ n,
    { linarith only [h, a.monotone hi.2] },
    have h2 : a i + a (fin.last m - k) ∈ A := hadd _ (ha _) _ (ha _) h1,
    rw [←mem_coe, ←range_order_emb_of_fin A hm, set.mem_range] at h2,
    cases h2 with j hj,
    use j,
    refine ⟨⟨_, fin.le_last j⟩, hj⟩,
    rw [← a.strict_mono.lt_iff_lt, hj],
    simpa using (hrange (a i) (ha i)).1 },

  -- A set of size `k+1` embed in one of size `k`, which yields a contradiction
  have ineq := card_le_of_subset hf,
  simp [fin.coe_sub, tedious] at ineq,
  contradiction ,
end

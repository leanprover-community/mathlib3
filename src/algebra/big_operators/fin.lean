/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import algebra.big_operators.basic
import data.fintype.fin
import data.fintype.card
/-!
# Big operators and `fin`

Some results about products and sums over the type `fin`.
-/

open_locale big_operators

open finset

namespace fin

@[to_additive]
lemma prod_filter_zero_lt {M : Type*} [comm_monoid M] {n : ℕ} {v : fin n.succ → M} :
  ∏ i in univ.filter (λ (i : fin n.succ), 0 < i), v i = ∏ (j : fin n), v j.succ :=
by rw [univ_filter_zero_lt, finset.prod_map, rel_embedding.coe_fn_to_embedding, coe_succ_embedding]

@[to_additive]
lemma prod_filter_succ_lt {M : Type*} [comm_monoid M] {n : ℕ} (j : fin n) (v : fin n.succ → M) :
  ∏ i in univ.filter (λ i, j.succ < i), v i =
    ∏ j in univ.filter (λ i, j < i), v j.succ :=
by rw [univ_filter_succ_lt, finset.prod_map, rel_embedding.coe_fn_to_embedding, coe_succ_embedding]

@[to_additive]
lemma prod_congr {M : Type*} [comm_monoid M] {a b : ℕ} (f : fin b → M) (h : a = b) :
  ∏ (i : fin a), f (fin.cast h i) = ∏ (i : fin b), f i :=
by { subst h, congr, ext, congr, ext, rw fin.coe_cast, }

@[to_additive]
lemma prod_split {M : Type*} [comm_monoid M] {a b : ℕ} (f : fin (a+b) → M) :
  ∏ (i : fin (a+b)), f i =
  (∏ (i : fin a), f (fin.cast_le le_self_add i)) * ∏ (i : fin b), f (fin.nat_add a i) :=
begin
  revert f a,
  induction b with b hb,
  { intros a f,
    simp only [prod_univ_zero, mul_one],
    congr,
    ext i,
    congr,
    ext,
    rw fin.coe_cast_le, },
  { intros a f,
    have eq : (a+1)+b=(a+b).succ := by simpa only [add_assoc, add_comm 1],
    rw [fin.prod_univ_succ, ← mul_assoc, ← fin.prod_congr f eq,
      hb (λ (i : fin((a+1)+b)), f (fin.cast eq i))],
    congr,
    { rw fin.prod_univ_cast_succ,
      congr, },
    { ext,
      simp only,
      congr,
      ext,
      simp only [fin.coe_cast, fin.coe_nat_add, fin.coe_succ, add_assoc, add_comm 1], }, }
end

@[to_additive]
lemma prod_trunc {M : Type*} [comm_monoid M] {n a b : ℕ}
  (h : n=a+b) (f : fin (n) → M)
  (hf : ∀ (j : fin b), f (fin.cast h.symm (fin.nat_add a j)) = 1) :
  ∏ (i : fin (n)), f i =
  ∏ (i : fin (a)), f (fin.cast_le (nat.le.intro (h.symm)) i) :=
begin
  rw [← fin.prod_congr f h.symm, fin.prod_split, fintype.prod_eq_one _ hf, mul_one],
  congr,
end

end fin

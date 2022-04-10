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
lemma prod_congr' {M : Type*} [comm_monoid M] {a b : ℕ} (f : fin b → M) (h : a = b) :
  ∏ (i : fin a), f (cast h i) = ∏ (i : fin b), f i :=
by { subst h, congr, ext, congr, ext, rw coe_cast, }

@[to_additive]
lemma prod_univ_add {M : Type*} [comm_monoid M] {a b : ℕ} (f : fin (a+b) → M) :
  ∏ (i : fin (a+b)), f i =
  (∏ (i : fin a), f (cast_add b i)) * ∏ (i : fin b), f (nat_add a i) :=
begin
  revert f a,
  induction b with b hb,
  { intros a f,
    simp only [prod_univ_zero, mul_one],
    congr,
    ext i,
    congr,
    ext,
    refl, },
  { intros a f,
    have eq : (a+1)+b=(a+b).succ := by simpa only [add_assoc, add_comm 1],
    rw [prod_univ_succ, ← mul_assoc, ← prod_congr' f eq,
      hb (λ (i : fin((a+1)+b)), f (cast eq i))],
    congr,
    { rw prod_univ_cast_succ,
      congr, },
    { ext,
      simp only,
      congr,
      ext,
      simp only [coe_cast, coe_nat_add, coe_succ, add_assoc, add_comm 1], }, }
end

@[to_additive]
lemma prod_trunc {M : Type*} [comm_monoid M] {a b : ℕ} (f : fin (a+b) → M)
  (hf : ∀ (j : fin b), f (nat_add a j) = 1) :
  ∏ (i : fin (a+b)), f i =
  ∏ (i : fin a), f (cast_le (nat.le.intro rfl) i) :=
by simpa only [prod_univ_add, fintype.prod_eq_one _ hf, mul_one]

end fin

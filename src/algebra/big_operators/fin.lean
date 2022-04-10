/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import algebra.big_operators.basic
import data.fintype.fin
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

end fin

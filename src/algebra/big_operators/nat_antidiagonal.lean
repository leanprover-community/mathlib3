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

variables {α : Type*} [add_comm_monoid α]

namespace finset
namespace nat

lemma sum_antidiagonal_succ {n : ℕ} {f : ℕ × ℕ → α} :
  (antidiagonal (n + 1)).sum f = f (0, n + 1) + ((antidiagonal n).map
  (function.embedding.prod_map ⟨nat.succ, nat.succ_injective⟩ (function.embedding.refl _))).sum f :=
begin
  rw [antidiagonal_succ, sum_insert],
  intro con, rcases mem_map.1 con with ⟨⟨a,b⟩, ⟨h1, h2⟩⟩,
  simp only [prod.mk.inj_iff, function.embedding.coe_prod_map, prod.map_mk] at h2,
  apply nat.succ_ne_zero a h2.1,
end

end nat
end finset

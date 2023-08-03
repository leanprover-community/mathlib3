/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import data.set.pointwise.basic
import data.list.of_fn

/-!
# Pointwise operations with lists of sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves some lemmas about pointwise algebraic operations with lists of sets.
-/

namespace set

variables {F α β γ : Type*}
variables [monoid α] {s t : set α} {a : α} {m n : ℕ}

open_locale pointwise

@[to_additive] lemma mem_prod_list_of_fn {a : α} {s : fin n → set α} :
  a ∈ (list.of_fn s).prod ↔ ∃ f : (Π i : fin n, s i), (list.of_fn (λ i, (f i : α))).prod = a :=
begin
  induction n with n ih generalizing a,
  { simp_rw [list.of_fn_zero, list.prod_nil, fin.exists_fin_zero_pi, eq_comm, set.mem_one] },
  { simp_rw [list.of_fn_succ, list.prod_cons, fin.exists_fin_succ_pi, fin.cons_zero, fin.cons_succ,
      mem_mul, @ih, exists_and_distrib_left, exists_exists_eq_and, set_coe.exists, subtype.coe_mk,
      exists_prop] }
end

@[to_additive] lemma mem_list_prod {l : list (set α)} {a : α} :
  a ∈ l.prod ↔ ∃ l' : list (Σ s : set α, ↥s),
    list.prod (l'.map (λ x, (sigma.snd x : α))) = a ∧ l'.map sigma.fst = l :=
begin
  induction l using list.of_fn_rec with n f,
  simp_rw [list.exists_iff_exists_tuple, list.map_of_fn, list.of_fn_inj', and.left_comm,
    exists_and_distrib_left, exists_eq_left, heq_iff_eq, function.comp, mem_prod_list_of_fn],
  split,
  { rintros ⟨fi, rfl⟩,  exact ⟨λ i, ⟨_, fi i⟩, rfl, rfl⟩, },
  { rintros ⟨fi, rfl, rfl⟩, exact ⟨λ i, _, rfl⟩, },
end

@[to_additive] lemma mem_pow {a : α} {n : ℕ} :
  a ∈ s ^ n ↔ ∃ f : fin n → s, (list.of_fn (λ i, (f i : α))).prod = a :=
by rw [←mem_prod_list_of_fn, list.of_fn_const, list.prod_replicate]

end set

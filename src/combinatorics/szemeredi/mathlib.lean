/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.order.floor
import combinatorics.simple_graph.degree_sum

/-! # Things that belong to mathlib -/

open finset function sum
open_locale big_operators

variables {α 𝕜 ι : Type*}

namespace tactic
open positivity
open_locale positivity

private lemma sub_ne_zero_of_ne' [subtraction_monoid α] {a b : α} (h : b ≠ a) : a - b ≠ 0 :=
sub_ne_zero_of_ne h.symm

/-- Extension for the `positivity` tactic: `a - b` is positive if `b < a` and nonnegative if
`b ≤ a`. Note, this only tries to find the appropriate assumption in context. -/
@[positivity]
meta def positivity_sub : expr → tactic strictness
| `(%%a - %%b) :=
  (do
    p ← to_expr ``(%%b < %%a) >>= find_assumption,
    positive <$> mk_app ``tsub_pos_of_lt [p] <|> positive <$> mk_app ``sub_pos_of_lt [p]) <|>
  (do
    p ← to_expr ``(%%b ≤ %%a) >>= find_assumption,
    nonnegative <$> mk_app ``sub_nonneg_of_le [p]) ≤|≥
  (do
    p ← to_expr ``(%%a ≠ %%b) >>= find_assumption,
    nonzero <$> to_expr ``(sub_ne_zero_of_ne %%p)) <|>
  do
    p ← to_expr ``(%%b ≠ %%a) >>= find_assumption,
    nonzero <$> to_expr ``(sub_ne_zero_of_ne' %%p)
| e := pp e >>= fail ∘ format.bracket "The expression `" "` is not of the form `a - b`"

example {a b : ℕ} (h : b < a) : 0 < a - b := by positivity
example {a b : ℤ} (h : b < a) : 0 < a - b := by positivity
example {a b : ℤ} (h : b ≤ a) : 0 ≤ a - b := by positivity

end tactic

attribute [protected] nat.div_mul_div_comm

namespace nat
variables [linear_ordered_semiring α] [floor_semiring α] {a : α} {n : ℕ}

lemma ceil_of_nonpos (ha : a ≤ 0) : ⌈a⌉₊ = 0 :=
nonpos_iff_eq_zero.1 $ ceil_le.2 $ ha.trans_eq cast_zero.symm

end nat

namespace simple_graph
variables {G G' : simple_graph α} {s : finset α}

attribute [simp] dart.is_adj

variables [decidable_eq α] [decidable_rel G.adj] [fintype α]

lemma two_mul_card_edge_finset :
  2 * G.edge_finset.card = (univ.filter $ λ xy : α × α, G.adj xy.1 xy.2).card :=
begin
  rw [←dart_card_eq_twice_card_edges, ←card_univ],
  refine card_congr (λ i _, (i.fst, i.snd)) (by simp) (by simp [dart.ext_iff, ←and_imp]) _,
  exact λ xy h, ⟨⟨xy, (mem_filter.1 h).2⟩, mem_univ _, prod.mk.eta⟩,
end

end simple_graph

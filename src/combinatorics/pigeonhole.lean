/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Yury Kudryashov
-/
import data.fintype.basic
import algebra.big_operators.order

/-!
# Pigeonhole principles

Given pigeons (possibly infinitely many) in pigeonholes, the
pigeonhole principle states that, if there are more pigeons than
pigeonholes, then there is a pigeonhole with two or more pigeons.

There are a few variations on this statement, and the conclusion can
be made stronger depending on how many pigeons you know you might
have.

The basic statements of the pigeonhole principle appear in the
following locations:

* `data.finset.basic` has `finset.pigeonhole`
* `data.fintype.basic` has `fintype.pigeonhole`
* `data.fintype.basic` has `fintype.infinite_pigeonhole`
* `data.fintype.basic` has `fintype.strong_infinite_pigeonhole`

This module gives access to these pigeonhole principles along with a few more:

* `finset.exists_lt_sum_fiberwise_of_nsmul_lt_sum`,
  `fintype.exists_lt_sum_fiberwise_of_nsmul_lt_sum`: the pigeonhole principle for finitely many
  pigeons with weights in a `decidable_linear_ordered_cancel_add_comm_monoid`, strict inequality
  version.

* `finset.exists_le_sum_fiberwise_of_nsmul_le_sum`,
  `fintype.exists_le_sum_fiberwise_of_nsmul_le_sum`: the pigeonhole principle for finitely many
  pigeons with weights in a `decidable_linear_ordered_cancel_add_comm_monoid`, non-strict inequality
  version.

* `finset.strong_pigeonhole`, `fintype.strong_pigeonhole`: the pigeonhole principle for finitely
  many pigeons of the same weight; there exists a pigeonhole which contains at least the average
  value of pigeons per pigeonhole.

Dijkstra observed in EWD980 that the classic pigeonhole principle
generalizes to the statement that in a finite list of numbers, the
maximum value is at least the average value.  These strong pigeonhole
principles state that there is a pigeonhole containing at least as
many pigeons as the average number of pigeons in each pigeonhole.

## See also

* `ordinal.infinite_pigeonhole`: pigeonhole principle for cardinals, formulated using cofinality;

* `measure_theory.exists_nonempty_inter_of_measure_univ_lt_tsum_measure`,
  `measure_theory.exists_nonempty_inter_of_measure_univ_lt_sum_measure`: pigeonhole principle in a
  measure space.

## Tags

pigeonhole principle
-/

universes u v w
variables {α : Type u} {β : Type v} {M : Type w} [decidable_linear_ordered_cancel_add_comm_monoid M]

open_locale big_operators

namespace finset

/--
The pigeonhole principle for finitely many pigeons of different weights, strict inequality version:
there is a pigeonhole with the total weight of pigeons in it greater than `b` provided that
the total number of pigeonholes times `b` is less than the total weight of all pigeons.

See also: `finset.exists_le_sum_fiberwise_of_nsmul_le_sum`, `finset.strong_pigeonhole`,
`finset.pigeonhole`
-/
lemma exists_lt_sum_fiberwise_of_nsmul_lt_sum {s : finset α} {t : finset β} [decidable_eq β]
  {f : α → β} (hf : ∀ a ∈ s, f a ∈ t) {w : α → M} {b : M} (hb : t.card •ℕ b < ∑ x in s, w x) :
  ∃ y ∈ t, b < ∑ x in s.filter (λ x, f x = y), w x :=
exists_lt_of_sum_lt $ by simpa only [sum_fiberwise_of_maps_to hf, sum_const]

/--
The pigeonhole principle for finitely many pigeons of different weights, non-strict inequality
version: there is a pigeonhole with the total weight of pigeons in it greater than or equal to `b`
provided that the total number of pigeonholes times `b` is less than or equal to the total weight of
all pigeons.

See also: `finset.exists_sum_fiberwise_le_of_sum_le`, `finset.strong_pigeonhole`,
`finset.pigeonhole`
-/
lemma exists_le_sum_fiberwise_of_nsmul_le_sum {s : finset α} {t : finset β} [decidable_eq β]
  {f : α → β} (hf : ∀ a ∈ s, f a ∈ t) (ht : t.nonempty)
  {w : α → M} {b : M} (hb : t.card •ℕ b ≤ ∑ x in s, w x) :
  ∃ y ∈ t, b ≤ ∑ x in s.filter (λ x, f x = y), w x :=
exists_le_of_sum_le ht $ by simpa only [sum_fiberwise_of_maps_to hf, sum_const]

/--
The strong pigeonhole principle for finitely many pigeons and
pigeonholes: there is a pigeonhole with at least as many pigeons as
the ceiling of the average number of pigeons across all pigeonholes.
("The maximum is at least the mean" specialized to integers.)

More formally, given a function between finite sets `s` and `t` and
setting `n` so that `n + 1` is at most the ceiling of `s.card /
t.card`, then there is an element of `t` whose preimage contains more
than `n` elements.  (We formulate the constraint on `n` as
`t.card * n < s.card`.  Since we have a function `f` from `s` to `t`,
this implies `t.card ≠ 0`, so `s.card / t.card` is defined.)

See also: `finset.pigeonhole`
-/
lemma strong_pigeonhole {s : finset α} {t : finset β} [decidable_eq β]
  {f : α → β} (hf : ∀ a ∈ s, f a ∈ t)
  {n : ℕ} (hn : t.card * n < s.card) :
  ∃ y ∈ t, n < (s.filter (λ x, f x = y)).card :=
begin
  simp only [card_eq_sum_ones],
  apply exists_lt_sum_fiberwise_of_nsmul_lt_sum hf,
  simpa
end

end finset

namespace fintype
open finset

variables [fintype α] [fintype β] [decidable_eq β]

/--
The pigeonhole principle for finitely many pigeons of different weights, strict inequality version:
there is a pigeonhole with the total weight of pigeons in it greater than `b` provided that
the total number of pigeonholes times `b` is less than the total weight of all pigeons.

See also: `fintype.exists_le_sum_fiberwise_of_nsmul_le_sum`, `fintype.strong_pigeonhole`,
`fintype.pigeonhole`
-/
lemma exists_lt_sum_fiberwise_of_nsmul_lt_sum (f : α → β)
  {w : α → M} {b : M} (hb : card β •ℕ b < ∑ x, w x) :
  ∃ y, b < ∑ x in univ.filter (λ x, f x = y), w x :=
let ⟨y, _, hy⟩ := exists_lt_sum_fiberwise_of_nsmul_lt_sum (λ _ _, mem_univ _) hb in ⟨y, hy⟩

/--
The pigeonhole principle for finitely many pigeons of different weights, non-strict inequality
version: there is a pigeonhole with the total weight of pigeons in it greater than or equal to `b`
provided that the total number of pigeonholes times `b` is less than or equal to the total weight of
all pigeons.

See also: `finset.exists_sum_fiberwise_le_of_sum_le`, `finset.strong_pigeonhole`,
`finset.pigeonhole`
-/
lemma exists_le_sum_fiberwise_of_nsmul_le_sum [nonempty β] (f : α → β)
  {w : α → M} {b : M} (hb : card β •ℕ b ≤ ∑ x, w x) :
  ∃ y, b ≤ ∑ x in univ.filter (λ x, f x = y), w x :=
let ⟨y, _, hy⟩ := exists_le_sum_fiberwise_of_nsmul_le_sum (λ _ _, mem_univ _) univ_nonempty hb
in ⟨y, hy⟩

/--
The strong pigeonhole principle for finitely many pigeons and pigeonholes.
There is a pigeonhole with at least as many pigeons as
the ceiling of the average number of pigeons across all pigeonholes.
("The maximum is at least the mean" specialized to integers.)

More formally, given a function between finite types `α` and `β` and
setting `n` so that `n + 1` is at most the ceiling of `card α / card β`,
then there is an element of `β` whose preimage contains more
than `n` elements.  (We formulate the constraint on `n` as
`card β * n < card α`.  Since we have a function `f` from `α` to `β`,
this implies `card β ≠ 0`, so `card α / card β` is defined.)

See also: `finset.strong_pigeonhole`, `fintype.pigeonhole`, `fintype.strong_infinite_pigeonhole`
-/
lemma strong_pigeonhole (f : α → β) {n : ℕ} (hn : card β * n < card α) :
  ∃ y : β, n < (univ.filter (λ x, f x = y)).card :=
let ⟨y, _, h⟩ := strong_pigeonhole (λ _ _, mem_univ _) hn in ⟨y, h⟩

end fintype

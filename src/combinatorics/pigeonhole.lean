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

This module gives access to these pigeonhole principles along with two
additional ones:

* `finset.strong_pigeonhole`
* `fintype.strong_pigeonhole`

Dijkstra observed in EWD980 that the classic pigeonhole principle
generalizes to the statement that in a finite list of numbers, the
maximum value is at least the average value.  These strong pigeonhole
principles state that there is a pigeonhole containing at least as
many pigeons as the average number of pigeons in each pigeonhole.

See also: `ordinal.infinite_pigeonhole`

## Tags

pigeonhole principle
-/

universes u v
variables {α : Type u} {β : Type v}

open_locale big_operators

namespace finset

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
  classical, by_contra hz, push_neg at hz,
  suffices h : s.card ≤ t.card * n,
  { have h' := lt_of_le_of_lt h hn,
    exact nat.lt_asymm h' h' },
  have key := λ (y : β) (yel : y ∈ t), (preimage_card_ne_zero_iff_mem_image s f y).mp,
  calc s.card = ∑ y in s.image f, (s.filter (λ x, f x = y)).card :
    by apply card_eq_sum_card_image
          ... = ∑ y in t, (s.filter (λ x, f x = y)).card :
    by { rw ←sum_filter_of_ne key, congr, convert (filter_mem_image_eq_image f s t hf).symm }
          ... ≤ ∑ y in t, n :
    by { convert sum_le_sum hz, simp, }
          ... = t.card * n :
    by { simp only [nat.cast_id, nsmul_eq_mul, sum_const] },
end

end finset

namespace fintype
open finset

/--
This is the `fintype` version of `finset.strong_pigeonhole`.
There is a pigeonhole with at least as many pigeons as
the ceiling of the average number of pigeons across all pigeonholes.
("The maximum is at least the mean" specialized to integers.)

More formally, given a function between finite types `α` and `β` and
setting `n` so that `n + 1` is at most the ceiling of `card α / card β`,
then there is an element of `β` whose preimage contains more
than `n` elements.  (We formulate the constraint on `n` as
`card β * n < card α`.  Since we have a function `f` from `α` to `β`,
this implies `card β ≠ 0`, so `card α / card β` is defined.)

See also: `fintype.pigeonhole`, `fintype.strong_infinite_pigeonhole`
-/
lemma strong_pigeonhole [fintype α] [fintype β] [decidable_eq β] (f : α → β)
  (n : ℕ) (hn : card β * n < card α) :
  ∃ y : β, n < (univ.filter (λ x, f x = y)).card :=
begin
  obtain ⟨y, _, h⟩ := @strong_pigeonhole _ _ univ univ _ f (by simp) n hn,
  exact ⟨y, h⟩,
end

end fintype

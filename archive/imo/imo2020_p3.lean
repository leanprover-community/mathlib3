/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.basic
import algebra.floor
import combinatorics.simple_graph.basic
import data.finset.intervals
import data.real.basic

open_locale big_operators
open finset

/-!
# IMO 2020 P3

There are `4n` pebbles of weights `1, ..., 4n`. Each pebble is coloured in one of `n` colors and
there are four pebbles of each color. Show that we can arrange the pebbles into two piles so that
the following two conditions are both satisfied:
• The total weights of both piles are the same.
• Each pile contains two pebbles of each color.
-/

theorem imo2020_p3 {n : ℕ} {color_of_pebble : fin (4 * n) → fin n} {pebbles_of_color : fin n →
  finset (fin (4 * n))} (hinv : ∀ pebble, pebble ∈ pebbles_of_color (color_of_pebble pebble))
  (hpebbles : ∀ color, (pebbles_of_color color).card = 4) :
  ∃ half : finset (fin (4 * n)), (∑ weight in half, weight : ℕ) = (∑ weight in halfᶜ, weight) ∧
  ∀ color, (pebbles_of_color color ∩ half).card = 2 :=
begin
  let G : simple_graph (fin (4 * n)) := simple_graph.from_rel
    (λ a b, (a + b : ℕ) = 4 * n + 1 ∨ color_of_pebble a = color_of_pebble b),
end

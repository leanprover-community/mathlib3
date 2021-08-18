/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .walk

/-!
# The Oxford Invariants Puzzle Challenges - Summer 2021, Week 4, Problem 1

## Original statement



## Comments



## Formalised statement



## Proof outline

### First part

`2`-color the tree. Let's show by induction that there's always at least one frog on each color:
* Base case:
  As `2 ≤ n`, take two neighbor frogs. Their lily pads are of different color, so we are done.
* Induction step:


### Second part
-/

open_locale big_operators

variables {α : Type*} [linear_ordered_field α]

theorem week4_p1 : true := trivial

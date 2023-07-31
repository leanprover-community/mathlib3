/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

/-!
# Absolute value

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a notational class `has_abs` which adds the unary operator `abs` and the notation
`|.|`. The concept of an absolute value occurs in lattice ordered groups and in GL and GM spaces.

Mathematical structures possessing an absolute value often also possess a unique decomposition of
elements into "positive" and "negative" parts which are in some sense "disjoint" (e.g. the Jordan
decomposition of a measure). This file also defines `has_pos_part` and `has_neg_part` classes
which add unary operators `pos` and `neg`, representing the maps taking an element to its positive
and negative part respectively along with the notation ⁺ and ⁻.

## Notations

The following notation is introduced:

* `|.|` for the absolute value;
* `.⁺` for the positive part;
* `.⁻` for the negative part.

## Tags

absolute
-/


/--
Absolute value is a unary operator with properties similar to the absolute value of a real number.
-/
class has_abs (α : Type*) := (abs : α → α)
export has_abs (abs)

/--
The positive part of an element admiting a decomposition into positive and negative parts.
-/
class has_pos_part (α : Type*) := (pos : α → α)

/--
The negative part of an element admiting a decomposition into positive and negative parts.
-/
class has_neg_part (α : Type*) := (neg : α → α)

notation `|`a`|` := abs a
postfix `⁺`:1000 := has_pos_part.pos
postfix `⁻`:1000 := has_neg_part.neg

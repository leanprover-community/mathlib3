/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

/-!
# Absolute value

This file defines a notational class `has_abs` which adds the unary operator `abs` and the notation
`|.|`. The concept of an absolute value occurs in lattice ordered groups and in GL and GM spaces.

## Notations

The notation `|.|` is introduced for the absolute value.

## Tags

absolute
-/


/--
Absolute value is a unary operator with properties similar to the absolute value of a real number.
-/
class has_abs (α : Type*) := (abs : α → α)
export has_abs (abs)

notation `|`a`|` := abs a

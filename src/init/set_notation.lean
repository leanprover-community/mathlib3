/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

/-!
# Placeholder for mathlib4's `Init.SetNotation`.

Various changes have been made between the core libraries of Lean 3 and Lean 4.
As an example, there is no `HasMem` corresponding to the `has_mem` in Lean 3,
and `∈` notation has not been set up.

Instead, we introduce this notation typeclass and its notation in mathlib4.

When we run mathport to translate files in mathlib3 that rely on `has_mem`,
we need to insert the line `import Mathlib.Init.SetNotation`.

There are various ways we could achieve this:
1. Teach `mathport` to detect this condition, and add the import when needed.
2. Have a configuration file for `mathport` that tells it where this import is needed.
3. Add "placeholder" imports in mathlib3.

Pros and cons:
1. requires writing code for a condition that rarely occurs.
2. does as well, although to a lesser extent.
3. arguably introduces some clutter in mathlib3, but is the simplest to implement.

This file represents the implementation of choice 3.
We're essentially starting to annotate mathlib3 with the additional information mathport requires
to make a successful port.
-/

-- This file intentionally blank; it has been written by hand in mathlib4.

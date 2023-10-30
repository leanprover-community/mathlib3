/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.nat.lattice
import data.enat.basic

/-!
# Extended natural numbers form a complete linear order

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This instance is not in `data.enat.basic` to avoid dependency on `finset`s.
-/

attribute [derive complete_linear_order] enat

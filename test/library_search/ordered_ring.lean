-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import algebra.ordered_ring

example {a b : ℕ} (h : b > 0) (w : a ≥ 1) : b ≤ a * b :=
by library_search -- exact (le_mul_iff_one_le_left h).mpr w

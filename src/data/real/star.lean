/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.star.basic
import data.real.basic

/-! # Star-ring structure on the real numbers -/

/-- The real numbers are a `*`-ring, with the trivial `*`-structure. -/
instance : star_ring ℝ          := star_ring_of_comm
instance : has_trivial_star ℝ   := ⟨λ _, rfl⟩

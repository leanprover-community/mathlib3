/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import data.complex.module
import linear_algebra.orientation

/-!
# The standard orientation on `ℂ`.

This had previously been in `linear_algebra.orientation`,
but keeping it separate results in a significant import reduction.
-/

namespace complex

/-- The standard orientation on `ℂ`. -/
protected noncomputable def orientation : orientation ℝ ℂ (fin 2) := complex.basis_one_I.orientation

end complex

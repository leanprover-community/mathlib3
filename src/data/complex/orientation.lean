/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import linear_algebra.orientation
import data.complex.module

/-!
# Orientation on `ℂ`
-/

namespace complex

/-- The standard orientation on `ℂ`. -/
protected noncomputable def orientation : orientation ℝ ℂ (fin 2) := complex.basis_one_I.orientation

end complex

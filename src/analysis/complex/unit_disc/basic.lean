/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.complex.basic

/-!
-/

namespace complex

def unit_disc : Type := {p : ℂ | abs p < 1}

localized "notation `𝔻` := complex.unit_disc" in unit_disc



end complex

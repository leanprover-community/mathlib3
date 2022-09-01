/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import data.real.basic
import ring_theory.localization.integral

/-!
TODO
-/

theorem transcendental_iff_transcendental_over_ℚ (x : ℝ) :
  transcendental ℤ x ↔ transcendental ℚ x :=
iff.not $ is_fraction_ring.is_algebraic_iff ℤ ℚ ℝ

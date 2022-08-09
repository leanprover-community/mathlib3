import data.real.basic
import ring_theory.localization.integral

theorem transcendental_iff_transcendental_over_ℚ (x : ℝ) :
  transcendental ℤ x ↔ transcendental ℚ x :=
iff.not $ is_fraction_ring.is_algebraic_iff ℤ ℚ ℝ

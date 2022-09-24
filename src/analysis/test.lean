import analysis.special_functions.pow

open_locale nnreal ennreal

namespace nnreal

lemma le_rpow_inv_iff_of_pos' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {c : ℝ} (hc : 0 < c) :
  a ≤ b^c⁻¹ ↔ a^c ≤ b := sorry

lemma le_rpow_inv_iff_of_pos (a b : ℝ≥0) {c : ℝ} (hc : 0 < c) :
  a ≤ b^c⁻¹ ↔ a^c ≤ b :=
le_rpow_inv_iff_of_pos' a.2 b.2 hc

lemma le_rpow_inv_iff_of_pos'' (a b : ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
  a ≤ b^c⁻¹ ↔ a^c ≤ b :=
begin
  have hc' : 0 < c⁻¹ := sorry,
  by_cases hb : b = ⊤,
  {
    rw hb,
    simp [hc'],
  },

end
--le_rpow_inv_iff_of_pos' a.2 b.2 hc



lemma lt_rpow_inv_iff_of_pos (a b : ℝ≥0) {c : ℝ} (hc : 0 < c) :
  a < b^c⁻¹ ↔ a^c < b := sorry

lemma rpow_inv_le_iff_of_pos (a b : ℝ≥0) {c : ℝ} (hc : 0 < c) :
  a^c⁻¹ ≤ b ↔ a ≤ b^c := sorry

lemma rpow_inv_lt_iff_of_pos (a b : ℝ≥0) {c : ℝ} (hc : 0 < c) :
  a^c⁻¹ < b ↔ a < b^c := sorry

end nnreal

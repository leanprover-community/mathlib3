/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import topology.instances.real

noncomputable theory
open_locale classical topological_space filter
open set

/-! ### The unit interval -/

localized "notation `I` := set.Icc (0 : ℝ) 1" in unit_interval

lemma Icc_zero_one_symm {t : ℝ} : t ∈ I ↔ 1 - t ∈ I :=
begin
  rw [mem_Icc, mem_Icc],
  split ; intro ; split ; linarith
end

instance I_has_zero : has_zero I := ⟨⟨0, by split ; norm_num⟩⟩

@[simp, norm_cast] lemma coe_I_zero : ((0 : I) : ℝ) = 0 := rfl

instance I_has_one : has_one I := ⟨⟨1, by split ; norm_num⟩⟩

@[simp, norm_cast] lemma coe_I_one : ((1 : I) : ℝ) = 1 := rfl

instance : nonempty I := ⟨0⟩

/-- Unit interval central symmetry. -/
def I_symm : I → I := λ t, ⟨1 - t.val, Icc_zero_one_symm.mp t.property⟩

localized "notation `σ` := I_symm" in unit_interval

@[simp] lemma I_symm_zero : σ 0 = 1 :=
subtype.ext $ by simp [I_symm]

@[simp] lemma I_symm_one : σ 1 = 0 :=
subtype.ext $ by simp [I_symm]

@[continuity]
lemma continuous_I_symm : continuous σ :=
by continuity!

instance : connected_space I :=
subtype.connected_space ⟨nonempty_Icc.mpr zero_le_one, is_preconnected_Icc⟩

/-- Verify there is an instance for `compact_space I`. -/
example : compact_space I := by apply_instance

namespace unit_interval

lemma nonneg (x : I) : 0 ≤ (x : ℝ) := x.2.1
lemma one_minus_nonneg (x : I) : 0 ≤ 1 - (x : ℝ) := by simpa using x.2.2
lemma le_one (x : I) : (x : ℝ) ≤ 1 := x.2.2
lemma one_minus_le_one (x : I) : 1 - (x : ℝ) ≤ 1 := by simpa using x.2.1

end unit_interval

namespace tactic.interactive

/-- A tactic that solves `0 ≤ x`, `0 ≤ 1 - x`, `x ≤ 1`, and `1 - x ≤ 1` for `x : I`. -/
meta def unit_interval : tactic unit :=
`[apply unit_interval.nonneg] <|> `[apply unit_interval.one_minus_nonneg] <|>
`[apply unit_interval.le_one] <|> `[apply unit_interval.one_minus_le_one]

end tactic.interactive

/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison
-/
import topology.instances.real
import topology.algebra.field

/-!
# The unit interval, as a topological space

Use `open_locale unit_interval` to turn on the notation `I := set.Icc (0 : ℝ) (1 : ℝ)`.

We provide basic instances, as well as a custom tactic for discharging
`0 ≤ x`, `0 ≤ 1 - x`, `x ≤ 1`, and `1 - x ≤ 1` when `x : I`.

-/

noncomputable theory
open_locale classical topological_space filter
open set

/-! ### The unit interval -/

/-- The unit interval `[0,1]` in ℝ. -/
abbreviation unit_interval : set ℝ := set.Icc 0 1

localized "notation `I` := unit_interval" in unit_interval

namespace unit_interval

lemma mem_iff_one_sub_mem {t : ℝ} : t ∈ I ↔ 1 - t ∈ I :=
begin
  rw [mem_Icc, mem_Icc],
  split ; intro ; split ; linarith
end

instance has_zero : has_zero I := ⟨⟨0, by split ; norm_num⟩⟩

@[simp, norm_cast] lemma coe_zero : ((0 : I) : ℝ) = 0 := rfl

@[simp] lemma mk_zero (h : (0 : ℝ) ∈ Icc (0 : ℝ) 1) : (⟨0, h⟩ : I) = 0 := rfl

instance has_one : has_one I := ⟨⟨1, by split ; norm_num⟩⟩

@[simp, norm_cast] lemma coe_one : ((1 : I) : ℝ) = 1 := rfl

@[simp] lemma mk_one (h : (1 : ℝ) ∈ Icc (0 : ℝ) 1) : (⟨1, h⟩ : I) = 1 := rfl

instance : nonempty I := ⟨0⟩

/-- Unit interval central symmetry. -/
def symm : I → I := λ t, ⟨1 - t.val, mem_iff_one_sub_mem.mp t.property⟩

localized "notation `σ` := unit_interval.symm" in unit_interval

@[simp] lemma symm_zero : σ 0 = 1 :=
subtype.ext $ by simp [symm]

@[simp] lemma symm_one : σ 1 = 0 :=
subtype.ext $ by simp [symm]

@[simp] lemma symm_symm (x : I) : σ (σ x) = x :=
subtype.ext $ by simp [symm]

@[simp] lemma coe_symm_eq (x : I) : (σ x : ℝ) = 1 - x := rfl

@[continuity]
lemma continuous_symm : continuous σ :=
by continuity!

instance : connected_space I :=
subtype.connected_space ⟨nonempty_Icc.mpr zero_le_one, is_preconnected_Icc⟩

/-- Verify there is an instance for `compact_space I`. -/
example : compact_space I := by apply_instance

lemma nonneg (x : I) : 0 ≤ (x : ℝ) := x.2.1
lemma one_minus_nonneg (x : I) : 0 ≤ 1 - (x : ℝ) := by simpa using x.2.2
lemma le_one (x : I) : (x : ℝ) ≤ 1 := x.2.2
lemma one_minus_le_one (x : I) : 1 - (x : ℝ) ≤ 1 := by simpa using x.2.1

lemma mul_pos_mem_iff {a t : ℝ} (ha : 0 < a) : a * t ∈ I ↔ t ∈ set.Icc (0 : ℝ) (1/a) :=
begin
  split; rintros ⟨h₁, h₂⟩; split,
  { exact nonneg_of_mul_nonneg_left h₁ ha },
  { rwa [le_div_iff ha, mul_comm] },
  { exact mul_nonneg ha.le h₁ },
  { rwa [le_div_iff ha, mul_comm] at h₂ }
end

lemma two_mul_sub_one_mem_iff {t : ℝ} : 2 * t - 1 ∈ I ↔ t ∈ set.Icc (1/2 : ℝ) 1 :=
by split; rintros ⟨h₁, h₂⟩; split; linarith

end unit_interval

namespace tactic.interactive

/-- A tactic that solves `0 ≤ x`, `0 ≤ 1 - x`, `x ≤ 1`, and `1 - x ≤ 1` for `x : I`. -/
meta def unit_interval : tactic unit :=
`[apply unit_interval.nonneg] <|> `[apply unit_interval.one_minus_nonneg] <|>
`[apply unit_interval.le_one] <|> `[apply unit_interval.one_minus_le_one]

end tactic.interactive

section
variables {𝕜 : Type*} [linear_ordered_field 𝕜] [topological_space 𝕜] [topological_ring 𝕜]

/--
The image of `[0,1]` under the homeomorphism `λ x, a * x + b` is `[b, a+b]`.
-/
-- We only need the ordering on `𝕜` here to avoid talking about flipping the interval over.
-- At the end of the day I only care about `ℝ`, so I'm hesitant to put work into generalizing.
lemma affine_homeomorph_image_I (a b : 𝕜) (h : 0 < a) :
  affine_homeomorph a b h.ne.symm '' set.Icc 0 1 = set.Icc b (a + b) :=
by simp [h]

/--
The affine homeomorphism from a nontrivial interval `[a,b]` to `[0,1]`.
-/
def Icc_homeo_I (a b : 𝕜) (h : a < b) : set.Icc a b ≃ₜ set.Icc (0 : 𝕜) (1 : 𝕜) :=
begin
  let e := homeomorph.image (affine_homeomorph (b-a) a (sub_pos.mpr h).ne.symm) (set.Icc 0 1),
  refine (e.trans _).symm,
  apply homeomorph.set_congr,
  simp [sub_pos.mpr h],
end

@[simp] lemma Icc_homeo_I_apply_coe (a b : 𝕜) (h : a < b) (x : set.Icc a b) :
  ((Icc_homeo_I a b h) x : 𝕜) = (x - a) / (b - a) :=
rfl

@[simp] lemma Icc_homeo_I_symm_apply_coe (a b : 𝕜) (h : a < b) (x : set.Icc (0 : 𝕜) (1 : 𝕜)) :
  ((Icc_homeo_I a b h).symm x : 𝕜) = (b - a) * x + a :=
rfl

end

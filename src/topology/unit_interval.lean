/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison
-/
import topology.instances.real
import topology.algebra.field
import data.set.intervals.proj_Icc
import data.set.intervals.instances

/-!
# The unit interval, as a topological space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Use `open_locale unit_interval` to turn on the notation `I := set.Icc (0 : ℝ) (1 : ℝ)`.

We provide basic instances, as well as a custom tactic for discharging
`0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` when `x : I`.

-/

noncomputable theory
open_locale classical topology filter
open set int set.Icc

/-! ### The unit interval -/

/-- The unit interval `[0,1]` in ℝ. -/
abbreviation unit_interval : set ℝ := set.Icc 0 1

localized "notation (name := unit_interval) `I` := unit_interval" in unit_interval

namespace unit_interval

lemma zero_mem : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩

lemma one_mem : (1 : ℝ) ∈ I := ⟨zero_le_one, le_rfl⟩

lemma mul_mem {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) : x * y ∈ I :=
⟨mul_nonneg hx.1 hy.1, (mul_le_mul hx.2 hy.2 hy.1 zero_le_one).trans_eq $ one_mul 1⟩

lemma div_mem {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) : x / y ∈ I :=
⟨div_nonneg hx hy, div_le_one_of_le hxy hy⟩

lemma fract_mem (x : ℝ) : fract x ∈ I := ⟨fract_nonneg _, (fract_lt_one _).le⟩

lemma mem_iff_one_sub_mem {t : ℝ} : t ∈ I ↔ 1 - t ∈ I :=
begin
  rw [mem_Icc, mem_Icc],
  split ; intro ; split ; linarith
end

instance has_zero : has_zero I := ⟨⟨0, zero_mem⟩⟩

instance has_one : has_one I := ⟨⟨1, by split ; norm_num⟩⟩

instance : zero_le_one_class I := ⟨@zero_le_one ℝ _ _ _ _⟩

lemma coe_ne_zero {x : I} : (x : ℝ) ≠ 0 ↔ x ≠ 0 :=
not_iff_not.mpr coe_eq_zero

lemma coe_ne_one {x : I} : (x : ℝ) ≠ 1 ↔ x ≠ 1 :=
not_iff_not.mpr coe_eq_one

lemma univ_eq_Icc : (univ : set I) = Icc 0 1 :=
by { ext ⟨x,xl,xr⟩, simp only [mem_univ, true_iff], exact ⟨xl,xr⟩, }

instance : nonempty I := ⟨0⟩

instance : has_mul I := ⟨λ x y, ⟨x * y, mul_mem x.2 y.2⟩⟩

-- todo: we could set up a `linear_ordered_comm_monoid_with_zero I` instance

lemma mul_le_left {x y : I} : x * y ≤ x :=
subtype.coe_le_coe.mp $ (mul_le_mul_of_nonneg_left y.2.2 x.2.1).trans_eq $ mul_one x

lemma mul_le_right {x y : I} : x * y ≤ y :=
subtype.coe_le_coe.mp $ (mul_le_mul_of_nonneg_right x.2.2 y.2.1).trans_eq $ one_mul y

/-- Halving an element of `unit_interval`. -/
def div_two (t : I) : I := ⟨(t/2 : ℝ), div_mem t.2.1 zero_le_two $ t.2.2.trans one_le_two⟩

lemma two_mul_div_two (t : I) : (2 * div_two t : ℝ) = t := mul_div_cancel' _ two_ne_zero

lemma div_two_mem_Iic (t : I) : div_two t ∈ set.Iic (div_two 1) :=
div_le_div_of_le_of_nonneg t.2.2 zero_le_two

/-- Unit interval central symmetry. -/
def symm : I → I := λ t, ⟨1 - t, mem_iff_one_sub_mem.mp t.prop⟩

localized "notation (name := unit_interval.symm) `σ` := unit_interval.symm" in unit_interval

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

lemma antitone_symm : antitone symm := λ x y h, sub_le_sub_left h _

lemma bijective_symm : function.bijective symm :=
function.bijective_iff_has_inverse.2 $ ⟨_, symm_symm, symm_symm⟩

lemma half_le_symm_iff (t : I) : 1 / 2 ≤ (symm t : ℝ) ↔ (t : ℝ) ≤ 1 / 2 :=
by rw [coe_symm_eq, le_sub_iff_add_le, add_comm, ←le_sub_iff_add_le, sub_half]

lemma symm_mem_Ici_iff (t : I) : symm t ∈ set.Ici (div_two 1) ↔ t ∈ set.Iic (div_two 1) :=
half_le_symm_iff t

instance : connected_space I :=
subtype.connected_space ⟨nonempty_Icc.mpr zero_le_one, is_preconnected_Icc⟩

/-- Verify there is an instance for `compact_space I`. -/
example : compact_space I := by apply_instance

lemma nonneg (x : I) : 0 ≤ (x : ℝ) := x.2.1
lemma one_minus_nonneg (x : I) : 0 ≤ 1 - (x : ℝ) := by simpa using x.2.2
lemma le_one (x : I) : (x : ℝ) ≤ 1 := x.2.2
lemma one_minus_le_one (x : I) : 1 - (x : ℝ) ≤ 1 := by simpa using x.2.1
lemma add_pos {t : I} {x : ℝ} (hx : 0 < x) : 0 < (x + t : ℝ) :=
add_pos_of_pos_of_nonneg hx $ nonneg _

/-- like `unit_interval.nonneg`, but with the inequality in `I`. -/
lemma nonneg' {t : I} : 0 ≤ t := t.2.1
/-- like `unit_interval.le_one`, but with the inequality in `I`. -/
lemma le_one' {t : I} : t ≤ 1 := t.2.2

lemma mul_pos_mem_iff {a t : ℝ} (ha : 0 < a) : a * t ∈ I ↔ t ∈ set.Icc (0 : ℝ) (1/a) :=
begin
  split; rintros ⟨h₁, h₂⟩; split,
  { exact nonneg_of_mul_nonneg_right h₁ ha },
  { rwa [le_div_iff ha, mul_comm] },
  { exact mul_nonneg ha.le h₁ },
  { rwa [le_div_iff ha, mul_comm] at h₂ }
end

lemma two_mul_sub_one_mem_iff {t : ℝ} : 2 * t - 1 ∈ I ↔ t ∈ set.Icc (1/2 : ℝ) 1 :=
by split; rintros ⟨h₁, h₂⟩; split; linarith

end unit_interval

@[simp] lemma proj_Icc_eq_zero {x : ℝ} : proj_Icc (0 : ℝ) 1 zero_le_one x = 0 ↔ x ≤ 0 :=
proj_Icc_eq_left zero_lt_one

@[simp] lemma proj_Icc_eq_one {x : ℝ} : proj_Icc (0 : ℝ) 1 zero_le_one x = 1 ↔ 1 ≤ x :=
proj_Icc_eq_right zero_lt_one

namespace tactic.interactive

/-- A tactic that solves `0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` for `x : I`. -/
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

-- TODO : move the following lemmas where they belong and restate them
-- to match existing API

/- `data/set/pointwise/interval.lean#525` :
@[simp] lemma image_affine_Icc' {a : α} (h : 0 < a) (b c d : α) :
  (λ x, a * x + b) '' Icc c d = Icc (a * c + b) (a * d + b) :=
begin
  suffices : (λ x, x + b) '' ((λ x, a * x) '' Icc c d) = Icc (a * c + b) (a * d + b),
  { rwa set.image_image at this, },
  rw [image_mul_left_Icc' h, image_add_const_Icc],
end
-/

-- Should go just before `image_affine_Icc'` ?
@[simp] lemma image_affine_Icc {α : Type*} [linear_ordered_field α]
  {a : α} (h : 0 ≤ a) (b c d : α) (hcd : c ≤ d) :
  (λ x, a * x + b) '' Icc c d = Icc (a * c + b) (a * d + b) :=
begin
  suffices : (λ x, x + b) '' ((λ x, a * x) '' Icc c d) = Icc (a * c + b) (a * d + b),
  { rwa set.image_image at this, },
  rw [image_mul_left_Icc h hcd, image_add_const_Icc],
end

-- TODO
-- no idea where it goes
lemma monotone_affine {α : Type*} [linear_ordered_field α]
  {a : α} (h : 0 ≤ a) (b : α) : monotone (λ x, a * x + b) :=
λ x y xy, add_le_add_right (mul_le_mul_of_nonneg_left xy h) _

-- TODO where?
lemma monotone_affine_of_le {s t : ℝ} (hst : s ≤ t) : monotone (λ u, (t - s) * u + s) :=
monotone_affine (sub_nonneg.2 hst) _

-- TODO
-- Putting it in either `order/monotone/basic` or `data/set/interval/basic` means adding an import
-- in one direction…
lemma monotone.Icc_maps_to_Icc {α β} [preorder α] [preorder β] {f : α → β} (hf : monotone f)
  (a b : α) : (set.Icc a b).maps_to f (set.Icc (f a) (f b)) := λ x hx, ⟨hf hx.1, hf hx.2⟩

-- TODO : probably fits here?
lemma affine_maps_to_I {s t : ℝ} (hst : s ≤ t) :
  set.maps_to (λ u, (t - s) * u + s) I (set.Icc s t) :=
begin
  rintro u hu,
  convert (monotone_affine_of_le hst).Icc_maps_to_Icc 0 1 hu;
  simp only [mul_one, sub_add_cancel, mul_zero, zero_add],
end

-- TODO : probably fits here?
lemma affine_surj_on_I {s t : ℝ} :
  set.surj_on (λ u, (t - s) * u + s) I (set.Icc s t) :=
begin
  convert intermediate_value_Icc zero_le_one (continuous.continuous_on _) using 1,
  { simp only [mul_zero, zero_add, mul_one, sub_add_cancel], },
  any_goals { apply_instance },
  continuity,
end

end

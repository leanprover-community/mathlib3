/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import analysis.normed_space.basic
import analysis.complex.basic

/-!
# R_or_C: a typeclass for ℝ or ℂ

This file defines the typeclass is_R_or_C intended to have only two instances:
ℝ and ℂ. It is meant for definitions and theorems which hold for both the
real and the complex case, such as inner products and Hilbert spaces. Its API
follows closely that of ℂ.
-/

open classical

/--
blah
-/
class is_R_or_C (K : Type*) [normed_field K] [algebra ℝ K] [has_coe ℝ K] [decidable_eq K]:=
(re : K →+ ℝ)
(im : K →+ ℝ)
(conj : K →+* K)
(I : K)
(I_re_ax : re I = 0)
(I_def_ax : I = 0 ∨ I * I = -1)
(re_add_im_ax : ∀ (z : K), (re z : K) + (im z) * I = z)
(smul_coe_mul_ax : ∀ (z : K) (r : ℝ), r • z = (r : K) * z)
(smul_re_ax : ∀ (r : ℝ) (z : K), re (r • z) = r * (re z))
(smul_im_ax : ∀ (r : ℝ) (z : K), im (r • z) = r * (im z))
(of_real_re_ax : ∀ r : ℝ, re (r : K) = r)
(of_real_im_ax : ∀ r : ℝ, im (r : K) = 0)
(mul_re_ax : ∀ z w : K, re (z * w) = re z * re w - im z * im w)
(mul_im_ax : ∀ z w : K, im (z * w) = re z * im w + im z * re w)
(conj_re_ax : ∀ z : K, re (conj z) = re z)
(conj_im_ax : ∀ z : K, im (conj z) = -(im z))
(conj_I_ax : conj I = -I)
(eq_conj_iff_real_ax : ∀ {z : K}, conj z = z ↔ ∃ r : ℝ, z = r)
(norm_sq_eq_def : ∀ (z : K), ∥z∥^2 = (re z) * (re z) + (im z) * (im z))
(mul_im_I_ax : ∀ (z : K), (im z) * im I = im z)
(inv_def : ∀ (z : K), z⁻¹ = conj z * ((∥z∥^2)⁻¹:ℝ))
(div_I_ax : ∀ (z : K), z / I = -(z * I))

instance : has_coe ℝ ℝ := ⟨id⟩

noncomputable instance : is_R_or_C ℝ :=
{ re := ⟨id, by simp only [id.def], by simp only [forall_const, id.def, eq_self_iff_true]⟩,
  im := ⟨0, by simp only [pi.zero_apply], by simp only [add_zero, forall_const, pi.zero_apply]⟩,
  conj := ⟨id, by simp only [id.def], by simp only [forall_const, id.def, eq_self_iff_true],
          by simp only [id.def], by simp only [forall_const, id.def, eq_self_iff_true]⟩,
  I := 0,
  I_re_ax := by simp only [add_monoid_hom.map_zero],
  I_def_ax := or.intro_left _ rfl,
  re_add_im_ax := λ z, by unfold_coes; simp only [add_zero, id.def, mul_zero],
  smul_coe_mul_ax := λ z r, by unfold_coes; simp only [algebra.id.smul_eq_mul, id.def],
  smul_re_ax := λ r z, by unfold_coes; simp only [algebra.id.smul_eq_mul, id.def],
  smul_im_ax := λ r z, by unfold_coes; simp only [pi.zero_apply, mul_zero],
  of_real_re_ax := λ r, by unfold_coes; simp only [id.def],
  of_real_im_ax := λ r, by unfold_coes; simp only [pi.zero_apply],
  mul_re_ax := λ z w, by simp only [add_monoid_hom.coe_mk, id.def, pi.zero_apply, sub_zero, mul_zero],
  mul_im_ax := λ z w, by simp only [add_zero, add_monoid_hom.coe_mk, zero_mul, pi.zero_apply, mul_zero],
  conj_re_ax := λ z, by simp only [ring_hom.coe_mk, id.def],
  conj_im_ax := λ z, by simp only [add_monoid_hom.coe_mk, pi.zero_apply, neg_zero],
  conj_I_ax := by simp only [ring_hom.map_zero, neg_zero],
  eq_conj_iff_real_ax := λ z,
    begin
      dsimp,
      refine ⟨_, λ z, rfl⟩,
      intro h,
      refine ⟨z, _⟩,
      unfold_coes,
      simp only [id.def],
    end,
  norm_sq_eq_def := λ z, by simp only [pow_two, norm, ←abs_mul, abs_mul_self z, add_zero, add_monoid_hom.coe_mk, id.def, pi.zero_apply, mul_zero],
  mul_im_I_ax := λ z, by simp only [add_monoid_hom.coe_mk, pi.zero_apply, mul_zero],
  inv_def :=
    begin
      intro z,
      rcases lt_trichotomy z 0 with hlt|heq|hgt,
      { unfold_coes,
        have : z ≠ 0 := by linarith,
        field_simp [norm, abs, max_eq_right_of_lt (show z < -z, by linarith), pow_two, mul_inv'],
        calc
          1 / z = 1 * (1 / z)           : (one_mul (1 / z)).symm
            ... = (z / z) * (1 / z)     : congr_arg (λ x, x * (1 / z)) (div_self this).symm
            ... = z / (z * z)           : by field_simp },
      { simp [heq] },
      { unfold_coes,
        have : z ≠ 0 := by linarith,
        field_simp [norm, abs, max_eq_left_of_lt (show -z < z, by linarith), pow_two, mul_inv'],
        calc
          1 / z = 1 * (1 / z)           : (one_mul (1 / z)).symm
            ... = (z / z) * (1 / z)     : congr_arg (λ x, x * (1 / z)) (div_self this).symm
            ... = z / (z * z)           : by field_simp },
    end,
  div_I_ax := λ z, by simp only [div_zero, mul_zero, neg_zero]}

noncomputable instance : is_R_or_C ℂ :=
{ re := ⟨complex.re, complex.zero_re, complex.add_re⟩,
  im := ⟨complex.im, complex.zero_im, complex.add_im⟩,
  conj := ⟨complex.conj, complex.conj.map_one, complex.conj.map_mul, complex.conj.map_zero, complex.conj.map_add⟩,
  I := complex.I,
  I_re_ax := by simp only [add_monoid_hom.coe_mk, complex.I_re],
  I_def_ax := by simp only [complex.I_mul_I, eq_self_iff_true, or_true],
  re_add_im_ax := by simp only [forall_const, add_monoid_hom.coe_mk, complex.re_add_im, eq_self_iff_true],
  smul_coe_mul_ax := λ z r, rfl,
  smul_re_ax := λ r z, by simp [(show r • z = r * z, by refl)],
  smul_im_ax := λ r z, by simp [(show r • z = r * z, by refl)],
  of_real_re_ax := λ r, by simp only [add_monoid_hom.coe_mk, complex.of_real_re],
  of_real_im_ax := λ r, by simp only [add_monoid_hom.coe_mk, complex.of_real_im],
  mul_re_ax := λ z w, by simp only [complex.mul_re, add_monoid_hom.coe_mk],
  mul_im_ax := λ z w, by simp only [add_monoid_hom.coe_mk, complex.mul_im],
  conj_re_ax := λ z, by simp only [ring_hom.coe_mk, add_monoid_hom.coe_mk, complex.conj_re],
  conj_im_ax := λ z, by simp only [ring_hom.coe_mk, complex.conj_im, add_monoid_hom.coe_mk],
  conj_I_ax := by simp only [complex.conj_I, ring_hom.coe_mk],
  eq_conj_iff_real_ax := λ z,
    begin
      split,
      { simp,
        intro h,
        refine ⟨z.re,_⟩,
        ext z,
        { simp only [complex.of_real_re]},
        { sorry } },
      { rintros ⟨r,rfl⟩,
        exact complex.conj_of_real r }
    end,
  norm_sq_eq_def := λ z, begin
    sorry,
  end,
  mul_im_I_ax := λ z, by simp only [mul_one, add_monoid_hom.coe_mk, complex.I_im],
  inv_def := λ z,
    begin
      dsimp,
      convert complex.inv_def z,
      rw [complex.norm_sq, complex.abs],
      sorry,
    end,
  div_I_ax := complex.div_I,
}

namespace is_R_or_C

variables {K : Type*} [normed_field K] [algebra ℝ K] [has_coe ℝ K] [decidable_eq K] [is_R_or_C K]

lemma coe_alg : ∀ x : ℝ, (x : K) = x • (1 : K) :=
  λ x, by rw [←mul_one (x : K), smul_coe_mul_ax]

@[simp] lemma re_add_im (z : K) : (re z : K) + (im z) * I = z := is_R_or_C.re_add_im_ax z
@[simp] lemma of_real_re : ∀ r : ℝ, re (r : K) = r := is_R_or_C.of_real_re_ax
@[simp] lemma of_real_im : ∀ r : ℝ, im (r : K) = 0 := is_R_or_C.of_real_im_ax
@[simp] lemma mul_re : ∀ z w : K, re (z * w) = re z * re w - im z * im w :=
  is_R_or_C.mul_re_ax
@[simp] lemma mul_im : ∀ z w : K, im (z * w) = re z * im w + im z * re w :=
  is_R_or_C.mul_im_ax
@[simp] lemma I_re : re (I : K) = 0 := I_re_ax

theorem ext_iff : ∀ {z w : K}, z = w ↔ re z = re w ∧ im z = im w :=
begin
  intros z w,
  split,
  { intro h,
    simp [h] },
  { rintro ⟨h₁,h₂⟩,
    rw [←re_add_im z, ←re_add_im w, h₁, h₂] }
end

theorem ext : ∀ {z w : K}, re z = re w → im z = im w → z = w :=
  λ z w hre him, is_R_or_C.ext_iff.mpr ⟨hre, him⟩


@[simp] lemma zero_re : re (0 : K) = (0 : ℝ) :=
  by rw [←@of_real_re K _ _ _ _ _ 0, coe_alg, zero_smul]
@[simp] lemma zero_im : im (0 : K) = 0 :=
  by rw [←@of_real_im K _ _ _ _ _  0, coe_alg, zero_smul]
@[simp, norm_cast] lemma of_real_zero : ((0 : ℝ) : K) = 0 :=
  by rw [coe_alg, zero_smul]

@[simp] lemma one_re : re (1 : K) = (1 : ℝ) :=
  by rw [←@of_real_re K _ _ _ _ _ 1, coe_alg, one_smul]
@[simp] lemma one_im : im (1 : K) = (0 : ℝ) :=
  by rw [←@of_real_im K _ _ _ _ _ 1, coe_alg, one_smul]
@[simp, norm_cast] lemma of_real_one : ((1 : ℝ) : K) = 1 :=
  by rw [coe_alg, one_smul]

@[simp, norm_cast] theorem of_real_inj {z w : ℝ} : (z : K) = w ↔ z = w :=
begin
  split,
  { intro h,
    have := congr_arg re h,
    simp only [of_real_re] at this,
    exact this },
  { intro h,
    simp only [h] }
end

@[simp] lemma bit0_re (z : K) : re (bit0 z) = bit0 (re z) := by simp [bit0]
@[simp] lemma bit1_re (z : K) : re (bit1 z) = bit1 (re z) := by simp [bit1]
@[simp] lemma bit0_im (z : K) : im (bit0 z) = bit0 (im z) := by simp [bit0]
@[simp] lemma bit1_im (z : K) : im (bit1 z) = bit0 (im z) := by simp [bit1]

@[simp] theorem of_real_eq_zero {z : ℝ} : (z : K) = 0 ↔ z = 0 :=
begin
  rw [←of_real_zero],
  apply @of_real_inj K _ _ _ _ _ z 0
end

@[simp, norm_cast] lemma of_real_add (r s : ℝ) : ((r + s : ℝ) : K) = r + s :=
begin
  apply (@is_R_or_C.ext_iff K _ _ _ _ _ ((r + s : ℝ) : K) (r + s)).mpr,
  simp,
end

@[simp, norm_cast] lemma of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : K) = bit0 r :=
ext_iff.2 $ by simp [bit0]

@[simp, norm_cast] lemma of_real_bit1 (r : ℝ) : ((bit1 r : ℝ) : K) = bit1 r :=
ext_iff.2 $ by simp [bit1]

@[simp, norm_cast] lemma of_real_neg (r : ℝ) : ((-r : ℝ) : K) = -r := ext_iff.2 $ by simp
@[simp, norm_cast] lemma of_real_mul (r s : ℝ) : ((r * s : ℝ) : K) = r * s := ext_iff.2 $ by simp

@[simp] lemma conj_re (z : K) : re (conj z) = re z := is_R_or_C.conj_re_ax z
@[simp] lemma conj_im (z : K) : im (conj z) = -(im z) := is_R_or_C.conj_im_ax z
@[simp] lemma conj_of_real (r : ℝ) : conj (r : K) = r :=
  (@is_R_or_C.ext_iff K _ _ _ _ _ (conj (r : K)) r).mpr $ by simp

@[simp] lemma conj_neg_I : conj (-I) = (I : K) := ext_iff.2 $ by simp
@[simp] lemma conj_conj (z : K) : conj (conj z) = z := ext_iff.2 $ by simp

lemma conj_involutive : @function.involutive K is_R_or_C.conj := conj_conj
lemma conj_bijective : @function.bijective K K is_R_or_C.conj := conj_involutive.bijective

lemma conj_inj {z w : K} : conj z = conj w ↔ z = w := conj_bijective.1.eq_iff

@[simp] lemma conj_eq_zero {z : K} : conj z = 0 ↔ z = 0 :=
  by simpa using @conj_inj K _ _ _ _ _ z 0

lemma eq_conj_iff_real {z : K} : conj z = z ↔ ∃ r : ℝ, z = r := is_R_or_C.eq_conj_iff_real_ax

lemma eq_conj_iff_re {z : K} : conj z = z ↔ (re z : K) = z :=
eq_conj_iff_real.trans ⟨by rintro ⟨r, rfl⟩; simp, λ h, ⟨_, h.symm⟩⟩

/-- The norm squared function. -/
def norm_sq (z : K) : ℝ := re z * re z + im z * im z

@[simp] lemma norm_sq_of_real (r : ℝ) : ∥(r : K)∥^2 = r * r :=
by simp [norm_sq_eq_def]

@[simp] lemma norm_sq_zero : norm_sq (0 : K) = 0 := by simp[norm_sq, pow_two]
@[simp] lemma norm_sq_one : norm_sq (1 : K) = 1 := by simp [norm_sq]

lemma norm_sq_nonneg (z : K) : 0 ≤ norm_sq z :=
add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

@[simp] lemma norm_sq_eq_zero {z : K} : norm_sq z = 0 ↔ z = 0 :=
begin
  rw [norm_sq, ←norm_sq_eq_def],
  split,
  { intro h,
    rw [pow_two] at h,
    exact norm_eq_zero.mp (mul_self_eq_zero.mp h) },
  { rintro rfl,
    simp[pow_two], }
end

@[simp] lemma norm_sq_pos {z : K} : 0 < norm_sq z ↔ z ≠ 0 :=
by rw [lt_iff_le_and_ne, ne, eq_comm]; simp [norm_sq_nonneg]

@[simp] lemma norm_sq_neg (z : K) : norm_sq (-z) = norm_sq z :=
by simp [norm_sq]

@[simp] lemma norm_sq_conj (z : K) : norm_sq (conj z) = norm_sq z := by simp [norm_sq]

@[simp] lemma norm_sq_mul (z w : K) : norm_sq (z * w) = norm_sq z * norm_sq w :=
  by simp [norm_sq, pow_two]; ring

lemma norm_sq_add (z w : K) : norm_sq (z + w) =
  norm_sq z + norm_sq w + 2 * (re (z * conj w)) :=
  by simp [norm_sq, pow_two]; ring

lemma re_sq_le_norm_sq (z : K) : re z * re z ≤ norm_sq z :=
le_add_of_nonneg_right (mul_self_nonneg _)

lemma im_sq_le_norm_sq (z : K) : im z * im z ≤ norm_sq z :=
le_add_of_nonneg_left (mul_self_nonneg _)

theorem mul_conj (z : K) : z * conj z = norm_sq z :=
ext_iff.2 $ by simp [norm_sq, mul_comm, sub_eq_neg_add, add_comm]

theorem add_conj (z : K) : z + conj z = (2 * re z : ℝ) :=
ext_iff.2 $ by simp [two_mul]

/-- The coercion `ℝ → K` as a `ring_hom`. -/
def of_real : ℝ →+* K := ⟨coe, of_real_one, of_real_mul, of_real_zero, of_real_add⟩

@[simp] lemma of_real_eq_coe (r : ℝ) : @is_R_or_C.of_real K _ _ _ _ _ r = r := rfl
@[simp, norm_cast] lemma of_real_sub (r s : ℝ) : ((r - s : ℝ) : K) = r - s := ext_iff.2 $ by simp
@[simp, norm_cast] lemma of_real_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : K) = r ^ n :=
by induction n; simp [*, of_real_mul, pow_succ]

theorem sub_conj (z : K) : z - conj z = (2 * im z : ℝ) * I :=
begin
  refine ext_iff.2 _,
  simp [two_mul, sub_eq_add_neg, add_mul, mul_im_I_ax],
end

lemma norm_sq_sub (z w : K) : norm_sq (z - w) =
  norm_sq z + norm_sq w - 2 * re (z * conj w) :=
by rw [sub_eq_add_neg, norm_sq_add]; simp [-mul_re, add_comm, add_left_comm, sub_eq_add_neg]

@[simp] lemma inv_re (z : K) : re (z⁻¹) = re z / norm_sq z :=
  by simp [@is_R_or_C.inv_def K _ _ _ _ _, norm_sq_eq_def, norm_sq, division_def]
@[simp] lemma inv_im (z : K) : im (z⁻¹) = im (-z) / norm_sq z :=
  by simp [@is_R_or_C.inv_def K _ _ _ _ _, norm_sq_eq_def, norm_sq, division_def]

@[simp, norm_cast] lemma of_real_inv (r : ℝ) : ((r⁻¹ : ℝ) : K) = r⁻¹ :=
ext_iff.2 $ begin
  simp,
  by_cases r = 0, { simp [h] },
  { simp [norm_sq],
    rw [← div_div_eq_div_mul, div_self h, one_div] },
end

lemma div_re (z w : K) : re (z / w) = re z * re w / norm_sq w + im z * im w / norm_sq w :=
by simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg]
lemma div_im (z w : K) : im (z / w) = im z * re w / norm_sq w - re z * im w / norm_sq w :=
by simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm]

@[simp, norm_cast] lemma of_real_div (r s : ℝ) : ((r / s : ℝ) : K) = r / s :=
(@is_R_or_C.of_real K _ _ _ _ _).map_div r s

@[simp, norm_cast] lemma of_real_fpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : K) = (r : K) ^ n :=
(@is_R_or_C.of_real K _ _ _ _ _).map_fpow r n

@[simp] lemma inv_I : (I : K)⁻¹ = -I :=
begin
  rcases (@I_def_ax K _ _ _ _ _) with h₁|h₂,
  { simp [h₁] },
  { by_cases h : (I : K) = 0,
    { simp [h] },
    { rw [inv_eq_one_div],
      field_simp [h, h₂] } }
end
--by simp [inv_eq_one_div]

@[simp] lemma norm_sq_inv (z : K) : norm_sq z⁻¹ = (norm_sq z)⁻¹ :=
if h : z = 0 then by simp [h] else
mul_right_cancel' (mt norm_sq_eq_zero.1 h) $
by rw [← norm_sq_mul]; simp [h, -norm_sq_mul]

@[simp] lemma norm_sq_div (z w : K) : norm_sq (z / w) = norm_sq z / norm_sq w :=
by rw [division_def, norm_sq_mul, norm_sq_inv]; refl

/-! ### Cast lemmas -/

@[simp, norm_cast] theorem of_real_nat_cast (n : ℕ) : ((n : ℝ) : K) = n :=
of_real.map_nat_cast n

@[simp, norm_cast] lemma nat_cast_re (n : ℕ) : re (n : K) = n :=
by rw [← of_real_nat_cast, of_real_re]

@[simp, norm_cast] lemma nat_cast_im (n : ℕ) : im (n : K) = 0 :=
by rw [← of_real_nat_cast, of_real_im]

@[simp, norm_cast] theorem of_real_int_cast (n : ℤ) : ((n : ℝ) : K) = n :=
of_real.map_int_cast n

@[simp, norm_cast] lemma int_cast_re (n : ℤ) : re (n : K) = n :=
by rw [← of_real_int_cast, of_real_re]

@[simp, norm_cast] lemma int_cast_im (n : ℤ) : im (n : K) = 0 :=
by rw [← of_real_int_cast, of_real_im]

@[simp, norm_cast] theorem of_real_rat_cast (n : ℚ) : ((n : ℝ) : K) = n :=
(@is_R_or_C.of_real K _ _ _ _ _).map_rat_cast n

@[simp, norm_cast] lemma rat_cast_re (q : ℚ) : re (q : K) = q :=
by rw [← of_real_rat_cast, of_real_re]

@[simp, norm_cast] lemma rat_cast_im (q : ℚ) : im (q : K) = 0 :=
by rw [← of_real_rat_cast, of_real_im]

/-! ### Characteristic zero -/

instance char_zero_R_or_C : char_zero K :=
add_group.char_zero_of_inj_zero $ λ n h,
by rwa [← of_real_nat_cast, of_real_eq_zero, nat.cast_eq_zero] at h

theorem re_eq_add_conj (z : K) : (re z : K) = (z + conj z) / 2 :=
by rw [add_conj]; simp; rw [mul_div_cancel_left (re z : K) two_ne_zero']


/-! ### Absolute value -/

/-- The complex absolute value function, defined as the square root of the norm squared. -/

@[pp_nodot] noncomputable def abs (z : K) : ℝ := (norm_sq z).sqrt

local notation `abs'` := _root_.abs
local notation `absK` := @abs K _ _ _ _ _

@[simp] lemma abs_of_real (r : ℝ) : absK r = abs' r :=
by simp [abs, norm_sq, norm_sq_of_real, real.sqrt_mul_self_eq_abs]

lemma abs_of_nonneg {r : ℝ} (h : 0 ≤ r) : absK r = r :=
(abs_of_real _).trans (abs_of_nonneg h)

lemma abs_of_nat (n : ℕ) : absK n = n :=
calc absK n = absK (n:ℝ) : by rw [of_real_nat_cast]
  ... = _ : abs_of_nonneg (nat.cast_nonneg n)

lemma mul_self_abs (z : K) : abs z * abs z = norm_sq z :=
real.mul_self_sqrt (norm_sq_nonneg _)

@[simp] lemma abs_zero : absK 0 = 0 := by simp [abs]
@[simp] lemma abs_one : absK 1 = 1 := by simp [abs]

@[simp] lemma abs_two : absK 2 = 2 :=
calc absK 2 = absK (2 : ℝ) : by rw [of_real_bit0, of_real_one]
... = (2 : ℝ) : abs_of_nonneg (by norm_num)

lemma abs_nonneg (z : K) : 0 ≤ absK z :=
real.sqrt_nonneg _

@[simp] lemma abs_eq_zero {z : K} : absK z = 0 ↔ z = 0 :=
(real.sqrt_eq_zero $ norm_sq_nonneg _).trans norm_sq_eq_zero

lemma abs_ne_zero {z : K} : abs z ≠ 0 ↔ z ≠ 0 :=
not_congr abs_eq_zero

@[simp] lemma abs_conj (z : K) : abs (conj z) = abs z :=
by simp [abs]

@[simp] lemma abs_mul (z w : K) : abs (z * w) = abs z * abs w :=
by rw [abs, norm_sq_mul, real.sqrt_mul (norm_sq_nonneg _)]; refl

lemma abs_re_le_abs (z : K) : abs' (re z) ≤ abs z :=
by rw [mul_self_le_mul_self_iff (_root_.abs_nonneg (re z)) (abs_nonneg _),
       abs_mul_abs_self, mul_self_abs];
   apply re_sq_le_norm_sq

lemma abs_im_le_abs (z : K) : abs' (im z) ≤ abs z :=
by rw [mul_self_le_mul_self_iff (_root_.abs_nonneg (im z)) (abs_nonneg _),
       abs_mul_abs_self, mul_self_abs];
   apply im_sq_le_norm_sq

lemma re_le_abs (z : K) : re z ≤ abs z :=
(abs_le.1 (abs_re_le_abs _)).2

lemma im_le_abs (z : K) : im z ≤ abs z :=
(abs_le.1 (abs_im_le_abs _)).2

lemma abs_add (z w : K) : abs (z + w) ≤ abs z + abs w :=
(mul_self_le_mul_self_iff (abs_nonneg _)
  (add_nonneg (abs_nonneg _) (abs_nonneg _))).2 $
begin
  rw [mul_self_abs, add_mul_self_eq, mul_self_abs, mul_self_abs,
      add_right_comm, norm_sq_add, add_le_add_iff_left,
      mul_assoc, mul_le_mul_left (@two_pos ℝ _)],
  simpa [-mul_re] using re_le_abs (z * conj w)
end

instance : is_absolute_value absK :=
{ abv_nonneg  := abs_nonneg,
  abv_eq_zero := λ _, abs_eq_zero,
  abv_add     := abs_add,
  abv_mul     := abs_mul }
open is_absolute_value

@[simp] lemma abs_abs (z : K) : abs' (abs z) = abs z :=
_root_.abs_of_nonneg (abs_nonneg _)

@[simp] lemma abs_pos {z : K} : 0 < abs z ↔ z ≠ 0 := abv_pos abs
@[simp] lemma abs_neg : ∀ z : K, abs (-z) = abs z := abv_neg abs
lemma abs_sub : ∀ z w : K, abs (z - w) = abs (w - z) := abv_sub abs
lemma abs_sub_le : ∀ a b c : K, abs (a - c) ≤ abs (a - b) + abs (b - c) := abv_sub_le abs
@[simp] theorem abs_inv : ∀ z : K, abs z⁻¹ = (abs z)⁻¹ := abv_inv abs
@[simp] theorem abs_div : ∀ z w : K, abs (z / w) = abs z / abs w := abv_div abs

lemma abs_abs_sub_le_abs_sub : ∀ z w : K, abs' (abs z - abs w) ≤ abs (z - w) :=
abs_abv_sub_le_abv_sub abs

lemma abs_re_div_abs_le_one (z : K) : abs' (re z / abs z) ≤ 1 :=
if hz : z = 0 then by simp [hz, zero_le_one]
else by { simp_rw [_root_.abs_div, abs_abs, div_le_iff (abs_pos.2 hz), one_mul, abs_re_le_abs] }

lemma abs_im_div_abs_le_one (z : K) : abs' (im z / abs z) ≤ 1 :=
if hz : z = 0 then by simp [hz, zero_le_one]
else by { simp_rw [_root_.abs_div, abs_abs, div_le_iff (abs_pos.2 hz), one_mul, abs_im_le_abs] }

@[simp, norm_cast] lemma abs_cast_nat (n : ℕ) : abs (n : K) = n :=
by rw [← of_real_nat_cast, abs_of_nonneg (nat.cast_nonneg n)]

lemma norm_sq_eq_abs (x : K) : norm_sq x = abs x ^ 2 :=
by rw [abs, pow_two, real.mul_self_sqrt (norm_sq_nonneg _)]


/-! ### Cauchy sequences -/

theorem is_cau_seq_re (f : cau_seq K abs) : is_cau_seq abs' (λ n, re (f n)) :=
λ ε ε0, (f.cauchy ε0).imp $ λ i H j ij,
lt_of_le_of_lt (by simpa using abs_re_le_abs (f j - f i)) (H _ ij)

theorem is_cau_seq_im (f : cau_seq K abs) : is_cau_seq abs' (λ n, im (f n)) :=
λ ε ε0, (f.cauchy ε0).imp $ λ i H j ij,
lt_of_le_of_lt (by simpa using abs_im_le_abs (f j - f i)) (H _ ij)

/-- The real part of a K Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cau_seq_re (f : cau_seq K abs) : cau_seq ℝ abs' :=
⟨_, is_cau_seq_re f⟩

/-- The imaginary part of a K Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cau_seq_im (f : cau_seq K abs) : cau_seq ℝ abs' :=
⟨_, is_cau_seq_im f⟩

lemma is_cau_seq_abs {f : ℕ → K} (hf : is_cau_seq abs f) :
  is_cau_seq abs' (abs ∘ f) :=
λ ε ε0, let ⟨i, hi⟩ := hf ε ε0 in
⟨i, λ j hj, lt_of_le_of_lt (abs_abs_sub_le_abs_sub _ _) (hi j hj)⟩

end is_R_or_C

/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import analysis.normed_space.basic
import analysis.complex.basic

/-!
# `is_R_or_C`: a typeclass for ℝ or ℂ

This file defines the typeclass `is_R_or_C` intended to have only two instances:
ℝ and ℂ. It is meant for definitions and theorems which hold for both the real and the complex case,
and in particular when the real case follows directly from the complex case by setting `re` to `id`,
`im` to zero and so on. Its API follows closely that of ℂ.

Possible applications include defining inner products and Hilbert spaces for both the real and
complex case. One would produce the definitions and proof for an arbitrary field of this
typeclass, which basically amounts to doing the complex case, and the two cases then fall out
immediately from the two instances of the class.
-/

/--
This typeclass captures properties shared by ℝ and ℂ, with an API that closely matches that of ℂ.
-/
class is_R_or_C (K : Type*) extends nondiscrete_normed_field K, normed_algebra ℝ K, complete_space K :=
(re : K →+ ℝ)
(im : K →+ ℝ)
(conj : K →+* K)
(I : K)                 -- Meant to be set to 0 for K=ℝ
(of_real : ℝ → K)      -- Meant to be id for K=ℝ and the coercion from ℝ for K=ℂ
(I_re_ax : re I = 0)
(I_mul_I_ax : I = 0 ∨ I * I = -1)
(re_add_im_ax : ∀ (z : K), of_real (re z) + of_real (im z) * I = z)
(smul_coe_mul_ax : ∀ (z : K) (r : ℝ), r • z = of_real r * z)
(of_real_re_ax : ∀ r : ℝ, re (of_real r) = r)
(of_real_im_ax : ∀ r : ℝ, im (of_real r) = 0)
(mul_re_ax : ∀ z w : K, re (z * w) = re z * re w - im z * im w)
(mul_im_ax : ∀ z w : K, im (z * w) = re z * im w + im z * re w)
(conj_re_ax : ∀ z : K, re (conj z) = re z)
(conj_im_ax : ∀ z : K, im (conj z) = -(im z))
(conj_I_ax : conj I = -I)
(norm_sq_eq_def_ax : ∀ (z : K), ∥z∥^2 = (re z) * (re z) + (im z) * (im z))
(mul_im_I_ax : ∀ (z : K), (im z) * im I = im z)
(inv_def_ax : ∀ (z : K), z⁻¹ = conj z * of_real ((∥z∥^2)⁻¹))
(div_I_ax : ∀ (z : K), z / I = -(z * I))

namespace is_R_or_C

variables {K : Type*} [is_R_or_C K]
local notation `𝓚` := @is_R_or_C.of_real K _
local postfix `†`:100 := @is_R_or_C.conj K _

lemma of_real_alg : ∀ x : ℝ, 𝓚 x = x • (1 : K) :=
λ x, by rw [←mul_one (𝓚 x), smul_coe_mul_ax]

@[simp] lemma re_add_im (z : K) : 𝓚 (re z) + 𝓚 (im z) * I = z := is_R_or_C.re_add_im_ax z
@[simp] lemma of_real_re : ∀ r : ℝ, re (𝓚 r) = r := is_R_or_C.of_real_re_ax
@[simp] lemma of_real_im : ∀ r : ℝ, im (𝓚 r) = 0 := is_R_or_C.of_real_im_ax
@[simp] lemma mul_re : ∀ z w : K, re (z * w) = re z * re w - im z * im w :=
is_R_or_C.mul_re_ax
@[simp] lemma mul_im : ∀ z w : K, im (z * w) = re z * im w + im z * re w :=
is_R_or_C.mul_im_ax

lemma inv_def {z : K} : z⁻¹ = conj z * of_real ((∥z∥^2)⁻¹) := is_R_or_C.inv_def_ax z

theorem ext_iff : ∀ {z w : K}, z = w ↔ re z = re w ∧ im z = im w :=
λ z w, { mp := by { rintro rfl, cc },
         mpr := by { rintro ⟨h₁,h₂⟩, rw [←re_add_im z, ←re_add_im w, h₁, h₂] } }

theorem ext : ∀ {z w : K}, re z = re w → im z = im w → z = w :=
by { simp_rw ext_iff, cc }


@[simp] lemma zero_re : re (𝓚 0) = (0 : ℝ) := by simp only [of_real_re]
@[simp] lemma zero_im : im (𝓚 0) = 0 := by rw [of_real_im]
lemma of_real_zero : 𝓚 0 = 0 := by rw [of_real_alg, zero_smul]

@[simp] lemma zero_re' : re (0 : K) = (0 : ℝ) :=
by simp only [add_monoid_hom.map_zero]


@[simp] lemma of_real_one : 𝓚 1 = 1 := by rw [of_real_alg, one_smul]
@[simp] lemma one_re : re (1 : K) = 1 := by rw [←of_real_one, of_real_re]
@[simp] lemma one_im : im (1 : K) = 0 := by rw [←of_real_one, of_real_im]

@[simp] theorem of_real_inj {z w : ℝ} : 𝓚 z = 𝓚 w ↔ z = w :=
{ mp := λ h, by { convert congr_arg re h; simp only [of_real_re] },
  mpr := λ h, by rw h }


@[simp] lemma bit0_re (z : K) : re (bit0 z) = bit0 (re z) := by simp [bit0]
@[simp] lemma bit1_re (z : K) : re (bit1 z) = bit1 (re z) :=
by simp only [bit1, add_monoid_hom.map_add, bit0_re, add_right_inj, one_re]
@[simp] lemma bit0_im (z : K) : im (bit0 z) = bit0 (im z) := by simp [bit0]
@[simp] lemma bit1_im (z : K) : im (bit1 z) = bit0 (im z) :=
by simp only [bit1, add_right_eq_self, add_monoid_hom.map_add, bit0_im, one_im]

@[simp] theorem of_real_eq_zero {z : ℝ} : 𝓚 z = 0 ↔ z = 0 :=
by rw [←of_real_zero]; exact of_real_inj

@[simp] lemma of_real_add ⦃r s : ℝ⦄ : 𝓚 (r + s) = 𝓚 r + 𝓚 s :=
by apply (@is_R_or_C.ext_iff K _ (𝓚 (r + s)) (𝓚 r + 𝓚 s)).mpr; simp

@[simp] lemma of_real_bit0 (r : ℝ) : 𝓚 (bit0 r : ℝ) = bit0 (𝓚 r) :=
ext_iff.2 $ by simp [bit0]

@[simp] lemma of_real_bit1 (r : ℝ) : 𝓚 (bit1 r : ℝ) = bit1 (𝓚 r) :=
ext_iff.2 $ by simp [bit1]

/- Note: This can be proven by `norm_num` once K is proven to be of characteristic zero below. -/
lemma two_ne_zero : (2 : K) ≠ 0 :=
begin
  intro h, rw [(show (2 : K) = 𝓚 2, by norm_num), ←of_real_zero, of_real_inj] at h,
  linarith,
end

@[simp] lemma of_real_neg (r : ℝ) : 𝓚 (-r) = -(𝓚 r) := ext_iff.2 $ by simp
@[simp] lemma of_real_mul (r s : ℝ) : 𝓚 (r * s) = (𝓚 r) * (𝓚 s) := ext_iff.2 $ by simp
lemma of_real_mul_re (r : ℝ) (z : K) : re ((𝓚 r) * z) = r * re z :=
by simp only [mul_re, of_real_im, zero_mul, of_real_re, sub_zero]

lemma smul_re (r : ℝ) (z : K) : re ((𝓚 r) * z) = r * (re z) :=
by simp only [of_real_im, zero_mul, of_real_re, sub_zero, mul_re]
lemma smul_im (r : ℝ) (z : K) : im ((𝓚 r) * z) = r * (im z) :=
by simp only [add_zero, of_real_im, zero_mul, of_real_re, mul_im]

lemma smul_re' : ∀ (r : ℝ) (z : K), re (r • z) = r * (re z) :=
λ r z, by { rw [smul_coe_mul_ax], apply smul_re }
lemma smul_im' : ∀ (r : ℝ) (z : K), im (r • z) = r * (im z) :=
λ r z, by { rw [smul_coe_mul_ax], apply smul_im }

/-! ### The imaginary unit, `I` -/

/-- The imaginary unit. -/
@[simp] lemma I_re : re (I : K) = 0 := I_re_ax
@[simp] lemma I_im (z : K) : im z * im (I : K) = im z := mul_im_I_ax z
@[simp] lemma I_im' (z : K) : im (I : K) * im z = im z :=
by rw [mul_comm, I_im _]

lemma I_mul_I : (I : K) = 0 ∨ (I : K) * I = -1 := I_mul_I_ax

@[simp] lemma conj_re (z : K) : re (conj z) = re z := is_R_or_C.conj_re_ax z
@[simp] lemma conj_im (z : K) : im (conj z) = -(im z) := is_R_or_C.conj_im_ax z
@[simp] lemma conj_of_real (r : ℝ) : conj (𝓚 r) = (𝓚 r) :=
by { rw ext_iff, simp only [of_real_im, conj_im, eq_self_iff_true, conj_re, and_self, neg_zero] }


@[simp] lemma conj_bit0 (z : K) : conj (bit0 z) = bit0 (conj z) := by simp [bit0, ext_iff]
@[simp] lemma conj_bit1 (z : K) : conj (bit1 z) = bit1 (conj z) := by simp [bit0, ext_iff]

@[simp] lemma conj_neg_I : conj (-I) = (I : K) := by simp [ext_iff]

@[simp] lemma conj_conj (z : K) : conj (conj z) = z := by simp [ext_iff]

lemma conj_involutive : @function.involutive K is_R_or_C.conj := conj_conj
lemma conj_bijective : @function.bijective K K is_R_or_C.conj := conj_involutive.bijective

lemma conj_inj (z w : K) : conj z = conj w ↔ z = w := conj_bijective.1.eq_iff

@[simp] lemma conj_eq_zero {z : K} : conj z = 0 ↔ z = 0 :=
by simpa using @conj_inj K _ z 0

lemma eq_conj_iff_real {z : K} : conj z = z ↔ ∃ r : ℝ, z = (𝓚 r) :=
begin
  split,
  { intro h,
    suffices : im z = 0,
    { use (re z),
      rw ← add_zero (of_real _),
      convert (re_add_im z).symm, simp [this] },
    contrapose! h,
    rw ← re_add_im z,
    simp only [conj_of_real, ring_hom.map_add, ring_hom.map_mul, conj_I_ax],
    rw [add_left_cancel_iff, ext_iff],
    simpa [neg_eq_iff_add_eq_zero, add_self_eq_zero] },
  { rintros ⟨r, rfl⟩, apply conj_of_real }
end

/-- Conjugation as a ring equivalence. This is used to convert the inner product into a
sesquilinear product. -/
def conj_to_ring_equiv : K ≃+* Kᵒᵖ :=
{ to_fun := opposite.op ∘ conj,
  inv_fun := conj ∘ opposite.unop,
  left_inv := λ x, by simp only [conj_conj, function.comp_app, opposite.unop_op],
  right_inv := λ x, by simp only [conj_conj, opposite.op_unop, function.comp_app],
  map_mul' := λ x y, by simp [mul_comm],
  map_add' := λ x y, by simp }

lemma eq_conj_iff_re {z : K} : conj z = z ↔ 𝓚 (re z) = z :=
eq_conj_iff_real.trans ⟨by rintro ⟨r, rfl⟩; simp, λ h, ⟨_, h.symm⟩⟩

/-- The norm squared function. -/
def norm_sq (z : K) : ℝ := re z * re z + im z * im z

lemma norm_sq_eq_def {z : K} : ∥z∥^2 = (re z) * (re z) + (im z) * (im z) := norm_sq_eq_def_ax z
lemma norm_sq_eq_def' (z : K) : norm_sq z = ∥z∥^2 := by rw [norm_sq_eq_def, norm_sq]

@[simp] lemma norm_sq_of_real (r : ℝ) : ∥𝓚 r∥^2 = r * r :=
by simp [norm_sq_eq_def]

@[simp] lemma norm_sq_zero : norm_sq (0 : K) = 0 := by simp [norm_sq, pow_two]
@[simp] lemma norm_sq_one : norm_sq (1 : K) = 1 := by simp [norm_sq]

lemma norm_sq_nonneg (z : K) : 0 ≤ norm_sq z :=
add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

@[simp] lemma norm_sq_eq_zero {z : K} : norm_sq z = 0 ↔ z = 0 :=
by { rw [norm_sq, ←norm_sq_eq_def], simp [pow_two] }

@[simp] lemma norm_sq_pos {z : K} : 0 < norm_sq z ↔ z ≠ 0 :=
by rw [lt_iff_le_and_ne, ne, eq_comm]; simp [norm_sq_nonneg]

@[simp] lemma norm_sq_neg (z : K) : norm_sq (-z) = norm_sq z :=
by simp [norm_sq]

@[simp] lemma norm_sq_conj (z : K) : norm_sq (conj z) = norm_sq z := by simp [norm_sq]

@[simp] lemma norm_sq_mul (z w : K) : norm_sq (z * w) = norm_sq z * norm_sq w :=
by simp [norm_sq, pow_two]; ring

lemma norm_sq_add (z w : K) :
  norm_sq (z + w) = norm_sq z + norm_sq w + 2 * (re (z * conj w)) :=
by simp [norm_sq, pow_two]; ring

lemma re_sq_le_norm_sq (z : K) : re z * re z ≤ norm_sq z :=
le_add_of_nonneg_right (mul_self_nonneg _)

lemma im_sq_le_norm_sq (z : K) : im z * im z ≤ norm_sq z :=
le_add_of_nonneg_left (mul_self_nonneg _)

theorem mul_conj (z : K) : z * conj z = 𝓚 (norm_sq z) :=
by simp [ext_iff, norm_sq, mul_comm, sub_eq_neg_add, add_comm]

theorem add_conj (z : K) : z + conj z = 𝓚 (2 * re z) :=
by simp [ext_iff, two_mul]

/-- The pseudo-coercion `of_real` as a `ring_hom`. -/
def of_real_hom : ℝ →+* K := ⟨of_real, of_real_one, of_real_mul, of_real_zero, of_real_add⟩

@[simp] lemma of_real_sub (r s : ℝ) : 𝓚 (r - s : ℝ) = 𝓚 r - 𝓚 s := ext_iff.2 $ by simp
@[simp] lemma of_real_pow (r : ℝ) (n : ℕ) : 𝓚 (r ^ n : ℝ) = (𝓚 r) ^ n :=
by induction n; simp [*, of_real_mul, pow_succ]

theorem sub_conj (z : K) : z - conj z = 𝓚 (2 * im z) * I :=
by simp [ext_iff, two_mul, sub_eq_add_neg, add_mul, mul_im_I_ax]

lemma norm_sq_sub (z w : K) : norm_sq (z - w) =
  norm_sq z + norm_sq w - 2 * re (z * conj w) :=
by simp [-mul_re, norm_sq_add, add_comm, add_left_comm, sub_eq_add_neg]

lemma sqrt_norm_sq_eq_norm {z : K} : real.sqrt (norm_sq z) = ∥z∥ :=
begin
  have h₁ : (norm_sq z) = ∥z∥^2 := by rw [norm_sq_eq_def, norm_sq],
  have h₂ : ∥z∥ = real.sqrt (∥z∥^2) := eq_comm.mp (real.sqrt_sqr (norm_nonneg z)),
  rw [h₂],
  exact congr_arg real.sqrt h₁
end

/-! ### Inversion -/

@[simp] lemma inv_re (z : K) : re (z⁻¹) = re z / norm_sq z :=
by simp [inv_def, norm_sq_eq_def, norm_sq, division_def]
@[simp] lemma inv_im (z : K) : im (z⁻¹) = im (-z) / norm_sq z :=
by simp [inv_def, norm_sq_eq_def, norm_sq, division_def]

@[simp] lemma of_real_inv (r : ℝ) : 𝓚 (r⁻¹) = (𝓚 r)⁻¹ :=
begin
  rw ext_iff, by_cases r = 0, { simp [h] },
  { simp; field_simp [h, norm_sq] },
end

protected lemma inv_zero : (0⁻¹ : K) = 0 :=
by rw [← of_real_zero, ← of_real_inv, inv_zero]

protected theorem mul_inv_cancel {z : K} (h : z ≠ 0) : z * z⁻¹ = 1 :=
by rw [inv_def, ←mul_assoc, mul_conj, ←of_real_mul, ←norm_sq_eq_def',
      mul_inv_cancel (mt norm_sq_eq_zero.1 h), of_real_one]

lemma div_re (z w : K) : re (z / w) = re z * re w / norm_sq w + im z * im w / norm_sq w :=
by simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg]
lemma div_im (z w : K) : im (z / w) = im z * re w / norm_sq w - re z * im w / norm_sq w :=
by simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm]

@[simp] lemma of_real_div (r s : ℝ) : 𝓚 (r / s : ℝ) = 𝓚 r / 𝓚 s :=
(@is_R_or_C.of_real_hom K _).map_div r s

lemma div_re_of_real {z : K} {r : ℝ} : re (z / (𝓚 r)) = re z / r :=
begin
  by_cases h : r = 0,
  { simp [h, of_real_zero] },
  { change r ≠ 0 at h,
    rw [div_eq_mul_inv, ←of_real_inv, div_eq_mul_inv],
    simp [norm_sq, norm_sq_of_real, div_mul_eq_div_mul_one_div, div_self h] }
end

@[simp] lemma of_real_fpow (r : ℝ) (n : ℤ) : 𝓚 (r ^ n) = (𝓚 r) ^ n :=
(@is_R_or_C.of_real_hom K _).map_fpow r n

lemma I_mul_I_of_nonzero : (I : K) ≠ 0 → (I : K) * I = -1 :=
by { have := I_mul_I_ax, tauto }

@[simp] lemma div_I (z : K) : z / I = -(z * I) :=
begin
  by_cases h : (I : K) = 0,
  { simp [h] },
  { field_simp [h], simp [mul_assoc, I_mul_I_of_nonzero h] }
end

@[simp] lemma inv_I : (I : K)⁻¹ = -I :=
by { by_cases h : (I : K) = 0; field_simp [h] }

@[simp] lemma norm_sq_inv (z : K) : norm_sq z⁻¹ = (norm_sq z)⁻¹ :=
begin
  by_cases z = 0,
  { simp [h] },
  { refine mul_right_cancel' (mt norm_sq_eq_zero.1 h) _,
    simp [h, ←norm_sq_mul], }
end

@[simp] lemma norm_sq_div (z w : K) : norm_sq (z / w) = norm_sq z / norm_sq w :=
by { rw [division_def, norm_sq_mul, norm_sq_inv], refl }

lemma norm_conj {z : K} : ∥conj z∥ = ∥z∥ :=
by simp only [←sqrt_norm_sq_eq_norm, norm_sq_conj]

lemma conj_inv {z : K} : conj (z⁻¹) = (conj z)⁻¹ :=
by simp only [inv_def, norm_conj, ring_hom.map_mul, conj_of_real]

lemma conj_div {z w : K} : conj (z / w) = (conj z) / (conj w) :=
by rw [div_eq_inv_mul, div_eq_inv_mul, ring_hom.map_mul]; simp only [conj_inv]

/-! ### Cast lemmas -/

@[simp] theorem of_real_nat_cast (n : ℕ) : 𝓚 (n : ℝ) = n :=
of_real_hom.map_nat_cast n

@[simp] lemma nat_cast_re (n : ℕ) : re (n : K) = n :=
by rw [← of_real_nat_cast, of_real_re]

@[simp] lemma nat_cast_im (n : ℕ) : im (n : K) = 0 :=
by rw [← of_real_nat_cast, of_real_im]

@[simp] theorem of_real_int_cast (n : ℤ) : 𝓚 (n : ℝ) = n :=
of_real_hom.map_int_cast n

@[simp] lemma int_cast_re (n : ℤ) : re (n : K) = n :=
by rw [← of_real_int_cast, of_real_re]

@[simp] lemma int_cast_im (n : ℤ) : im (n : K) = 0 :=
by rw [← of_real_int_cast, of_real_im]

@[simp] theorem of_real_rat_cast (n : ℚ) : 𝓚 (n : ℝ) = n :=
(@is_R_or_C.of_real_hom K _).map_rat_cast n

@[simp] lemma rat_cast_re (q : ℚ) : re (q : K) = q :=
by rw [← of_real_rat_cast, of_real_re]

@[simp] lemma rat_cast_im (q : ℚ) : im (q : K) = 0 :=
by rw [← of_real_rat_cast, of_real_im]

/-! ### Characteristic zero -/

/--
ℝ and ℂ are both of characteristic zero.

Note: This is not registered as an instance to avoid having multiple instances on ℝ and ℂ.
-/
lemma char_zero_R_or_C : char_zero K :=
add_group.char_zero_of_inj_zero $ λ n h,
by rwa [← of_real_nat_cast, of_real_eq_zero, nat.cast_eq_zero] at h

theorem re_eq_add_conj (z : K) : 𝓚 (re z) = (z + conj z) / 2 :=
by rw [add_conj]; simp; rw [mul_div_cancel_left (𝓚 (re z)) two_ne_zero]


/-! ### Absolute value -/

/-- The complex absolute value function, defined as the square root of the norm squared. -/
@[pp_nodot] noncomputable def abs (z : K) : ℝ := (norm_sq z).sqrt

local notation `abs'` := _root_.abs
local notation `absK` := @abs K _

@[simp] lemma abs_of_real (r : ℝ) : absK (𝓚 r) = abs' r :=
by simp [abs, norm_sq, norm_sq_of_real, real.sqrt_mul_self_eq_abs]

lemma abs_of_nonneg {r : ℝ} (h : 0 ≤ r) : absK (𝓚 r) = r :=
(abs_of_real _).trans (abs_of_nonneg h)

lemma abs_of_nat (n : ℕ) : absK n = n :=
by { rw [← of_real_nat_cast], exact abs_of_nonneg (nat.cast_nonneg n) }

lemma mul_self_abs (z : K) : abs z * abs z = norm_sq z :=
real.mul_self_sqrt (norm_sq_nonneg _)

@[simp] lemma abs_zero : absK 0 = 0 := by simp [abs]
@[simp] lemma abs_one : absK 1 = 1 := by simp [abs]

@[simp] lemma abs_two : absK 2 = 2 :=
calc absK 2 = absK (𝓚 2) : by rw [of_real_bit0, of_real_one]
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
      mul_assoc, mul_le_mul_left (@zero_lt_two ℝ _)],
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
begin
  by_cases hz : z = 0,
  { simp [hz, zero_le_one] },
  { simp_rw [_root_.abs_div, abs_abs, div_le_iff (abs_pos.2 hz), one_mul, abs_re_le_abs] }
end

lemma abs_im_div_abs_le_one (z : K) : abs' (im z / abs z) ≤ 1 :=
begin
  by_cases hz : z = 0,
  { simp [hz, zero_le_one] },
  { simp_rw [_root_.abs_div, abs_abs, div_le_iff (abs_pos.2 hz), one_mul, abs_im_le_abs] }
end

@[simp] lemma abs_cast_nat (n : ℕ) : abs (n : K) = n :=
by rw [← of_real_nat_cast, abs_of_nonneg (nat.cast_nonneg n)]

lemma norm_sq_eq_abs (x : K) : norm_sq x = abs x ^ 2 :=
by rw [abs, pow_two, real.mul_self_sqrt (norm_sq_nonneg _)]

lemma re_eq_abs_of_mul_conj (x : K) : re (x * (conj x)) = abs (x * (conj x)) :=
by rw [mul_conj, of_real_re, abs_of_real, norm_sq_eq_abs, pow_two, _root_.abs_mul, abs_abs]

lemma abs_sqr_re_add_conj (x : K) : (abs (x + x†))^2 = (re (x + x†))^2 :=
by simp [pow_two, ←norm_sq_eq_abs, norm_sq]

lemma abs_sqr_re_add_conj' (x : K) : (abs (x† + x))^2 = (re (x† + x))^2 :=
by simp [pow_two, ←norm_sq_eq_abs, norm_sq]

lemma conj_mul_eq_norm_sq_left (x : K) : x† * x = 𝓚 (norm_sq x) :=
begin
  rw ext_iff,
  refine ⟨by simp [of_real_re, mul_re, conj_re, conj_im, norm_sq],_⟩,
  simp [of_real_im, mul_im, conj_im, conj_re, mul_comm],
end

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

section instances

noncomputable instance real.is_R_or_C : is_R_or_C ℝ :=
{ re := add_monoid_hom.id ℝ,
  im := 0,
  conj := ring_hom.id ℝ,
  I := 0,
  of_real := id,
  I_re_ax := by simp only [add_monoid_hom.map_zero],
  I_mul_I_ax := or.intro_left _ rfl,
  re_add_im_ax := λ z, by unfold_coes; simp [add_zero, id.def, mul_zero],
  smul_coe_mul_ax := λ z r, by simp only [algebra.id.smul_eq_mul, id.def],
  of_real_re_ax := λ r, by simp only [id.def, add_monoid_hom.id_apply],
  of_real_im_ax := λ r, by simp only [add_monoid_hom.zero_apply],
  mul_re_ax := λ z w, by simp only [sub_zero, mul_zero, add_monoid_hom.zero_apply, add_monoid_hom.id_apply],
  mul_im_ax := λ z w, by simp only [add_zero, zero_mul, mul_zero, add_monoid_hom.zero_apply],
  conj_re_ax := λ z, by simp only [ring_hom.id_apply],
  conj_im_ax := λ z, by simp only [neg_zero, add_monoid_hom.zero_apply],
  conj_I_ax := by simp only [ring_hom.map_zero, neg_zero],
  norm_sq_eq_def_ax := λ z, by simp only [pow_two, norm, ←abs_mul, abs_mul_self z, add_zero, mul_zero, add_monoid_hom.zero_apply, add_monoid_hom.id_apply],
  mul_im_I_ax := λ z, by simp only [mul_zero, add_monoid_hom.zero_apply],
  inv_def_ax :=
    begin
      intro z,
      unfold_coes,
      have H : z ≠ 0 → 1 / z = z / (z * z) := λ h,
        calc
          1 / z = 1 * (1 / z)           : (one_mul (1 / z)).symm
            ... = (z / z) * (1 / z)     : congr_arg (λ x, x * (1 / z)) (div_self h).symm
            ... = z / (z * z)           : by field_simp,
      rcases lt_trichotomy z 0 with hlt|heq|hgt,
      { field_simp [norm, abs, max_eq_right_of_lt (show z < -z, by linarith), pow_two, mul_inv', ←H (ne_of_lt hlt)] },
      { simp [heq] },
      { field_simp [norm, abs, max_eq_left_of_lt (show -z < z, by linarith), pow_two, mul_inv', ←H (ne_of_gt hgt)] },
    end,
  div_I_ax := λ z, by simp only [div_zero, mul_zero, neg_zero]}

noncomputable instance complex.is_R_or_C : is_R_or_C ℂ :=
{ re := ⟨complex.re, complex.zero_re, complex.add_re⟩,
  im := ⟨complex.im, complex.zero_im, complex.add_im⟩,
  conj := complex.conj,
  I := complex.I,
  of_real := coe,
  I_re_ax := by simp only [add_monoid_hom.coe_mk, complex.I_re],
  I_mul_I_ax := by simp only [complex.I_mul_I, eq_self_iff_true, or_true],
  re_add_im_ax := by simp only [forall_const, add_monoid_hom.coe_mk, complex.re_add_im, eq_self_iff_true],
  smul_coe_mul_ax := λ z r, rfl,
  of_real_re_ax := λ r, by simp only [add_monoid_hom.coe_mk, complex.of_real_re],
  of_real_im_ax := λ r, by simp only [add_monoid_hom.coe_mk, complex.of_real_im],
  mul_re_ax := λ z w, by simp only [complex.mul_re, add_monoid_hom.coe_mk],
  mul_im_ax := λ z w, by simp only [add_monoid_hom.coe_mk, complex.mul_im],
  conj_re_ax := λ z, by simp only [ring_hom.coe_mk, add_monoid_hom.coe_mk, complex.conj_re],
  conj_im_ax := λ z, by simp only [ring_hom.coe_mk, complex.conj_im, add_monoid_hom.coe_mk],
  conj_I_ax := by simp only [complex.conj_I, ring_hom.coe_mk],
  norm_sq_eq_def_ax := λ z, by simp only [←complex.norm_sq_eq_abs, ←complex.norm_sq, add_monoid_hom.coe_mk, complex.norm_eq_abs],
  mul_im_I_ax := λ z, by simp only [mul_one, add_monoid_hom.coe_mk, complex.I_im],
  inv_def_ax := λ z, by convert complex.inv_def z; exact (complex.norm_sq_eq_abs z).symm,
  div_I_ax := complex.div_I }

end instances

namespace is_R_or_C

section cleanup_lemmas

local notation `reR` := @is_R_or_C.re ℝ _
local notation `imR` := @is_R_or_C.im ℝ _
local notation `conjR` := @is_R_or_C.conj ℝ _
local notation `IR` := @is_R_or_C.I ℝ _
local notation `of_realR` := @is_R_or_C.of_real ℝ _
local notation `absR` := @is_R_or_C.abs ℝ _
local notation `norm_sqR` := @is_R_or_C.norm_sq ℝ _

local notation `reC` := @is_R_or_C.re ℂ _
local notation `imC` := @is_R_or_C.im ℂ _
local notation `conjC` := @is_R_or_C.conj ℂ _
local notation `IC` := @is_R_or_C.I ℂ _
local notation `of_realC` := @is_R_or_C.of_real ℂ _
local notation `absC` := @is_R_or_C.abs ℂ _
local notation `norm_sqC` := @is_R_or_C.norm_sq ℂ _

@[simp] lemma re_to_real {x : ℝ} : reR x = x := rfl
@[simp] lemma im_to_real {x : ℝ} : imR x = 0 := rfl
@[simp] lemma conj_to_real {x : ℝ} : conjR x = x := rfl
@[simp] lemma I_to_real : IR = 0 := rfl
@[simp] lemma of_real_to_real {x : ℝ} : of_realR x = x := rfl
@[simp] lemma norm_sq_to_real {x : ℝ} : norm_sqR x = x*x := by simp [is_R_or_C.norm_sq]
@[simp] lemma abs_to_real {x : ℝ} : absR x = _root_.abs x :=
by simp [is_R_or_C.abs, abs, real.sqrt_mul_self_eq_abs]

@[simp] lemma re_to_complex {x : ℂ} : reC x = x.re := rfl
@[simp] lemma im_to_complex {x : ℂ} : imC x = x.im := rfl
@[simp] lemma conj_to_complex {x : ℂ} : conjC x = x.conj := rfl
@[simp] lemma I_to_complex : IC = complex.I := rfl
@[simp] lemma of_real_to_complex {x : ℝ} : of_realC x = x := rfl
@[simp] lemma norm_sq_to_complex {x : ℂ} : norm_sqC x = complex.norm_sq x :=
by simp [is_R_or_C.norm_sq, complex.norm_sq]
@[simp] lemma abs_to_complex {x : ℂ} : absC x = complex.abs x :=
by simp [is_R_or_C.abs, complex.abs]

end cleanup_lemmas

end is_R_or_C

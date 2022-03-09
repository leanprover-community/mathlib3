/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import data.real.sqrt
import field_theory.tower
import analysis.normed_space.finite_dimension
import analysis.normed_space.star.basic

/-!
# `is_R_or_C`: a typeclass for ℝ or ℂ

This file defines the typeclass `is_R_or_C` intended to have only two instances:
ℝ and ℂ. It is meant for definitions and theorems which hold for both the real and the complex case,
and in particular when the real case follows directly from the complex case by setting `re` to `id`,
`im` to zero and so on. Its API follows closely that of ℂ.

Applications include defining inner products and Hilbert spaces for both the real and
complex case. One typically produces the definitions and proof for an arbitrary field of this
typeclass, which basically amounts to doing the complex case, and the two cases then fall out
immediately from the two instances of the class.

The instance for `ℝ` is registered in this file.
The instance for `ℂ` is declared in `analysis.complex.basic`.

## Implementation notes

The coercion from reals into an `is_R_or_C` field is done by registering `algebra_map ℝ K` as
a `has_coe_t`. For this to work, we must proceed carefully to avoid problems involving circular
coercions in the case `K=ℝ`; in particular, we cannot use the plain `has_coe` and must set
priorities carefully. This problem was already solved for `ℕ`, and we copy the solution detailed
in `data/nat/cast`. See also Note [coercion into rings] for more details.

In addition, several lemmas need to be set at priority 900 to make sure that they do not override
their counterparts in `complex.lean` (which causes linter errors).
-/

open_locale big_operators

section

local notation `𝓚` := algebra_map ℝ _
open_locale complex_conjugate

/--
This typeclass captures properties shared by ℝ and ℂ, with an API that closely matches that of ℂ.
-/
class is_R_or_C (K : Type*)
  extends nondiscrete_normed_field K, star_ring K, normed_algebra ℝ K, complete_space K :=
(re : K →+ ℝ)
(im : K →+ ℝ)
(I : K)                 -- Meant to be set to 0 for K=ℝ
(I_re_ax : re I = 0)
(I_mul_I_ax : I = 0 ∨ I * I = -1)
(re_add_im_ax : ∀ (z : K), 𝓚 (re z) + 𝓚 (im z) * I = z)
(of_real_re_ax : ∀ r : ℝ, re (𝓚 r) = r)
(of_real_im_ax : ∀ r : ℝ, im (𝓚 r) = 0)
(mul_re_ax : ∀ z w : K, re (z * w) = re z * re w - im z * im w)
(mul_im_ax : ∀ z w : K, im (z * w) = re z * im w + im z * re w)
(conj_re_ax : ∀ z : K, re (conj z) = re z)
(conj_im_ax : ∀ z : K, im (conj z) = -(im z))
(conj_I_ax : conj I = -I)
(norm_sq_eq_def_ax : ∀ (z : K), ∥z∥^2 = (re z) * (re z) + (im z) * (im z))
(mul_im_I_ax : ∀ (z : K), (im z) * im I = im z)
(inv_def_ax : ∀ (z : K), z⁻¹ = conj z * 𝓚 ((∥z∥^2)⁻¹))
(div_I_ax : ∀ (z : K), z / I = -(z * I))

end

mk_simp_attribute is_R_or_C_simps "Simp attribute for lemmas about `is_R_or_C`"

variables {K : Type*} [is_R_or_C K]

namespace is_R_or_C

open_locale complex_conjugate

/- The priority must be set at 900 to ensure that coercions are tried in the right order.
See Note [coercion into rings], or `data/nat/cast.lean` for more details. -/
@[priority 900] noncomputable instance algebra_map_coe : has_coe_t ℝ K := ⟨algebra_map ℝ K⟩

lemma of_real_alg (x : ℝ) : (x : K) = x • (1 : K) :=
algebra.algebra_map_eq_smul_one x

lemma algebra_map_eq_of_real : ⇑(algebra_map ℝ K) = coe := rfl

@[simp, is_R_or_C_simps] lemma re_add_im (z : K) : ((re z) : K) + (im z) * I = z :=
is_R_or_C.re_add_im_ax z
@[simp, norm_cast, is_R_or_C_simps] lemma of_real_re : ∀ r : ℝ, re (r : K) = r :=
is_R_or_C.of_real_re_ax
@[simp, norm_cast, is_R_or_C_simps] lemma of_real_im : ∀ r : ℝ, im (r : K) = 0 :=
is_R_or_C.of_real_im_ax
@[simp, is_R_or_C_simps] lemma mul_re : ∀ z w : K, re (z * w) = re z * re w - im z * im w :=
is_R_or_C.mul_re_ax
@[simp, is_R_or_C_simps] lemma mul_im : ∀ z w : K, im (z * w) = re z * im w + im z * re w :=
is_R_or_C.mul_im_ax

theorem inv_def (z : K) : z⁻¹ = conj z * ((∥z∥^2)⁻¹:ℝ) :=
is_R_or_C.inv_def_ax z

theorem ext_iff : ∀ {z w : K}, z = w ↔ re z = re w ∧ im z = im w :=
λ z w, { mp := by { rintro rfl, cc },
         mpr := by { rintro ⟨h₁,h₂⟩, rw [←re_add_im z, ←re_add_im w, h₁, h₂] } }

theorem ext : ∀ {z w : K}, re z = re w → im z = im w → z = w :=
by { simp_rw ext_iff, cc }


@[simp, norm_cast, is_R_or_C_simps, priority 900] lemma of_real_zero : ((0 : ℝ) : K) = 0 :=
by rw [of_real_alg, zero_smul]

@[simp, is_R_or_C_simps] lemma zero_re' : re (0 : K) = (0 : ℝ) := re.map_zero

@[simp, norm_cast, is_R_or_C_simps, priority 900] lemma of_real_one : ((1 : ℝ) : K) = 1 :=
by rw [of_real_alg, one_smul]
@[simp, is_R_or_C_simps] lemma one_re : re (1 : K) = 1 := by rw [←of_real_one, of_real_re]
@[simp, is_R_or_C_simps] lemma one_im : im (1 : K) = 0 := by rw [←of_real_one, of_real_im]

@[simp, norm_cast, priority 900] theorem of_real_inj {z w : ℝ} : (z : K) = (w : K) ↔ z = w :=
{ mp := λ h, by { convert congr_arg re h; simp only [of_real_re] },
  mpr := λ h, by rw h }

@[simp, is_R_or_C_simps] lemma bit0_re (z : K) : re (bit0 z) = bit0 (re z) :=
by simp only [bit0, map_add]
@[simp, is_R_or_C_simps] lemma bit1_re (z : K) : re (bit1 z) = bit1 (re z) :=
by simp only [bit1, add_monoid_hom.map_add, bit0_re, add_right_inj, one_re]
@[simp, is_R_or_C_simps] lemma bit0_im (z : K) : im (bit0 z) = bit0 (im z) :=
by simp only [bit0, map_add]
@[simp, is_R_or_C_simps] lemma bit1_im (z : K) : im (bit1 z) = bit0 (im z) :=
by simp only [bit1, add_right_eq_self, add_monoid_hom.map_add, bit0_im, one_im]

@[simp, is_R_or_C_simps, priority 900]
theorem of_real_eq_zero {z : ℝ} : (z : K) = 0 ↔ z = 0 :=
by rw [←of_real_zero]; exact of_real_inj

@[simp, is_R_or_C_simps, norm_cast, priority 900]
lemma of_real_add ⦃r s : ℝ⦄ : ((r + s : ℝ) : K) = r + s :=
by { apply (@is_R_or_C.ext_iff K _ ((r + s : ℝ) : K) (r + s)).mpr, simp }

@[simp, is_R_or_C_simps, norm_cast, priority 900]
lemma of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : K) = bit0 (r : K) :=
ext_iff.2 $ by simp [bit0]

@[simp, is_R_or_C_simps, norm_cast, priority 900]
lemma of_real_bit1 (r : ℝ) : ((bit1 r : ℝ) : K) = bit1 (r : K) :=
ext_iff.2 $ by simp [bit1]

/- Note: This can be proven by `norm_num` once K is proven to be of characteristic zero below. -/
lemma two_ne_zero : (2 : K) ≠ 0 :=
begin
  intro h, rw [(show (2 : K) = ((2 : ℝ) : K), by norm_num), ←of_real_zero, of_real_inj] at h,
  linarith,
end

@[simp, norm_cast, is_R_or_C_simps, priority 900]
lemma of_real_neg (r : ℝ) : ((-r : ℝ) : K) = -r := ext_iff.2 $ by simp

@[simp, norm_cast, is_R_or_C_simps, priority 900]
lemma of_real_mul (r s : ℝ) : ((r * s : ℝ) : K) = r * s := ext_iff.2 $ by simp with is_R_or_C_simps

@[simp, norm_cast, is_R_or_C_simps]
lemma of_real_smul (r x : ℝ) : r • (x : K) = (r : K) * (x : K) :=
begin
  simp_rw [← smul_eq_mul, of_real_alg r],
  simp only [algebra.id.smul_eq_mul, one_mul, algebra.smul_mul_assoc],
end

@[is_R_or_C_simps] lemma of_real_mul_re (r : ℝ) (z : K) : re (↑r * z) = r * re z :=
by simp only [mul_re, of_real_im, zero_mul, of_real_re, sub_zero]
@[is_R_or_C_simps] lemma of_real_mul_im (r : ℝ) (z : K) : im (↑r * z) = r * (im z) :=
by simp only [add_zero, of_real_im, zero_mul, of_real_re, mul_im]

@[is_R_or_C_simps] lemma smul_re : ∀ (r : ℝ) (z : K), re (r • z) = r * (re z) :=
λ r z, by { rw algebra.smul_def, apply of_real_mul_re }
@[is_R_or_C_simps] lemma smul_im : ∀ (r : ℝ) (z : K), im (r • z) = r * (im z) :=
λ r z, by { rw algebra.smul_def, apply of_real_mul_im }

/-! ### The imaginary unit, `I` -/

/-- The imaginary unit. -/
@[simp, is_R_or_C_simps] lemma I_re : re (I : K) = 0 := I_re_ax
@[simp, is_R_or_C_simps] lemma I_im (z : K) : im z * im (I : K) = im z := mul_im_I_ax z
@[simp, is_R_or_C_simps] lemma I_im' (z : K) : im (I : K) * im z = im z :=
by rw [mul_comm, I_im _]

@[simp, is_R_or_C_simps] lemma I_mul_re (z : K) : re (I * z) = - im z :=
by simp only [I_re, zero_sub, I_im', zero_mul, mul_re]

lemma I_mul_I : (I : K) = 0 ∨ (I : K) * I = -1 := I_mul_I_ax

@[simp, is_R_or_C_simps] lemma conj_re (z : K) : re (conj z) = re z := is_R_or_C.conj_re_ax z
@[simp, is_R_or_C_simps] lemma conj_im (z : K) : im (conj z) = -(im z) := is_R_or_C.conj_im_ax z
@[simp, is_R_or_C_simps] lemma conj_I : conj (I : K) = -I := is_R_or_C.conj_I_ax
@[simp, is_R_or_C_simps] lemma conj_of_real (r : ℝ) : conj (r : K) = (r : K) :=
by { rw ext_iff, simp only [of_real_im, conj_im, eq_self_iff_true, conj_re, and_self, neg_zero] }


@[simp, is_R_or_C_simps] lemma conj_bit0 (z : K) : conj (bit0 z) = bit0 (conj z) :=
by simp only [bit0, ring_hom.map_add, eq_self_iff_true]
@[simp, is_R_or_C_simps] lemma conj_bit1 (z : K) : conj (bit1 z) = bit1 (conj z) :=
by simp only [bit0, ext_iff, bit1_re, conj_im, eq_self_iff_true, conj_re, neg_add_rev,
              and_self, bit1_im]

@[simp, is_R_or_C_simps] lemma conj_neg_I : conj (-I) = (I : K) :=
by simp only [conj_I, ring_hom.map_neg, eq_self_iff_true, neg_neg]

lemma conj_eq_re_sub_im (z : K) : conj z = re z - (im z) * I :=
by { rw ext_iff, simp only [add_zero, I_re, of_real_im, I_im, zero_sub, zero_mul, conj_im,
                            of_real_re, eq_self_iff_true, sub_zero, conj_re, mul_im, neg_inj,
                            and_self, mul_re, mul_zero, map_sub], }

@[is_R_or_C_simps] lemma conj_smul (r : ℝ) (z : K) : conj (r • z) = r • conj z :=
begin
  simp_rw conj_eq_re_sub_im,
  simp only [smul_re, smul_im, of_real_mul],
  rw smul_sub,
  simp_rw of_real_alg,
  simp only [one_mul, algebra.smul_mul_assoc],
end

lemma eq_conj_iff_real {z : K} : conj z = z ↔ ∃ r : ℝ, z = (r : K) :=
begin
  split,
  { intro h,
    suffices : im z = 0,
    { use (re z),
      rw ← add_zero (coe _),
      convert (re_add_im z).symm, simp [this] },
    contrapose! h,
    rw ← re_add_im z,
    simp only [conj_of_real, ring_hom.map_add, ring_hom.map_mul, conj_I_ax],
    rw [add_left_cancel_iff, ext_iff],
    simpa [neg_eq_iff_add_eq_zero, add_self_eq_zero] },
  { rintros ⟨r, rfl⟩, apply conj_of_real }
end

@[simp] lemma star_def : (has_star.star : K → K) = conj := rfl

variables (K)
/-- Conjugation as a ring equivalence. This is used to convert the inner product into a
sesquilinear product. -/
abbreviation conj_to_ring_equiv : K ≃+* Kᵐᵒᵖ := star_ring_equiv

variables {K}

lemma eq_conj_iff_re {z : K} : conj z = z ↔ ((re z) : K) = z :=
eq_conj_iff_real.trans ⟨by rintro ⟨r, rfl⟩; simp, λ h, ⟨_, h.symm⟩⟩

/-- The norm squared function. -/
def norm_sq : K →*₀ ℝ :=
{ to_fun := λ z, re z * re z + im z * im z,
  map_zero' := by simp only [add_zero, mul_zero, map_zero],
  map_one' := by simp only [one_im, add_zero, mul_one, one_re, mul_zero],
  map_mul' := λ z w, by { simp only [mul_im, mul_re], ring } }

lemma norm_sq_eq_def {z : K} : ∥z∥^2 = (re z) * (re z) + (im z) * (im z) := norm_sq_eq_def_ax z
lemma norm_sq_eq_def' (z : K) : norm_sq z = ∥z∥^2 := by { rw norm_sq_eq_def, refl }

@[simp, is_R_or_C_simps] lemma norm_sq_of_real (r : ℝ) : ∥(r : K)∥^2 = r * r :=
by simp only [norm_sq_eq_def, add_zero, mul_zero] with is_R_or_C_simps

@[is_R_or_C_simps] lemma norm_sq_zero : norm_sq (0 : K) = 0 := norm_sq.map_zero
@[is_R_or_C_simps] lemma norm_sq_one : norm_sq (1 : K) = 1 := norm_sq.map_one

lemma norm_sq_nonneg (z : K) : 0 ≤ norm_sq z :=
add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

@[simp, is_R_or_C_simps] lemma norm_sq_eq_zero {z : K} : norm_sq z = 0 ↔ z = 0 :=
by { rw [norm_sq_eq_def'], simp [sq] }

@[simp, is_R_or_C_simps] lemma norm_sq_pos {z : K} : 0 < norm_sq z ↔ z ≠ 0 :=
by rw [lt_iff_le_and_ne, ne, eq_comm]; simp [norm_sq_nonneg]

@[simp, is_R_or_C_simps] lemma norm_sq_neg (z : K) : norm_sq (-z) = norm_sq z :=
by simp only [norm_sq_eq_def', norm_neg]

@[simp, is_R_or_C_simps] lemma norm_sq_conj (z : K) : norm_sq (conj z) = norm_sq z :=
by simp only [norm_sq, neg_mul, monoid_with_zero_hom.coe_mk,
              mul_neg, neg_neg] with is_R_or_C_simps

@[simp, is_R_or_C_simps] lemma norm_sq_mul (z w : K) : norm_sq (z * w) = norm_sq z * norm_sq w :=
norm_sq.map_mul z w

lemma norm_sq_add (z w : K) :
  norm_sq (z + w) = norm_sq z + norm_sq w + 2 * (re (z * conj w)) :=
by { simp only [norm_sq, map_add, monoid_with_zero_hom.coe_mk, mul_neg,
                sub_neg_eq_add] with is_R_or_C_simps, ring }

lemma re_sq_le_norm_sq (z : K) : re z * re z ≤ norm_sq z :=
le_add_of_nonneg_right (mul_self_nonneg _)

lemma im_sq_le_norm_sq (z : K) : im z * im z ≤ norm_sq z :=
le_add_of_nonneg_left (mul_self_nonneg _)

theorem mul_conj (z : K) : z * conj z = ((norm_sq z) : K) :=
by simp only [map_add, add_zero, ext_iff, monoid_with_zero_hom.coe_mk,
              add_left_inj, mul_eq_mul_left_iff, zero_mul, add_comm, true_or, eq_self_iff_true,
              mul_neg, add_right_neg, zero_add, norm_sq, mul_comm, and_self,
              neg_neg, mul_zero, sub_eq_neg_add, neg_zero] with is_R_or_C_simps

theorem add_conj (z : K) : z + conj z = 2 * (re z) :=
by simp only [ext_iff, two_mul, map_add, add_zero, of_real_im, conj_im, of_real_re,
              eq_self_iff_true, add_right_neg, conj_re, and_self]

/-- The pseudo-coercion `of_real` as a `ring_hom`. -/
noncomputable def of_real_hom : ℝ →+* K := algebra_map ℝ K

/-- The coercion from reals as a `ring_hom`. -/
noncomputable def coe_hom : ℝ →+* K := ⟨coe, of_real_one, of_real_mul, of_real_zero, of_real_add⟩

@[simp, norm_cast, is_R_or_C_simps, priority 900] lemma of_real_sub (r s : ℝ) :
  ((r - s : ℝ) : K) = r - s :=
ext_iff.2 $ by simp only [of_real_im, of_real_re, eq_self_iff_true, sub_zero, and_self, map_sub]

@[simp, norm_cast, is_R_or_C_simps, priority 900] lemma of_real_pow (r : ℝ) (n : ℕ) :
  ((r ^ n : ℝ) : K) = r ^ n :=
begin
  induction n,
  { simp only [of_real_one, pow_zero]},
  { simp only [*, of_real_mul, pow_succ]}
end

theorem sub_conj (z : K) : z - conj z = (2 * im z) * I :=
by simp only [ext_iff, two_mul, sub_eq_add_neg, add_mul, map_add, add_zero, add_left_inj, zero_mul,
              map_add_neg, eq_self_iff_true, add_right_neg, and_self, neg_neg, mul_zero, neg_zero]
              with is_R_or_C_simps

lemma norm_sq_sub (z w : K) : norm_sq (z - w) = norm_sq z + norm_sq w - 2 * re (z * conj w) :=
by simp only [norm_sq_add, sub_eq_add_neg, ring_equiv.map_neg, mul_neg,
              norm_sq_neg, map_neg]

lemma sqrt_norm_sq_eq_norm {z : K} : real.sqrt (norm_sq z) = ∥z∥ :=
begin
  have h₂ : ∥z∥ = real.sqrt (∥z∥^2) := (real.sqrt_sq (norm_nonneg z)).symm,
  rw [h₂],
  exact congr_arg real.sqrt (norm_sq_eq_def' z)
end

/-! ### Inversion -/

@[simp, is_R_or_C_simps] lemma inv_re (z : K) : re (z⁻¹) = re z / norm_sq z :=
by simp only [inv_def, norm_sq_eq_def, norm_sq, division_def,
              monoid_with_zero_hom.coe_mk, sub_zero, mul_zero] with is_R_or_C_simps
@[simp, is_R_or_C_simps] lemma inv_im (z : K) : im (z⁻¹) = im (-z) / norm_sq z :=
by simp only [inv_def, norm_sq_eq_def, norm_sq, division_def, of_real_im,
              monoid_with_zero_hom.coe_mk, of_real_re, zero_add, map_neg, mul_zero]
              with is_R_or_C_simps

@[simp, norm_cast, is_R_or_C_simps, priority 900]
lemma of_real_inv (r : ℝ) : ((r⁻¹ : ℝ) : K) = r⁻¹ :=
begin
  rw ext_iff,
  by_cases r = 0,
  { simp only [h, of_real_zero, inv_zero, and_self, map_zero]},
  { simp only with is_R_or_C_simps,
    field_simp [h, norm_sq] }
end

protected lemma inv_zero : (0⁻¹ : K) = 0 :=
by rw [← of_real_zero, ← of_real_inv, inv_zero]

protected theorem mul_inv_cancel {z : K} (h : z ≠ 0) : z * z⁻¹ = 1 :=
by rw [inv_def, ←mul_assoc, mul_conj, ←of_real_mul, ←norm_sq_eq_def',
      mul_inv_cancel (mt norm_sq_eq_zero.1 h), of_real_one]

lemma div_re (z w : K) : re (z / w) = re z * re w / norm_sq w + im z * im w / norm_sq w :=
by simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, neg_mul,
              mul_neg, neg_neg, map_neg] with is_R_or_C_simps
lemma div_im (z w : K) : im (z / w) = im z * re w / norm_sq w - re z * im w / norm_sq w :=
by simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm, neg_mul,
              mul_neg, map_neg] with is_R_or_C_simps

@[simp, is_R_or_C_simps]
lemma conj_inv (x : K) : conj (x⁻¹) = (conj x)⁻¹ := star_inv' _

@[simp, norm_cast, is_R_or_C_simps, priority 900] lemma of_real_div (r s : ℝ) :
  ((r / s : ℝ) : K) = r / s :=
(@is_R_or_C.coe_hom K _).map_div r s

lemma div_re_of_real {z : K} {r : ℝ} : re (z / r) = re z / r :=
begin
  by_cases h : r = 0,
  { simp only [h, of_real_zero, div_zero, zero_re']},
  { change r ≠ 0 at h,
    rw [div_eq_mul_inv, ←of_real_inv, div_eq_mul_inv],
    simp only [one_div, of_real_im, of_real_re, sub_zero, mul_re, mul_zero]}
end

@[simp, norm_cast, is_R_or_C_simps, priority 900] lemma of_real_zpow (r : ℝ) (n : ℤ) :
  ((r ^ n : ℝ) : K) = r ^ n :=
(@is_R_or_C.coe_hom K _).map_zpow r n

lemma I_mul_I_of_nonzero : (I : K) ≠ 0 → (I : K) * I = -1 :=
by { have := I_mul_I_ax, tauto }

@[simp, is_R_or_C_simps] lemma div_I (z : K) : z / I = -(z * I) :=
begin
  by_cases h : (I : K) = 0,
  { simp [h] },
  { field_simp [mul_assoc, I_mul_I_of_nonzero h] }
end

@[simp, is_R_or_C_simps] lemma inv_I : (I : K)⁻¹ = -I :=
by field_simp

@[simp, is_R_or_C_simps] lemma norm_sq_inv (z : K) : norm_sq z⁻¹ = (norm_sq z)⁻¹ :=
(@norm_sq K _).map_inv z

@[simp, is_R_or_C_simps] lemma norm_sq_div (z w : K) : norm_sq (z / w) = norm_sq z / norm_sq w :=
(@norm_sq K _).map_div z w

@[is_R_or_C_simps] lemma norm_conj {z : K} : ∥conj z∥ = ∥z∥ :=
by simp only [←sqrt_norm_sq_eq_norm, norm_sq_conj]

@[priority 100] instance : cstar_ring K :=
{ norm_star_mul_self := λ x, (norm_mul _ _).trans $ congr_arg (* ∥x∥) norm_conj }

/-! ### Cast lemmas -/

@[simp, is_R_or_C_simps, norm_cast, priority 900] theorem of_real_nat_cast (n : ℕ) :
  ((n : ℝ) : K) = n :=
show (algebra_map ℝ K) n = n, from map_nat_cast of_real_hom n
--of_real_hom.map_nat_cast n
--@[simp, norm_cast, priority 900] theorem of_real_nat_cast (n : ℕ) : ((n : ℝ) : K) = n :=

@[simp, is_R_or_C_simps, norm_cast] lemma nat_cast_re (n : ℕ) : re (n : K) = n :=
by rw [← of_real_nat_cast, of_real_re]

@[simp, is_R_or_C_simps, norm_cast] lemma nat_cast_im (n : ℕ) : im (n : K) = 0 :=
by rw [← of_real_nat_cast, of_real_im]

@[simp, is_R_or_C_simps, norm_cast, priority 900] theorem of_real_int_cast (n : ℤ) :
  ((n : ℝ) : K) = n :=
of_real_hom.map_int_cast n

@[simp, is_R_or_C_simps, norm_cast] lemma int_cast_re (n : ℤ) : re (n : K) = n :=
by rw [← of_real_int_cast, of_real_re]

@[simp, is_R_or_C_simps, norm_cast] lemma int_cast_im (n : ℤ) : im (n : K) = 0 :=
by rw [← of_real_int_cast, of_real_im]

@[simp, is_R_or_C_simps, norm_cast, priority 900] theorem of_real_rat_cast (n : ℚ) :
  ((n : ℝ) : K) = n :=
(@is_R_or_C.of_real_hom K _).map_rat_cast n

@[simp, is_R_or_C_simps, norm_cast] lemma rat_cast_re (q : ℚ) : re (q : K) = q :=
by rw [← of_real_rat_cast, of_real_re]

@[simp, is_R_or_C_simps, norm_cast] lemma rat_cast_im (q : ℚ) : im (q : K) = 0 :=
by rw [← of_real_rat_cast, of_real_im]

/-! ### Characteristic zero -/
/-- ℝ and ℂ are both of characteristic zero.  -/
@[priority 100] -- see Note [lower instance priority]
instance char_zero_R_or_C : char_zero K :=
char_zero_of_inj_zero $ λ n h,
by rwa [← of_real_nat_cast, of_real_eq_zero, nat.cast_eq_zero] at h

theorem re_eq_add_conj (z : K) : ↑(re z) = (z + conj z) / 2 :=
by rw [add_conj, mul_div_cancel_left ((re z):K) two_ne_zero']

theorem im_eq_conj_sub (z : K) : ↑(im z) = I * (conj z - z) / 2 :=
begin
  rw [← neg_inj, ← of_real_neg, ← I_mul_re, re_eq_add_conj],
  simp only [mul_add, sub_eq_add_neg, neg_div', neg_mul, conj_I,
             mul_neg, neg_add_rev, neg_neg, ring_hom.map_mul]
end

/-! ### Absolute value -/

/-- The complex absolute value function, defined as the square root of the norm squared. -/
@[pp_nodot] noncomputable def abs (z : K) : ℝ := (norm_sq z).sqrt

local notation `abs'` := has_abs.abs
local notation `absK` := @abs K _

@[simp, norm_cast] lemma abs_of_real (r : ℝ) : absK r = abs' r :=
by simp only [abs, norm_sq, real.sqrt_mul_self_eq_abs, add_zero, of_real_im,
              monoid_with_zero_hom.coe_mk, of_real_re, mul_zero]

lemma norm_eq_abs (z : K) : ∥z∥ = absK z :=
by simp only [abs, norm_sq_eq_def', norm_nonneg, real.sqrt_sq]

@[is_R_or_C_simps, norm_cast]
lemma norm_of_real (z : ℝ) : ∥(z : K)∥ = ∥z∥ :=
by { rw [is_R_or_C.norm_eq_abs, is_R_or_C.abs_of_real, real.norm_eq_abs] }

lemma abs_of_nonneg {r : ℝ} (h : 0 ≤ r) : absK r = r :=
(abs_of_real _).trans (abs_of_nonneg h)

lemma norm_of_nonneg {r : ℝ} (r_nn : 0 ≤ r) : ∥(r : K)∥ = r :=
by { rw norm_of_real, exact abs_eq_self.mpr r_nn, }

lemma abs_of_nat (n : ℕ) : absK n = n :=
by { rw [← of_real_nat_cast], exact abs_of_nonneg (nat.cast_nonneg n) }

lemma mul_self_abs (z : K) : abs z * abs z = norm_sq z :=
real.mul_self_sqrt (norm_sq_nonneg _)

@[simp, is_R_or_C_simps] lemma abs_zero : absK 0 = 0 := by simp only [abs, real.sqrt_zero, map_zero]
@[simp, is_R_or_C_simps] lemma abs_one : absK 1 = 1 := by simp only [abs, map_one, real.sqrt_one]

@[simp, is_R_or_C_simps] lemma abs_two : absK 2 = 2 :=
calc absK 2 = absK (2 : ℝ) : by rw [of_real_bit0, of_real_one]
... = (2 : ℝ) : abs_of_nonneg (by norm_num)

lemma abs_nonneg (z : K) : 0 ≤ absK z :=
real.sqrt_nonneg _

@[simp, is_R_or_C_simps] lemma abs_eq_zero {z : K} : absK z = 0 ↔ z = 0 :=
(real.sqrt_eq_zero $ norm_sq_nonneg _).trans norm_sq_eq_zero

lemma abs_ne_zero {z : K} : abs z ≠ 0 ↔ z ≠ 0 :=
not_congr abs_eq_zero

@[simp, is_R_or_C_simps] lemma abs_conj (z : K) : abs (conj z) = abs z :=
by simp only [abs, norm_sq_conj]

@[simp, is_R_or_C_simps] lemma abs_mul (z w : K) : abs (z * w) = abs z * abs w :=
by rw [abs, norm_sq_mul, real.sqrt_mul (norm_sq_nonneg _)]; refl

lemma abs_re_le_abs (z : K) : abs' (re z) ≤ abs z :=
by rw [mul_self_le_mul_self_iff (_root_.abs_nonneg (re z)) (abs_nonneg _),
       abs_mul_abs_self, mul_self_abs];
   apply re_sq_le_norm_sq

lemma abs_im_le_abs (z : K) : abs' (im z) ≤ abs z :=
by rw [mul_self_le_mul_self_iff (_root_.abs_nonneg (im z)) (abs_nonneg _),
       abs_mul_abs_self, mul_self_abs];
   apply im_sq_le_norm_sq

lemma norm_re_le_norm (z : K) : ∥re z∥ ≤ ∥z∥ :=
by { rw [is_R_or_C.norm_eq_abs, real.norm_eq_abs], exact is_R_or_C.abs_re_le_abs _, }

lemma norm_im_le_norm (z : K) : ∥im z∥ ≤ ∥z∥ :=
by { rw [is_R_or_C.norm_eq_abs, real.norm_eq_abs], exact is_R_or_C.abs_im_le_abs _, }

lemma re_le_abs (z : K) : re z ≤ abs z :=
(abs_le.1 (abs_re_le_abs _)).2

lemma im_le_abs (z : K) : im z ≤ abs z :=
(abs_le.1 (abs_im_le_abs _)).2

lemma im_eq_zero_of_le {a : K} (h : abs a ≤ re a) : im a = 0 :=
begin
  rw ← zero_eq_mul_self,
  have : re a * re a = re a * re a + im a * im a,
  { convert is_R_or_C.mul_self_abs a;
    linarith [re_le_abs a] },
  linarith
end

lemma re_eq_self_of_le {a : K} (h : abs a ≤ re a) : (re a : K) = a :=
by { rw ← re_add_im a, simp only [im_eq_zero_of_le h, add_zero, zero_mul] with is_R_or_C_simps }

lemma abs_add (z w : K) : abs (z + w) ≤ abs z + abs w :=
(mul_self_le_mul_self_iff (abs_nonneg _)
  (add_nonneg (abs_nonneg _) (abs_nonneg _))).2 $
begin
  rw [mul_self_abs, add_mul_self_eq, mul_self_abs, mul_self_abs,
      add_right_comm, norm_sq_add, add_le_add_iff_left,
      mul_assoc, mul_le_mul_left (@zero_lt_two ℝ _ _)],
  simpa [-mul_re] with is_R_or_C_simps using re_le_abs (z * conj w)
end

instance : is_absolute_value absK :=
{ abv_nonneg  := abs_nonneg,
  abv_eq_zero := λ _, abs_eq_zero,
  abv_add     := abs_add,
  abv_mul     := abs_mul }
open is_absolute_value

@[simp, is_R_or_C_simps] lemma abs_abs (z : K) : abs' (abs z) = abs z :=
_root_.abs_of_nonneg (abs_nonneg _)

@[simp, is_R_or_C_simps] lemma abs_pos {z : K} : 0 < abs z ↔ z ≠ 0 := abv_pos abs
@[simp, is_R_or_C_simps] lemma abs_neg : ∀ z : K, abs (-z) = abs z := abv_neg abs
lemma abs_sub : ∀ z w : K, abs (z - w) = abs (w - z) := abv_sub abs
lemma abs_sub_le : ∀ a b c : K, abs (a - c) ≤ abs (a - b) + abs (b - c) := abv_sub_le abs
@[simp, is_R_or_C_simps] theorem abs_inv : ∀ z : K, abs z⁻¹ = (abs z)⁻¹ := abv_inv abs
@[simp, is_R_or_C_simps] theorem abs_div : ∀ z w : K, abs (z / w) = abs z / abs w := abv_div abs

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

@[simp, is_R_or_C_simps, norm_cast] lemma abs_cast_nat (n : ℕ) : abs (n : K) = n :=
by rw [← of_real_nat_cast, abs_of_nonneg (nat.cast_nonneg n)]

lemma norm_sq_eq_abs (x : K) : norm_sq x = abs x ^ 2 :=
by rw [abs, sq, real.mul_self_sqrt (norm_sq_nonneg _)]

lemma re_eq_abs_of_mul_conj (x : K) : re (x * (conj x)) = abs (x * (conj x)) :=
by rw [mul_conj, of_real_re, abs_of_real, norm_sq_eq_abs, sq, _root_.abs_mul, abs_abs]

lemma abs_sq_re_add_conj (x : K) : (abs (x + conj x))^2 = (re (x + conj x))^2 :=
by simp only [sq, ←norm_sq_eq_abs, norm_sq, map_add, add_zero, monoid_with_zero_hom.coe_mk,
              add_right_neg, mul_zero] with is_R_or_C_simps

lemma abs_sq_re_add_conj' (x : K) : (abs (conj x + x))^2 = (re (conj x + x))^2 :=
by simp only [sq, ←norm_sq_eq_abs, norm_sq, map_add, add_zero, monoid_with_zero_hom.coe_mk,
              add_left_neg, mul_zero] with is_R_or_C_simps

lemma conj_mul_eq_norm_sq_left (x : K) : conj x * x = ((norm_sq x) : K) :=
begin
  rw ext_iff,
  refine ⟨by simp only [norm_sq, neg_mul, monoid_with_zero_hom.coe_mk,
                        sub_neg_eq_add, map_add, sub_zero, mul_zero] with is_R_or_C_simps, _⟩,
  simp only [mul_comm, mul_neg, add_left_neg] with is_R_or_C_simps
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

@[simp, is_R_or_C_simps, norm_cast, priority 900]
lemma of_real_prod {α : Type*} (s : finset α) (f : α → ℝ) :
  ((∏ i in s, f i : ℝ) : K) = ∏ i in s, (f i : K) :=
ring_hom.map_prod _ _ _

@[simp, is_R_or_C_simps, norm_cast, priority 900]
lemma of_real_sum {α : Type*} (s : finset α) (f : α → ℝ) :
  ((∑ i in s, f i : ℝ) : K) = ∑ i in s, (f i : K) :=
ring_hom.map_sum _ _ _

@[simp, is_R_or_C_simps, norm_cast] lemma of_real_finsupp_sum
  {α M : Type*} [has_zero M] (f : α →₀ M) (g : α → M → ℝ) :
  ((f.sum (λ a b, g a b) : ℝ) : K) = f.sum (λ a b, ((g a b) : K)) :=
ring_hom.map_finsupp_sum _ f g

@[simp, is_R_or_C_simps, norm_cast] lemma of_real_finsupp_prod
  {α M : Type*} [has_zero M] (f : α →₀ M) (g : α → M → ℝ) :
  ((f.prod (λ a b, g a b) : ℝ) : K) = f.prod (λ a b, ((g a b) : K)) :=
ring_hom.map_finsupp_prod _ f g

end is_R_or_C

namespace finite_dimensional

open_locale classical
open is_R_or_C

/-- This instance generates a type-class problem with a metavariable `?m` that should satisfy
`is_R_or_C ?m`. Since this can only be satisfied by `ℝ` or `ℂ`, this does not cause problems. -/
library_note "is_R_or_C instance"

/-- An `is_R_or_C` field is finite-dimensional over `ℝ`, since it is spanned by `{1, I}`. -/
@[nolint dangerous_instance] instance is_R_or_C_to_real : finite_dimensional ℝ K :=
⟨⟨{1, I},
  begin
    rw eq_top_iff,
    intros a _,
    rw [finset.coe_insert, finset.coe_singleton, submodule.mem_span_insert],
    refine ⟨re a, (im a) • I, _, _⟩,
    { rw submodule.mem_span_singleton,
      use im a },
    simp [re_add_im a, algebra.smul_def, algebra_map_eq_of_real]
  end⟩⟩

variables (K) (E : Type*) [normed_group E] [normed_space K E]

/-- A finite dimensional vector space Over an `is_R_or_C` is a proper metric space.

This is not an instance because it would cause a search for `finite_dimensional ?x E` before
`is_R_or_C ?x`. -/
lemma proper_is_R_or_C [finite_dimensional K E] : proper_space E :=
begin
  letI : normed_space ℝ E := restrict_scalars.normed_space ℝ K E,
  letI : finite_dimensional ℝ E := finite_dimensional.trans ℝ K E,
  apply_instance
end

variable {E}

instance is_R_or_C.proper_space_span_singleton (x : E) : proper_space (K ∙ x) :=
proper_is_R_or_C K (K ∙ x)

end finite_dimensional

section instances

noncomputable instance real.is_R_or_C : is_R_or_C ℝ :=
{ re := add_monoid_hom.id ℝ,
  im := 0,
  I := 0,
  I_re_ax := by simp only [add_monoid_hom.map_zero],
  I_mul_I_ax := or.intro_left _ rfl,
  re_add_im_ax := λ z, by simp only [add_zero, mul_zero, algebra.id.map_eq_id, ring_hom.id_apply,
                                     add_monoid_hom.id_apply],
  of_real_re_ax := λ r, by simp only [add_monoid_hom.id_apply, algebra.id.map_eq_self],
  of_real_im_ax := λ r, by simp only [add_monoid_hom.zero_apply],
  mul_re_ax := λ z w,
    by simp only [sub_zero, mul_zero, add_monoid_hom.zero_apply, add_monoid_hom.id_apply],
  mul_im_ax := λ z w, by simp only [add_zero, zero_mul, mul_zero, add_monoid_hom.zero_apply],
  conj_re_ax := λ z, by simp only [star_ring_end_apply, star_id_of_comm],
  conj_im_ax := λ z, by simp only [neg_zero, add_monoid_hom.zero_apply],
  conj_I_ax := by simp only [ring_hom.map_zero, neg_zero],
  norm_sq_eq_def_ax := λ z, by simp only [sq, norm, ←abs_mul, abs_mul_self z, add_zero,
    mul_zero, add_monoid_hom.zero_apply, add_monoid_hom.id_apply],
  mul_im_I_ax := λ z, by simp only [mul_zero, add_monoid_hom.zero_apply],
  inv_def_ax := λ z, by simp only [star_ring_end_apply, star, sq, real.norm_eq_abs,
    abs_mul_abs_self, ←div_eq_mul_inv, algebra.id.map_eq_id, id.def, ring_hom.id_apply,
    div_self_mul_self'],
  div_I_ax := λ z, by simp only [div_zero, mul_zero, neg_zero]}

end instances

namespace is_R_or_C

open_locale complex_conjugate

section cleanup_lemmas

local notation `reR` := @is_R_or_C.re ℝ _
local notation `imR` := @is_R_or_C.im ℝ _
local notation `IR` := @is_R_or_C.I ℝ _
local notation `absR` := @is_R_or_C.abs ℝ _
local notation `norm_sqR` := @is_R_or_C.norm_sq ℝ _

@[simp, is_R_or_C_simps] lemma re_to_real {x : ℝ} : reR x = x := rfl
@[simp, is_R_or_C_simps] lemma im_to_real {x : ℝ} : imR x = 0 := rfl
@[simp, is_R_or_C_simps] lemma conj_to_real {x : ℝ} : conj x = x := rfl
@[simp, is_R_or_C_simps] lemma I_to_real : IR = 0 := rfl
@[simp, is_R_or_C_simps] lemma norm_sq_to_real {x : ℝ} : norm_sq x = x*x :=
by simp [is_R_or_C.norm_sq]
@[simp, is_R_or_C_simps] lemma abs_to_real {x : ℝ} : absR x = has_abs.abs x :=
by simp [is_R_or_C.abs, abs, real.sqrt_mul_self_eq_abs]

@[simp] lemma coe_real_eq_id : @coe ℝ ℝ _ = id := rfl

end cleanup_lemmas

section linear_maps

/-- The real part in a `is_R_or_C` field, as a linear map. -/
noncomputable def re_lm : K →ₗ[ℝ] ℝ :=
{ map_smul' := smul_re,  .. re }

@[simp, is_R_or_C_simps] lemma re_lm_coe : (re_lm : K → ℝ) = re := rfl

/-- The real part in a `is_R_or_C` field, as a continuous linear map. -/
noncomputable def re_clm : K →L[ℝ] ℝ :=
linear_map.mk_continuous re_lm 1 $ by
{ simp only [norm_eq_abs, re_lm_coe, one_mul, abs_to_real], exact abs_re_le_abs, }

@[simp, is_R_or_C_simps] lemma re_clm_norm : ∥(re_clm : K →L[ℝ] ℝ)∥ = 1 :=
begin
  apply le_antisymm (linear_map.mk_continuous_norm_le _ zero_le_one _),
  convert continuous_linear_map.ratio_le_op_norm _ (1 : K),
  { simp },
  { apply_instance }
end

@[simp, is_R_or_C_simps, norm_cast] lemma re_clm_coe : ((re_clm : K →L[ℝ] ℝ) :
  K →ₗ[ℝ] ℝ) = re_lm := rfl

@[simp, is_R_or_C_simps] lemma re_clm_apply : ((re_clm : K →L[ℝ] ℝ) : K → ℝ) = re := rfl

@[continuity] lemma continuous_re : continuous (re : K → ℝ) := re_clm.continuous

/-- The imaginary part in a `is_R_or_C` field, as a linear map. -/
noncomputable def im_lm : K →ₗ[ℝ] ℝ :=
{ map_smul' := smul_im,  .. im }

@[simp, is_R_or_C_simps] lemma im_lm_coe : (im_lm : K → ℝ) = im := rfl

/-- The imaginary part in a `is_R_or_C` field, as a continuous linear map. -/
noncomputable def im_clm : K →L[ℝ] ℝ :=
linear_map.mk_continuous im_lm 1 $ by
{ simp only [norm_eq_abs, re_lm_coe, one_mul, abs_to_real], exact abs_im_le_abs, }

@[simp, is_R_or_C_simps, norm_cast] lemma im_clm_coe : ((im_clm : K →L[ℝ] ℝ) :
  K →ₗ[ℝ] ℝ) = im_lm := rfl

@[simp, is_R_or_C_simps] lemma im_clm_apply : ((im_clm : K →L[ℝ] ℝ) : K → ℝ) = im := rfl

@[continuity] lemma continuous_im : continuous (im : K → ℝ) := im_clm.continuous

/-- Conjugate as an `ℝ`-algebra equivalence -/
noncomputable def conj_ae : K ≃ₐ[ℝ] K :=
{ inv_fun := conj,
  left_inv := conj_conj,
  right_inv := conj_conj,
  commutes' := conj_of_real,
  .. conj }

@[simp, is_R_or_C_simps] lemma conj_ae_coe : (conj_ae : K → K) = conj := rfl

/-- Conjugate as a linear isometry -/
noncomputable def conj_lie : K ≃ₗᵢ[ℝ] K :=
⟨conj_ae.to_linear_equiv, λ z, by simp [norm_eq_abs] with is_R_or_C_simps⟩

@[simp, is_R_or_C_simps] lemma conj_lie_apply : (conj_lie : K → K) = conj := rfl

/-- Conjugate as a continuous linear equivalence -/
noncomputable def conj_cle : K ≃L[ℝ] K := @conj_lie K _

@[simp, is_R_or_C_simps] lemma conj_cle_coe :
  (@conj_cle K _).to_linear_equiv = conj_ae.to_linear_equiv := rfl

@[simp, is_R_or_C_simps] lemma conj_cle_apply : (conj_cle : K → K) = conj := rfl

@[simp, is_R_or_C_simps] lemma conj_cle_norm : ∥(@conj_cle K _ : K →L[ℝ] K)∥ = 1 :=
(@conj_lie K _).to_linear_isometry.norm_to_continuous_linear_map

@[continuity] lemma continuous_conj : continuous (conj : K → K) := conj_lie.continuous

/-- The `ℝ → K` coercion, as a linear map -/
noncomputable def of_real_am : ℝ →ₐ[ℝ] K := algebra.of_id ℝ K

@[simp, is_R_or_C_simps] lemma of_real_am_coe : (of_real_am : ℝ → K) = coe := rfl

/-- The ℝ → K coercion, as a linear isometry -/
noncomputable def of_real_li : ℝ →ₗᵢ[ℝ] K :=
{ to_linear_map := of_real_am.to_linear_map, norm_map' := by simp [norm_eq_abs] }

@[simp, is_R_or_C_simps] lemma of_real_li_apply : (of_real_li : ℝ → K) = coe := rfl

/-- The `ℝ → K` coercion, as a continuous linear map -/
noncomputable def of_real_clm : ℝ →L[ℝ] K := of_real_li.to_continuous_linear_map

@[simp, is_R_or_C_simps] lemma of_real_clm_coe :
  ((@of_real_clm K _) : ℝ →ₗ[ℝ] K) = of_real_am.to_linear_map := rfl

@[simp, is_R_or_C_simps] lemma of_real_clm_apply : (of_real_clm : ℝ → K) = coe := rfl

@[simp, is_R_or_C_simps] lemma of_real_clm_norm : ∥(of_real_clm : ℝ →L[ℝ] K)∥ = 1 :=
linear_isometry.norm_to_continuous_linear_map of_real_li

@[continuity] lemma continuous_of_real : continuous (coe : ℝ → K) := of_real_li.continuous

end linear_maps

end is_R_or_C

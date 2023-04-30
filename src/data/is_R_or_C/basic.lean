/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import data.real.sqrt
import analysis.normed_space.star.basic
import analysis.normed_space.continuous_linear_map

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

A few lemmas requiring heavier imports are in `data.is_R_or_C.lemmas`.
-/

open_locale big_operators

section

local notation `𝓚` := algebra_map ℝ _
open_locale complex_conjugate

/--
This typeclass captures properties shared by ℝ and ℂ, with an API that closely matches that of ℂ.
-/
class is_R_or_C (K : Type*)
  extends densely_normed_field K, star_ring K, normed_algebra ℝ K, complete_space K :=
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
(norm_sq_eq_def_ax : ∀ (z : K), ‖z‖^2 = (re z) * (re z) + (im z) * (im z))
(mul_im_I_ax : ∀ (z : K), (im z) * im I = im z)

end

mk_simp_attribute is_R_or_C_simps "Simp attribute for lemmas about `is_R_or_C`"

variables {K E : Type*} [is_R_or_C K]

namespace is_R_or_C

open_locale complex_conjugate

/- The priority must be set at 900 to ensure that coercions are tried in the right order.
See Note [coercion into rings], or `data/nat/cast.lean` for more details. -/
@[priority 900] noncomputable instance algebra_map_coe : has_coe_t ℝ K := ⟨algebra_map ℝ K⟩

lemma of_real_alg (x : ℝ) : (x : K) = x • (1 : K) :=
algebra.algebra_map_eq_smul_one x

lemma real_smul_eq_coe_mul (r : ℝ) (z : K) : r • z = (r : K) * z :=
algebra.smul_def r z

lemma real_smul_eq_coe_smul [add_comm_group E] [module K E] [module ℝ E] [is_scalar_tower ℝ K E]
  (r : ℝ) (x : E) : r • x = (r : K) • x :=
by rw [is_R_or_C.of_real_alg, smul_one_smul]

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

theorem ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w :=
⟨λ h, h ▸ ⟨rfl, rfl⟩, λ ⟨h₁, h₂⟩, re_add_im z ▸ re_add_im w ▸ h₁ ▸ h₂ ▸ rfl⟩

theorem ext {z w : K} (hre : re z = re w) (him : im z = im w) : z = w :=
ext_iff.2 ⟨hre, him⟩

@[simp, norm_cast] lemma of_real_zero : ((0 : ℝ) : K) = 0 :=
by rw [of_real_alg, zero_smul]

@[simp, is_R_or_C_simps] lemma zero_re' : re (0 : K) = (0 : ℝ) := re.map_zero

@[norm_cast] lemma of_real_one : ((1 : ℝ) : K) = 1 := map_one (algebra_map ℝ K)
@[simp, is_R_or_C_simps] lemma one_re : re (1 : K) = 1 := by rw [← of_real_one, of_real_re]
@[simp, is_R_or_C_simps] lemma one_im : im (1 : K) = 0 := by rw [← of_real_one, of_real_im]

theorem of_real_injective : function.injective (coe : ℝ → K) := (algebra_map ℝ K).injective

@[simp, norm_cast] theorem of_real_inj {z w : ℝ} : (z : K) = (w : K) ↔ z = w :=
algebra_map.coe_inj

@[simp, is_R_or_C_simps] lemma bit0_re (z : K) : re (bit0 z) = bit0 (re z) := map_bit0 _ _

@[simp, is_R_or_C_simps] lemma bit1_re (z : K) : re (bit1 z) = bit1 (re z) :=
by simp only [bit1, map_add, bit0_re, one_re]

@[simp, is_R_or_C_simps] lemma bit0_im (z : K) : im (bit0 z) = bit0 (im z) := map_bit0 _ _

@[simp, is_R_or_C_simps] lemma bit1_im (z : K) : im (bit1 z) = bit0 (im z) :=
by simp only [bit1, map_add, bit0_im, one_im, add_zero]

theorem of_real_eq_zero {x : ℝ} : (x : K) = 0 ↔ x = 0 :=
algebra_map.lift_map_eq_zero_iff x

theorem of_real_ne_zero {x : ℝ} : (x : K) ≠ 0 ↔ x ≠ 0 := of_real_eq_zero.not

@[simp, is_R_or_C_simps, norm_cast, priority 900]
lemma of_real_add (r s : ℝ) : ((r + s : ℝ) : K) = r + s := algebra_map.coe_add _ _

@[simp, is_R_or_C_simps, norm_cast, priority 900]
lemma of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : K) = bit0 (r : K) := of_real_add _ _

@[simp, is_R_or_C_simps, norm_cast, priority 900]
lemma of_real_bit1 (r : ℝ) : ((bit1 r : ℝ) : K) = bit1 (r : K) :=
map_bit1 (algebra_map ℝ K) r

@[simp, norm_cast, is_R_or_C_simps, priority 900]
lemma of_real_neg (r : ℝ) : ((-r : ℝ) : K) = -r := algebra_map.coe_neg r

@[simp, norm_cast, is_R_or_C_simps, priority 900]
lemma of_real_sub (r s : ℝ) : ((r - s : ℝ) : K) = r - s := map_sub (algebra_map ℝ K) r s

@[simp, is_R_or_C_simps, norm_cast, priority 900]
lemma of_real_sum {α : Type*} (s : finset α) (f : α → ℝ) :
  ((∑ i in s, f i : ℝ) : K) = ∑ i in s, (f i : K) :=
map_sum (algebra_map ℝ K) _ _

@[simp, is_R_or_C_simps, norm_cast] lemma of_real_finsupp_sum
  {α M : Type*} [has_zero M] (f : α →₀ M) (g : α → M → ℝ) :
  ((f.sum (λ a b, g a b) : ℝ) : K) = f.sum (λ a b, ((g a b) : K)) :=
map_finsupp_sum (algebra_map ℝ K) f g

@[simp, norm_cast, is_R_or_C_simps, priority 900]
lemma of_real_mul (r s : ℝ) : ((r * s : ℝ) : K) = r * s := algebra_map.coe_mul _ _

@[simp, norm_cast, is_R_or_C_simps, priority 900]
lemma of_real_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : K) = r ^ n := map_pow (algebra_map ℝ K) r n

@[simp, is_R_or_C_simps, norm_cast, priority 900]
lemma of_real_prod {α : Type*} (s : finset α) (f : α → ℝ) :
  ((∏ i in s, f i : ℝ) : K) = ∏ i in s, (f i : K) :=
ring_hom.map_prod _ _ _

@[simp, is_R_or_C_simps, norm_cast] lemma of_real_finsupp_prod
  {α M : Type*} [has_zero M] (f : α →₀ M) (g : α → M → ℝ) :
  ((f.prod (λ a b, g a b) : ℝ) : K) = f.prod (λ a b, ((g a b) : K)) :=
ring_hom.map_finsupp_prod _ f g

@[simp, norm_cast, is_R_or_C_simps]
lemma real_smul_of_real (r x : ℝ) : r • (x : K) = (r : K) * (x : K) := real_smul_eq_coe_mul _ _

@[is_R_or_C_simps] lemma of_real_mul_re (r : ℝ) (z : K) : re (↑r * z) = r * re z :=
by simp only [mul_re, of_real_im, zero_mul, of_real_re, sub_zero]

@[is_R_or_C_simps] lemma of_real_mul_im (r : ℝ) (z : K) : im (↑r * z) = r * (im z) :=
by simp only [add_zero, of_real_im, zero_mul, of_real_re, mul_im]

@[is_R_or_C_simps] lemma smul_re (r : ℝ) (z : K) : re (r • z) = r * (re z) :=
by rw [real_smul_eq_coe_mul, of_real_mul_re]

@[is_R_or_C_simps] lemma smul_im (r : ℝ) (z : K) : im (r • z) = r * (im z) :=
by rw [real_smul_eq_coe_mul, of_real_mul_im]

@[simp, norm_cast, is_R_or_C_simps] lemma norm_of_real (r : ℝ) : ‖(r : K)‖ = |r| :=
norm_algebra_map' K r

/-! ### Characteristic zero -/

/-- ℝ and ℂ are both of characteristic zero.  -/
@[priority 100] -- see Note [lower instance priority]
instance char_zero_R_or_C : char_zero K :=
(algebra_map ℝ K).injective.char_zero

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


@[simp, is_R_or_C_simps] lemma conj_bit0 (z : K) : conj (bit0 z) = bit0 (conj z) := map_bit0 _ _
@[simp, is_R_or_C_simps] lemma conj_bit1 (z : K) : conj (bit1 z) = bit1 (conj z) := map_bit1 _ _

@[simp, is_R_or_C_simps] lemma conj_neg_I : conj (-I) = (I : K) :=
by rw [map_neg, conj_I, neg_neg]

lemma conj_eq_re_sub_im (z : K) : conj z = re z - im z * I :=
(congr_arg conj (re_add_im z).symm).trans $ by rw [map_add, map_mul, conj_I, conj_of_real,
  conj_of_real, mul_neg, sub_eq_add_neg]

theorem sub_conj (z : K) : z - conj z = 2 * im z * I :=
begin
  nth_rewrite 0 [← re_add_im z],
  rw [conj_eq_re_sub_im, add_sub_sub_cancel, ← two_mul, mul_assoc]
end

@[is_R_or_C_simps] lemma conj_smul (r : ℝ) (z : K) : conj (r • z) = r • conj z :=
by rw [conj_eq_re_sub_im, conj_eq_re_sub_im, smul_re, smul_im, of_real_mul, of_real_mul,
  real_smul_eq_coe_mul, mul_sub, mul_assoc]

theorem add_conj (z : K) : z + conj z = 2 * (re z) :=
by simp only [ext_iff, two_mul, map_add, add_zero, of_real_im, conj_im, of_real_re,
              eq_self_iff_true, add_right_neg, conj_re, and_self]

theorem re_eq_add_conj (z : K) : ↑(re z) = (z + conj z) / 2 :=
by rw [add_conj, mul_div_cancel_left ((re z):K) two_ne_zero]

theorem im_eq_conj_sub (z : K) : ↑(im z) = I * (conj z - z) / 2 :=
begin
  rw [← neg_inj, ← of_real_neg, ← I_mul_re, re_eq_add_conj],
  simp only [mul_add, sub_eq_add_neg, neg_div', neg_mul, conj_I,
             mul_neg, neg_add_rev, neg_neg, ring_hom.map_mul]
end

/-- There are several equivalent ways to say that a number `z` is in fact a real number. -/
theorem is_real_tfae (z : K) :
  tfae [conj z = z, ∃ r : ℝ, (r : K) = z, ↑(re z) = z, im z = 0] :=
begin
  tfae_have : 1 → 4,
  { intro h,
    rw [← @of_real_inj K, im_eq_conj_sub, h, sub_self, mul_zero, zero_div, of_real_zero] },
  tfae_have : 4 → 3,
  { intro h,
    conv_rhs { rw [← re_add_im z, h, of_real_zero, zero_mul, add_zero] } },
  tfae_have : 3 → 2, from λ h, ⟨_, h⟩,
  tfae_have : 2 → 1, from λ ⟨r, hr⟩, hr ▸ conj_of_real _,
  tfae_finish
end

lemma conj_eq_iff_real {z : K} : conj z = z ↔ ∃ r : ℝ, z = (r : K) :=
((is_real_tfae z).out 0 1).trans $ by simp only [eq_comm]

lemma conj_eq_iff_re {z : K} : conj z = z ↔ ((re z) : K) = z :=
(is_real_tfae z).out 0 2

lemma conj_eq_iff_im {z : K} : conj z = z ↔ im z = 0 := (is_real_tfae z).out 0 3

@[simp] lemma star_def : (has_star.star : K → K) = conj := rfl

variables (K)
/-- Conjugation as a ring equivalence. This is used to convert the inner product into a
sesquilinear product. -/
abbreviation conj_to_ring_equiv : K ≃+* Kᵐᵒᵖ := star_ring_equiv

variables {K}

/-- The norm squared function. -/
def norm_sq : K →*₀ ℝ :=
{ to_fun := λ z, re z * re z + im z * im z,
  map_zero' := by simp only [add_zero, mul_zero, map_zero],
  map_one' := by simp only [one_im, add_zero, mul_one, one_re, mul_zero],
  map_mul' := λ z w, by { simp only [mul_im, mul_re], ring } }

lemma norm_sq_apply (z : K) : norm_sq z = re z * re z + im z * im z := rfl

lemma norm_sq_eq_def {z : K} : ‖z‖^2 = re z * re z + im z * im z := norm_sq_eq_def_ax z
lemma norm_sq_eq_def' (z : K) : norm_sq z = ‖z‖^2 := norm_sq_eq_def.symm

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
by simp only [norm_sq_apply, neg_mul, mul_neg, neg_neg] with is_R_or_C_simps

@[simp, is_R_or_C_simps] lemma norm_sq_mul (z w : K) : norm_sq (z * w) = norm_sq z * norm_sq w :=
norm_sq.map_mul z w

lemma norm_sq_add (z w : K) :
  norm_sq (z + w) = norm_sq z + norm_sq w + 2 * (re (z * conj w)) :=
by { simp only [norm_sq_apply, map_add, mul_neg, sub_neg_eq_add] with is_R_or_C_simps, ring }

lemma re_sq_le_norm_sq (z : K) : re z * re z ≤ norm_sq z :=
le_add_of_nonneg_right (mul_self_nonneg _)

lemma im_sq_le_norm_sq (z : K) : im z * im z ≤ norm_sq z :=
le_add_of_nonneg_left (mul_self_nonneg _)

theorem mul_conj (z : K) : z * conj z = ((norm_sq z) : K) :=
by simp only [map_add, add_zero, ext_iff, add_left_inj, mul_eq_mul_left_iff, zero_mul, add_comm,
              true_or, eq_self_iff_true, mul_neg, add_right_neg, zero_add, norm_sq_apply, mul_comm,
              and_self, neg_neg, mul_zero, sub_eq_neg_add, neg_zero] with is_R_or_C_simps

lemma conj_mul (x : K) : conj x * x = ((norm_sq x) : K) := by rw [mul_comm, mul_conj]

lemma norm_sq_sub (z w : K) : norm_sq (z - w) = norm_sq z + norm_sq w - 2 * re (z * conj w) :=
by simp only [norm_sq_add, sub_eq_add_neg, ring_equiv.map_neg, mul_neg,
              norm_sq_neg, map_neg]

lemma sqrt_norm_sq_eq_norm {z : K} : real.sqrt (norm_sq z) = ‖z‖ :=
by rw [norm_sq_eq_def', real.sqrt_sq (norm_nonneg _)]

/-! ### Inversion -/

@[simp, norm_cast, is_R_or_C_simps, priority 900]
lemma of_real_inv (r : ℝ) : ((r⁻¹ : ℝ) : K) = r⁻¹ := map_inv₀ (algebra_map ℝ K) r

theorem inv_def (z : K) : z⁻¹ = conj z * ((‖z‖^2)⁻¹:ℝ) :=
begin
  rcases eq_or_ne z 0 with (rfl | h₀),
  { simp },
  { apply inv_eq_of_mul_eq_one_right,
    rw [← mul_assoc, mul_conj, of_real_inv, ← norm_sq_eq_def', mul_inv_cancel],
    rwa [of_real_ne_zero, ne.def, norm_sq_eq_zero] }
end

@[simp, is_R_or_C_simps] lemma inv_re (z : K) : re (z⁻¹) = re z / norm_sq z :=
by rw [inv_def, norm_sq_eq_def', mul_comm, of_real_mul_re, conj_re, div_eq_inv_mul]

@[simp, is_R_or_C_simps] lemma inv_im (z : K) : im (z⁻¹) = -im z / norm_sq z :=
by rw [inv_def, norm_sq_eq_def', mul_comm, of_real_mul_im, conj_im, div_eq_inv_mul]

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
map_div₀ (algebra_map ℝ K) r s

lemma div_re_of_real {z : K} {r : ℝ} : re (z / r) = re z / r :=
by rw [div_eq_inv_mul, div_eq_inv_mul, ← of_real_inv, of_real_mul_re]

@[simp, norm_cast, is_R_or_C_simps, priority 900] lemma of_real_zpow (r : ℝ) (n : ℤ) :
  ((r ^ n : ℝ) : K) = r ^ n :=
map_zpow₀ (algebra_map ℝ K) r n

lemma I_mul_I_of_nonzero : (I : K) ≠ 0 → (I : K) * I = -1 := I_mul_I_ax.resolve_left

@[simp, is_R_or_C_simps] lemma inv_I : (I : K)⁻¹ = -I :=
begin
  by_cases h : (I : K) = 0,
  { simp [h] },
  { field_simp [I_mul_I_of_nonzero h] }
end

@[simp, is_R_or_C_simps] lemma div_I (z : K) : z / I = -(z * I) :=
by rw [div_eq_mul_inv, inv_I, mul_neg]

@[simp, is_R_or_C_simps] lemma norm_sq_inv (z : K) : norm_sq z⁻¹ = (norm_sq z)⁻¹ :=
map_inv₀ (@norm_sq K _) z

@[simp, is_R_or_C_simps] lemma norm_sq_div (z w : K) : norm_sq (z / w) = norm_sq z / norm_sq w :=
map_div₀ (@norm_sq K _) z w

@[simp, is_R_or_C_simps] lemma norm_conj {z : K} : ‖conj z‖ = ‖z‖ :=
by simp only [← sqrt_norm_sq_eq_norm, norm_sq_conj]

@[priority 100] instance : cstar_ring K :=
{ norm_star_mul_self := λ x, (norm_mul _ _).trans $ congr_arg (* ‖x‖) norm_conj }

/-! ### Cast lemmas -/

@[simp, is_R_or_C_simps, norm_cast, priority 900] theorem of_real_nat_cast (n : ℕ) :
  ((n : ℝ) : K) = n :=
map_nat_cast (algebra_map ℝ K) n

@[simp, is_R_or_C_simps, norm_cast] lemma nat_cast_re (n : ℕ) : re (n : K) = n :=
by rw [← of_real_nat_cast, of_real_re]

@[simp, is_R_or_C_simps, norm_cast] lemma nat_cast_im (n : ℕ) : im (n : K) = 0 :=
by rw [← of_real_nat_cast, of_real_im]

@[simp, is_R_or_C_simps, norm_cast, priority 900]
lemma of_real_int_cast (n : ℤ) : ((n : ℝ) : K) = n := map_int_cast (algebra_map ℝ K) n

@[simp, is_R_or_C_simps, norm_cast] lemma int_cast_re (n : ℤ) : re (n : K) = n :=
by rw [← of_real_int_cast, of_real_re]

@[simp, is_R_or_C_simps, norm_cast] lemma int_cast_im (n : ℤ) : im (n : K) = 0 :=
by rw [← of_real_int_cast, of_real_im]

@[simp, is_R_or_C_simps, norm_cast, priority 900] theorem of_real_rat_cast (n : ℚ) :
  ((n : ℝ) : K) = n :=
map_rat_cast (algebra_map ℝ K) n

@[simp, is_R_or_C_simps, norm_cast] lemma rat_cast_re (q : ℚ) : re (q : K) = q :=
by rw [← of_real_rat_cast, of_real_re]

@[simp, is_R_or_C_simps, norm_cast] lemma rat_cast_im (q : ℚ) : im (q : K) = 0 :=
by rw [← of_real_rat_cast, of_real_im]

/-! ### Norm -/

lemma norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : K)‖ = r :=
(norm_of_real _).trans (abs_of_nonneg h)

@[simp, is_R_or_C_simps, norm_cast]
lemma norm_nat_cast (n : ℕ) : ‖(n : K)‖ = n :=
by { rw [← of_real_nat_cast], exact norm_of_nonneg (nat.cast_nonneg n) }

lemma mul_self_norm (z : K) : ‖z‖ * ‖z‖ = norm_sq z :=
by rw [norm_sq_eq_def', sq]

attribute [is_R_or_C_simps] norm_zero norm_one norm_eq_zero abs_norm norm_inv norm_div

@[simp, is_R_or_C_simps] lemma norm_two : ‖(2 : K)‖ = 2 :=
by rw [← nat.cast_two, norm_nat_cast, nat.cast_two]

lemma abs_re_le_norm (z : K) : |re z| ≤ ‖z‖ :=
by rw [mul_self_le_mul_self_iff (_root_.abs_nonneg (re z)) (norm_nonneg _),
       abs_mul_abs_self, mul_self_norm];
   apply re_sq_le_norm_sq

lemma abs_im_le_norm (z : K) : |im z| ≤ ‖z‖ :=
by rw [mul_self_le_mul_self_iff (_root_.abs_nonneg (im z)) (norm_nonneg _),
       abs_mul_abs_self, mul_self_norm];
   apply im_sq_le_norm_sq

lemma norm_re_le_norm (z : K) : ‖re z‖ ≤ ‖z‖ := abs_re_le_norm z
lemma norm_im_le_norm (z : K) : ‖im z‖ ≤ ‖z‖ := abs_im_le_norm z

lemma re_le_norm (z : K) : re z ≤ ‖z‖ := (abs_le.1 (abs_re_le_norm z)).2
lemma im_le_abs (z : K) : im z ≤ ‖z‖ := (abs_le.1 (abs_im_le_norm _)).2

lemma im_eq_zero_of_le {a : K} (h : ‖a‖ ≤ re a) : im a = 0 :=
by simpa only [mul_self_norm a, norm_sq_apply, self_eq_add_right, mul_self_eq_zero]
  using congr_arg (λ z, z * z) ((re_le_norm a).antisymm h)

lemma re_eq_self_of_le {a : K} (h : ‖a‖ ≤ re a) : (re a : K) = a :=
by rw [(is_real_tfae a).out 2 3, im_eq_zero_of_le h]

open is_absolute_value

lemma abs_re_div_abs_le_one (z : K) : |re z / ‖z‖| ≤ 1 :=
begin
  rw [abs_div, abs_norm],
  exact div_le_one_of_le (abs_re_le_norm _) (norm_nonneg _)
end

lemma abs_im_div_abs_le_one (z : K) : |im z / ‖z‖| ≤ 1 :=
begin
  rw [abs_div, abs_norm],
  exact div_le_one_of_le (abs_im_le_norm _) (norm_nonneg _)
end

lemma re_eq_norm_of_mul_conj (x : K) : re (x * conj x) = ‖x * conj x‖ :=
by rw [mul_conj, of_real_re, norm_of_real, abs_of_nonneg (norm_sq_nonneg _)]

lemma norm_sq_re_add_conj (x : K) : (‖x + conj x‖)^2 = (re (x + conj x))^2 :=
by rw [add_conj, norm_mul, norm_two, norm_of_real, two_mul (re x : K), map_add, of_real_re,
  ← two_mul, mul_pow, mul_pow, sq_abs]

lemma norm_sq_re_conj_add (x : K) : (‖conj x + x‖)^2 = (re (conj x + x))^2 :=
by rw [add_comm, norm_sq_re_add_conj]

/-! ### Cauchy sequences -/

theorem is_cau_seq_re (f : cau_seq K norm) : is_cau_seq abs (λ n, re (f n)) :=
λ ε ε0, (f.cauchy ε0).imp $ λ i H j ij,
lt_of_le_of_lt (by simpa only [map_sub] using abs_re_le_norm (f j - f i)) (H _ ij)

theorem is_cau_seq_im (f : cau_seq K norm) : is_cau_seq abs (λ n, im (f n)) :=
λ ε ε0, (f.cauchy ε0).imp $ λ i H j ij,
lt_of_le_of_lt (by simpa only [map_sub] using abs_im_le_norm (f j - f i)) (H _ ij)

/-- The real part of a K Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cau_seq_re (f : cau_seq K norm) : cau_seq ℝ abs :=
⟨_, is_cau_seq_re f⟩

/-- The imaginary part of a K Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cau_seq_im (f : cau_seq K norm) : cau_seq ℝ abs :=
⟨_, is_cau_seq_im f⟩

lemma is_cau_seq_norm {f : ℕ → K} (hf : is_cau_seq norm f) :
  is_cau_seq abs (norm ∘ f) :=
λ ε ε0, let ⟨i, hi⟩ := hf ε ε0 in
⟨i, λ j hj, lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩

end is_R_or_C


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
  norm_sq_eq_def_ax := λ z, by simp only [sq, real.norm_eq_abs, ←abs_mul, abs_mul_self z, add_zero,
    mul_zero, add_monoid_hom.zero_apply, add_monoid_hom.id_apply],
  mul_im_I_ax := λ z, by simp only [mul_zero, add_monoid_hom.zero_apply],
  .. real.densely_normed_field, .. real.metric_space }

end instances

namespace is_R_or_C

open_locale complex_conjugate

section cleanup_lemmas

local notation `reR` := @is_R_or_C.re ℝ _
local notation `imR` := @is_R_or_C.im ℝ _
local notation `IR` := @is_R_or_C.I ℝ _
local notation `norm_sqR` := @is_R_or_C.norm_sq ℝ _

@[simp, is_R_or_C_simps] lemma re_to_real {x : ℝ} : reR x = x := rfl
@[simp, is_R_or_C_simps] lemma im_to_real {x : ℝ} : imR x = 0 := rfl
@[simp, is_R_or_C_simps] lemma conj_to_real {x : ℝ} : conj x = x := rfl
@[simp, is_R_or_C_simps] lemma I_to_real : IR = 0 := rfl
@[simp, is_R_or_C_simps] lemma norm_sq_to_real {x : ℝ} : norm_sq x = x*x :=
by simp [is_R_or_C.norm_sq]

@[simp] lemma coe_real_eq_id : @coe ℝ ℝ _ = id := rfl

end cleanup_lemmas

section linear_maps

/-- The real part in a `is_R_or_C` field, as a linear map. -/
def re_lm : K →ₗ[ℝ] ℝ :=
{ map_smul' := smul_re,  .. re }

@[simp, is_R_or_C_simps] lemma re_lm_coe : (re_lm : K → ℝ) = re := rfl

/-- The real part in a `is_R_or_C` field, as a continuous linear map. -/
noncomputable def re_clm : K →L[ℝ] ℝ :=
linear_map.mk_continuous re_lm 1 $ λ x, by { rw [one_mul], exact abs_re_le_norm x }

@[simp, is_R_or_C_simps, norm_cast] lemma re_clm_coe : ((re_clm : K →L[ℝ] ℝ) :
  K →ₗ[ℝ] ℝ) = re_lm := rfl

@[simp, is_R_or_C_simps] lemma re_clm_apply : ((re_clm : K →L[ℝ] ℝ) : K → ℝ) = re := rfl

@[continuity] lemma continuous_re : continuous (re : K → ℝ) := re_clm.continuous

/-- The imaginary part in a `is_R_or_C` field, as a linear map. -/
def im_lm : K →ₗ[ℝ] ℝ :=
{ map_smul' := smul_im,  .. im }

@[simp, is_R_or_C_simps] lemma im_lm_coe : (im_lm : K → ℝ) = im := rfl

/-- The imaginary part in a `is_R_or_C` field, as a continuous linear map. -/
noncomputable def im_clm : K →L[ℝ] ℝ :=
linear_map.mk_continuous im_lm 1 $ fun x, by { rw [one_mul], exact abs_im_le_norm x }

@[simp, is_R_or_C_simps, norm_cast] lemma im_clm_coe : ((im_clm : K →L[ℝ] ℝ) :
  K →ₗ[ℝ] ℝ) = im_lm := rfl

@[simp, is_R_or_C_simps] lemma im_clm_apply : ((im_clm : K →L[ℝ] ℝ) : K → ℝ) = im := rfl

@[continuity] lemma continuous_im : continuous (im : K → ℝ) := im_clm.continuous

/-- Conjugate as an `ℝ`-algebra equivalence -/
def conj_ae : K ≃ₐ[ℝ] K :=
{ inv_fun := conj,
  left_inv := conj_conj,
  right_inv := conj_conj,
  commutes' := conj_of_real,
  .. conj }

@[simp, is_R_or_C_simps] lemma conj_ae_coe : (conj_ae : K → K) = conj := rfl

/-- Conjugate as a linear isometry -/
noncomputable def conj_lie : K ≃ₗᵢ[ℝ] K :=
⟨conj_ae.to_linear_equiv, λ _, norm_conj⟩

@[simp, is_R_or_C_simps] lemma conj_lie_apply : (conj_lie : K → K) = conj := rfl

/-- Conjugate as a continuous linear equivalence -/
noncomputable def conj_cle : K ≃L[ℝ] K := @conj_lie K _

@[simp, is_R_or_C_simps] lemma conj_cle_coe :
  (@conj_cle K _).to_linear_equiv = conj_ae.to_linear_equiv := rfl

@[simp, is_R_or_C_simps] lemma conj_cle_apply : (conj_cle : K → K) = conj := rfl

@[priority 100]
instance : has_continuous_star K := ⟨conj_lie.continuous⟩

@[continuity] lemma continuous_conj : continuous (conj : K → K) := continuous_star

/-- The `ℝ → K` coercion, as a linear map -/
noncomputable def of_real_am : ℝ →ₐ[ℝ] K := algebra.of_id ℝ K

@[simp, is_R_or_C_simps] lemma of_real_am_coe : (of_real_am : ℝ → K) = coe := rfl

/-- The ℝ → K coercion, as a linear isometry -/
noncomputable def of_real_li : ℝ →ₗᵢ[ℝ] K :=
{ to_linear_map := of_real_am.to_linear_map, norm_map' := norm_of_real }

@[simp, is_R_or_C_simps] lemma of_real_li_apply : (of_real_li : ℝ → K) = coe := rfl

/-- The `ℝ → K` coercion, as a continuous linear map -/
noncomputable def of_real_clm : ℝ →L[ℝ] K := of_real_li.to_continuous_linear_map

@[simp, is_R_or_C_simps] lemma of_real_clm_coe :
  ((@of_real_clm K _) : ℝ →ₗ[ℝ] K) = of_real_am.to_linear_map := rfl

@[simp, is_R_or_C_simps] lemma of_real_clm_apply : (of_real_clm : ℝ → K) = coe := rfl

@[continuity] lemma continuous_of_real : continuous (coe : ℝ → K) := of_real_li.continuous

@[continuity] lemma continuous_norm_sq : continuous (norm_sq : K → ℝ) :=
(continuous_re.mul continuous_re).add (continuous_im.mul continuous_im)

end linear_maps

end is_R_or_C

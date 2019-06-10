/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro

The complex numbers, modelled as R^2 in the obvious way.
-/
import data.real.basic tactic.ring algebra.field_power

structure complex : Type :=
(re : ℝ) (im : ℝ)

notation `ℂ` := complex

namespace complex

@[simp] theorem eta : ∀ z : ℂ, complex.mk z.re z.im = z
| ⟨a, b⟩ := rfl

theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
| ⟨zr, zi⟩ ⟨_, _⟩ rfl rfl := rfl

theorem ext_iff {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
⟨λ H, by simp [H], and.rec ext⟩

def of_real (r : ℝ) : ℂ := ⟨r, 0⟩
instance : has_coe ℝ ℂ := ⟨of_real⟩
@[simp] lemma of_real_eq_coe (r : ℝ) : of_real r = r := rfl

@[simp] lemma of_real_re (r : ℝ) : (r : ℂ).re = r := rfl
@[simp] lemma of_real_im (r : ℝ) : (r : ℂ).im = 0 := rfl

@[simp] theorem of_real_inj {z w : ℝ} : (z : ℂ) = w ↔ z = w :=
⟨congr_arg re, congr_arg _⟩

instance : has_zero ℂ := ⟨(0 : ℝ)⟩
instance : inhabited ℂ := ⟨0⟩

@[simp] lemma zero_re : (0 : ℂ).re = 0 := rfl
@[simp] lemma zero_im : (0 : ℂ).im = 0 := rfl
@[simp] lemma of_real_zero : ((0 : ℝ) : ℂ) = 0 := rfl

@[simp] theorem of_real_eq_zero {z : ℝ} : (z : ℂ) = 0 ↔ z = 0 := of_real_inj
@[simp] theorem of_real_ne_zero {z : ℝ} : (z : ℂ) ≠ 0 ↔ z ≠ 0 := not_congr of_real_eq_zero

instance : has_one ℂ := ⟨(1 : ℝ)⟩

@[simp] lemma one_re : (1 : ℂ).re = 1 := rfl
@[simp] lemma one_im : (1 : ℂ).im = 0 := rfl
@[simp] lemma of_real_one : ((1 : ℝ) : ℂ) = 1 := rfl

def I : ℂ := ⟨0, 1⟩

@[simp] lemma I_re : I.re = 0 := rfl
@[simp] lemma I_im : I.im = 1 := rfl

instance : has_add ℂ := ⟨λ z w, ⟨z.re + w.re, z.im + w.im⟩⟩

@[simp] lemma add_re (z w : ℂ) : (z + w).re = z.re + w.re := rfl
@[simp] lemma add_im (z w : ℂ) : (z + w).im = z.im + w.im := rfl
@[simp] lemma of_real_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s := ext_iff.2 $ by simp

@[simp] lemma of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : ℂ) = bit0 r := ext_iff.2 $ by simp [bit0]
@[simp] lemma of_real_bit1 (r : ℝ) : ((bit1 r : ℝ) : ℂ) = bit1 r := ext_iff.2 $ by simp [bit1]

instance : has_neg ℂ := ⟨λ z, ⟨-z.re, -z.im⟩⟩

@[simp] lemma neg_re (z : ℂ) : (-z).re = -z.re := rfl
@[simp] lemma neg_im (z : ℂ) : (-z).im = -z.im := rfl
@[simp] lemma of_real_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r := ext_iff.2 $ by simp

instance : has_mul ℂ := ⟨λ z w, ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp] lemma mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] lemma mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] lemma of_real_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s := ext_iff.2 $ by simp

@[simp] lemma I_mul_I : I * I = -1 := ext_iff.2 $ by simp

lemma I_ne_zero : (I : ℂ) ≠ 0 := mt (congr_arg im) zero_ne_one.symm

lemma mk_eq_add_mul_I (a b : ℝ) : complex.mk a b = a + b * I :=
ext_iff.2 $ by simp

@[simp] lemma re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z :=
ext_iff.2 $ by simp

def real_prod_equiv : ℂ ≃ (ℝ × ℝ) :=
{ to_fun := λ z, ⟨z.re, z.im⟩,
  inv_fun := λ p, ⟨p.1, p.2⟩,
  left_inv := λ ⟨x, y⟩, rfl,
  right_inv := λ ⟨x, y⟩, rfl }

@[simp] theorem real_prod_equiv_apply (z : ℂ) : real_prod_equiv z = (z.re, z.im) := rfl
theorem real_prod_equiv_symm_re (x y : ℝ) : (real_prod_equiv.symm (x, y)).re = x := rfl
theorem real_prod_equiv_symm_im (x y : ℝ) : (real_prod_equiv.symm (x, y)).im = y := rfl

def conj (z : ℂ) : ℂ := ⟨z.re, -z.im⟩

@[simp] lemma conj_re (z : ℂ) : (conj z).re = z.re := rfl
@[simp] lemma conj_im (z : ℂ) : (conj z).im = -z.im := rfl

@[simp] lemma conj_of_real (r : ℝ) : conj r = r := ext_iff.2 $ by simp [conj]

@[simp] lemma conj_zero : conj 0 = 0 := ext_iff.2 $ by simp [conj]
@[simp] lemma conj_one : conj 1 = 1 := ext_iff.2 $ by simp
@[simp] lemma conj_I : conj I = -I := ext_iff.2 $ by simp
@[simp] lemma conj_neg_I : conj (-I) = I := ext_iff.2 $ by simp

@[simp] lemma conj_add (z w : ℂ) : conj (z + w) = conj z + conj w :=
ext_iff.2 $ by simp

@[simp] lemma conj_neg (z : ℂ) : conj (-z) = -conj z := rfl

@[simp] lemma conj_mul (z w : ℂ) : conj (z * w) = conj z * conj w :=
ext_iff.2 $ by simp

@[simp] lemma conj_conj (z : ℂ) : conj (conj z) = z :=
ext_iff.2 $ by simp

lemma conj_bijective : function.bijective conj :=
⟨function.injective_of_has_left_inverse ⟨conj, conj_conj⟩,
 function.surjective_of_has_right_inverse ⟨conj, conj_conj⟩⟩

lemma conj_inj {z w : ℂ} : conj z = conj w ↔ z = w :=
conj_bijective.1.eq_iff

@[simp] lemma conj_eq_zero {z : ℂ} : conj z = 0 ↔ z = 0 :=
by simpa using @conj_inj z 0

@[simp] lemma eq_conj_iff_real (z : ℂ) : conj z = z ↔ ∃ r : ℝ, z = r :=
⟨λ h, ⟨z.re, ext rfl $ eq_zero_of_neg_eq (congr_arg im h)⟩,
 λ ⟨h, e⟩, e.symm ▸ rfl⟩

def norm_sq (z : ℂ) : ℝ := z.re * z.re + z.im * z.im

@[simp] lemma norm_sq_of_real (r : ℝ) : norm_sq r = r * r :=
by simp [norm_sq]

@[simp] lemma norm_sq_zero : norm_sq 0 = 0 := by simp [norm_sq]
@[simp] lemma norm_sq_one : norm_sq 1 = 1 := by simp [norm_sq]
@[simp] lemma norm_sq_I : norm_sq I = 1 := by simp [norm_sq]

lemma norm_sq_nonneg (z : ℂ) : 0 ≤ norm_sq z :=
add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

@[simp] lemma norm_sq_eq_zero {z : ℂ} : norm_sq z = 0 ↔ z = 0 :=
⟨λ h, ext
  (eq_zero_of_mul_self_add_mul_self_eq_zero h)
  (eq_zero_of_mul_self_add_mul_self_eq_zero $ (add_comm _ _).trans h),
 λ h, h.symm ▸ norm_sq_zero⟩

@[simp] lemma norm_sq_pos {z : ℂ} : 0 < norm_sq z ↔ z ≠ 0 :=
by rw [lt_iff_le_and_ne, ne, eq_comm]; simp [norm_sq_nonneg]

@[simp] lemma norm_sq_neg (z : ℂ) : norm_sq (-z) = norm_sq z :=
by simp [norm_sq]

@[simp] lemma norm_sq_conj (z : ℂ) : norm_sq (conj z) = norm_sq z :=
by simp [norm_sq]

@[simp] lemma norm_sq_mul (z w : ℂ) : norm_sq (z * w) = norm_sq z * norm_sq w :=
by dsimp [norm_sq]; ring

lemma norm_sq_add (z w : ℂ) : norm_sq (z + w) =
  norm_sq z + norm_sq w + 2 * (z * conj w).re :=
by dsimp [norm_sq]; ring

lemma re_sq_le_norm_sq (z : ℂ) : z.re * z.re ≤ norm_sq z :=
le_add_of_nonneg_right (mul_self_nonneg _)

lemma im_sq_le_norm_sq (z : ℂ) : z.im * z.im ≤ norm_sq z :=
le_add_of_nonneg_left (mul_self_nonneg _)

theorem mul_conj (z : ℂ) : z * conj z = norm_sq z :=
ext_iff.2 $ by simp [norm_sq, mul_comm]

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
ext_iff.2 $ by simp [two_mul]

instance : comm_ring ℂ :=
by refine { zero := 0, add := (+), neg := has_neg.neg, one := 1, mul := (*), ..};
   { intros, apply ext_iff.2; split; simp; ring }

@[simp] lemma bit0_re (z : ℂ) : (bit0 z).re = bit0 z.re := rfl
@[simp] lemma bit1_re (z : ℂ) : (bit1 z).re = bit1 z.re := rfl
@[simp] lemma bit0_im (z : ℂ) : (bit0 z).im = bit0 z.im := eq.refl _
@[simp] lemma bit1_im (z : ℂ) : (bit1 z).im = bit0 z.im := add_zero _

@[simp] lemma sub_re (z w : ℂ) : (z - w).re = z.re - w.re := rfl
@[simp] lemma sub_im (z w : ℂ) : (z - w).im = z.im - w.im := rfl
@[simp] lemma of_real_sub (r s : ℝ) : ((r - s : ℝ) : ℂ) = r - s := ext_iff.2 $ by simp
@[simp] lemma of_real_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : ℂ) = r ^ n :=
by induction n; simp [*, of_real_mul, pow_succ]

theorem sub_conj (z : ℂ) : z - conj z = (2 * z.im : ℝ) * I :=
ext_iff.2 $ by simp [two_mul]

lemma conj_pow (z : ℂ) (n : ℕ) : conj (z ^ n) = conj z ^ n :=
by induction n; simp [*, conj_mul, pow_succ]

@[simp] lemma conj_two : conj (2 : ℂ) = 2 := by apply complex.ext; simp

lemma norm_sq_sub (z w : ℂ) : norm_sq (z - w) =
  norm_sq z + norm_sq w - 2 * (z * conj w).re :=
by rw [sub_eq_add_neg, norm_sq_add]; simp [-mul_re]

noncomputable instance : has_inv ℂ := ⟨λ z, conj z * ((norm_sq z)⁻¹:ℝ)⟩

theorem inv_def (z : ℂ) : z⁻¹ = conj z * ((norm_sq z)⁻¹:ℝ) := rfl
@[simp] lemma inv_re (z : ℂ) : (z⁻¹).re = z.re / norm_sq z := by simp [inv_def, division_def]
@[simp] lemma inv_im (z : ℂ) : (z⁻¹).im = -z.im / norm_sq z := by simp [inv_def, division_def]

@[simp] lemma of_real_inv (r : ℝ) : ((r⁻¹ : ℝ) : ℂ) = r⁻¹ :=
ext_iff.2 $ begin
  simp,
  by_cases r = 0, {simp [h]},
  rw [← div_div_eq_div_mul, div_self h, one_div_eq_inv]
end

protected lemma inv_zero : (0⁻¹ : ℂ) = 0 :=
by rw [← of_real_zero, ← of_real_inv, inv_zero]

protected theorem mul_inv_cancel {z : ℂ} (h : z ≠ 0) : z * z⁻¹ = 1 :=
by rw [inv_def, ← mul_assoc, mul_conj, ← of_real_mul,
  mul_inv_cancel (mt norm_sq_eq_zero.1 h), of_real_one]

noncomputable instance : discrete_field ℂ :=
{ inv := has_inv.inv,
  zero_ne_one := mt (congr_arg re) zero_ne_one,
  mul_inv_cancel := @complex.mul_inv_cancel,
  inv_mul_cancel := λ z h, by rw [mul_comm, complex.mul_inv_cancel h],
  inv_zero := complex.inv_zero,
  has_decidable_eq := classical.dec_eq _,
  ..complex.comm_ring }

instance re.is_add_group_hom : is_add_group_hom complex.re :=
by refine_struct {..}; simp

instance im.is_add_group_hom : is_add_group_hom complex.im :=
by refine_struct {..}; simp

instance : is_ring_hom conj :=
by refine_struct {..}; simp

instance of_real.is_ring_hom : is_ring_hom (coe : ℝ → ℂ) :=
by refine_struct {..}; simp

@[simp] lemma of_real_div (r s : ℝ) : ((r / s : ℝ) : ℂ) = r / s :=
is_field_hom.map_div coe

@[simp] lemma of_real_fpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n :=
is_field_hom.map_fpow of_real r n

@[simp] theorem of_real_int_cast : ∀ n : ℤ, ((n : ℝ) : ℂ) = n :=
int.eq_cast (λ n, ((n : ℝ) : ℂ))
  (by rw [int.cast_one, of_real_one])
  (λ _ _, by rw [int.cast_add, of_real_add])

@[simp] theorem of_real_nat_cast (n : ℕ) : ((n : ℝ) : ℂ) = n :=
by rw [← int.cast_coe_nat, of_real_int_cast]; refl

@[simp] lemma conj_inv (z : ℂ) : conj z⁻¹ = (conj z)⁻¹ :=
if h : z = 0 then by simp [h] else
(domain.mul_left_inj (mt conj_eq_zero.1 h)).1 $
by rw [← conj_mul]; simp [h, -conj_mul]

@[simp] lemma conj_sub (z w : ℂ) : conj (z - w) = conj z - conj w :=
by simp

@[simp] lemma conj_div (z w : ℂ) : conj (z / w) = conj z / conj w :=
by rw [division_def, conj_mul, conj_inv]; refl

@[simp] lemma norm_sq_inv (z : ℂ) : norm_sq z⁻¹ = (norm_sq z)⁻¹ :=
if h : z = 0 then by simp [h] else
(domain.mul_left_inj (mt norm_sq_eq_zero.1 h)).1 $
by rw [← norm_sq_mul]; simp [h, -norm_sq_mul]

@[simp] lemma norm_sq_div (z w : ℂ) : norm_sq (z / w) = norm_sq z / norm_sq w :=
by rw [division_def, norm_sq_mul, norm_sq_inv]; refl

instance char_zero_complex : char_zero ℂ :=
add_group.char_zero_of_inj_zero $ λ n h,
by rwa [← of_real_nat_cast, of_real_eq_zero, nat.cast_eq_zero] at h

@[simp] theorem of_real_rat_cast : ∀ n : ℚ, ((n : ℝ) : ℂ) = n :=
by apply rat.eq_cast (λ n, ((n : ℝ) : ℂ)); simp

theorem re_eq_add_conj (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 :=
by rw [add_conj]; simp; rw [mul_div_cancel_left (z.re:ℂ) two_ne_zero']

@[simp] lemma nat_cast_re (n : ℕ) : (n : ℂ).re = n :=
by rw [← of_real_nat_cast, of_real_re]

@[simp] lemma nat_cast_im (n : ℕ) : (n : ℂ).im = 0 :=
by rw [← of_real_nat_cast, of_real_im]

@[simp] lemma int_cast_re (n : ℤ) : (n : ℂ).re = n :=
by rw [← of_real_int_cast, of_real_re]

@[simp] lemma int_cast_im (n : ℤ) : (n : ℂ).im = 0 :=
by rw [← of_real_int_cast, of_real_im]

@[simp] lemma rat_cast_re (q : ℚ) : (q : ℂ).re = q :=
by rw [← of_real_rat_cast, of_real_re]

@[simp] lemma rat_cast_im (q : ℚ) : (q : ℂ).im = 0 :=
by rw [← of_real_rat_cast, of_real_im]

noncomputable def abs (z : ℂ) : ℝ := (norm_sq z).sqrt

local notation `abs'` := _root_.abs

@[simp] lemma abs_of_real (r : ℝ) : abs r = abs' r :=
by simp [abs, norm_sq_of_real, real.sqrt_mul_self_eq_abs]

lemma abs_of_nonneg {r : ℝ} (h : 0 ≤ r) : abs r = r :=
(abs_of_real _).trans (abs_of_nonneg h)

lemma mul_self_abs (z : ℂ) : abs z * abs z = norm_sq z :=
real.mul_self_sqrt (norm_sq_nonneg _)

@[simp] lemma abs_zero : abs 0 = 0 := by simp [abs]
@[simp] lemma abs_one : abs 1 = 1 := by simp [abs]
@[simp] lemma abs_I : abs I = 1 := by simp [abs]

@[simp] lemma abs_two : abs 2 = 2 :=
calc abs 2 = abs (2 : ℝ) : by rw [of_real_bit0, of_real_one]
... = (2 : ℝ) : abs_of_nonneg (by norm_num)

lemma abs_nonneg (z : ℂ) : 0 ≤ abs z :=
real.sqrt_nonneg _

@[simp] lemma abs_eq_zero {z : ℂ} : abs z = 0 ↔ z = 0 :=
(real.sqrt_eq_zero $ norm_sq_nonneg _).trans norm_sq_eq_zero

@[simp] lemma abs_conj (z : ℂ) : abs (conj z) = abs z :=
by simp [abs]

@[simp] lemma abs_mul (z w : ℂ) : abs (z * w) = abs z * abs w :=
by rw [abs, norm_sq_mul, real.sqrt_mul (norm_sq_nonneg _)]; refl

lemma abs_re_le_abs (z : ℂ) : abs' z.re ≤ abs z :=
by rw [mul_self_le_mul_self_iff (_root_.abs_nonneg z.re) (abs_nonneg _),
       abs_mul_abs_self, mul_self_abs];
   apply re_sq_le_norm_sq

lemma abs_im_le_abs (z : ℂ) : abs' z.im ≤ abs z :=
by rw [mul_self_le_mul_self_iff (_root_.abs_nonneg z.im) (abs_nonneg _),
       abs_mul_abs_self, mul_self_abs];
   apply im_sq_le_norm_sq

lemma re_le_abs (z : ℂ) : z.re ≤ abs z :=
(abs_le.1 (abs_re_le_abs _)).2

lemma im_le_abs (z : ℂ) : z.im ≤ abs z :=
(abs_le.1 (abs_im_le_abs _)).2

lemma abs_add (z w : ℂ) : abs (z + w) ≤ abs z + abs w :=
(mul_self_le_mul_self_iff (abs_nonneg _)
  (add_nonneg (abs_nonneg _) (abs_nonneg _))).2 $
begin
  rw [mul_self_abs, add_mul_self_eq, mul_self_abs, mul_self_abs,
      add_right_comm, norm_sq_add, add_le_add_iff_left,
      mul_assoc, mul_le_mul_left (@two_pos ℝ _)],
  simpa [-mul_re] using re_le_abs (z * conj w)
end

instance : is_absolute_value abs :=
{ abv_nonneg  := abs_nonneg,
  abv_eq_zero := λ _, abs_eq_zero,
  abv_add     := abs_add,
  abv_mul     := abs_mul }
open is_absolute_value

@[simp] lemma abs_abs (z : ℂ) : abs' (abs z) = abs z :=
_root_.abs_of_nonneg (abs_nonneg _)

@[simp] lemma abs_pos {z : ℂ} : 0 < abs z ↔ z ≠ 0 := abv_pos abs
@[simp] lemma abs_neg : ∀ z, abs (-z) = abs z := abv_neg abs
lemma abs_sub : ∀ z w, abs (z - w) = abs (w - z) := abv_sub abs
lemma abs_sub_le : ∀ a b c, abs (a - c) ≤ abs (a - b) + abs (b - c) := abv_sub_le abs
@[simp] theorem abs_inv : ∀ z, abs z⁻¹ = (abs z)⁻¹ := abv_inv abs
@[simp] theorem abs_div : ∀ z w, abs (z / w) = abs z / abs w := abv_div abs
lemma abs_abs_sub_le_abs_sub : ∀ z w, abs' (abs z - abs w) ≤ abs (z - w) := abs_abv_sub_le_abv_sub abs

lemma abs_le_abs_re_add_abs_im (z : ℂ) : abs z ≤ abs' z.re + abs' z.im :=
by simpa [re_add_im] using abs_add z.re (z.im * I)

lemma abs_re_div_abs_le_one (z : ℂ) : abs' (z.re / z.abs) ≤ 1 :=
if hz : z = 0 then by simp [hz, zero_le_one]
else by rw [_root_.abs_div, abs_abs]; exact
  div_le_of_le_mul (abs_pos.2 hz) (by rw mul_one; exact abs_re_le_abs _)

lemma abs_im_div_abs_le_one (z : ℂ) : abs' (z.im / z.abs) ≤ 1 :=
if hz : z = 0 then by simp [hz, zero_le_one]
else by rw [_root_.abs_div, abs_abs]; exact
  div_le_of_le_mul (abs_pos.2 hz) (by rw mul_one; exact abs_im_le_abs _)

@[simp] lemma abs_cast_nat (n : ℕ) : abs (n : ℂ) = n :=
by rw [← of_real_nat_cast, abs_of_nonneg (nat.cast_nonneg n)]

lemma norm_sq_eq_abs (x : ℂ) : norm_sq x = abs x ^ 2 :=
by rw [abs, pow_two, real.mul_self_sqrt (norm_sq_nonneg _)]

theorem is_cau_seq_re (f : cau_seq ℂ abs) : is_cau_seq abs' (λ n, (f n).re) :=
λ ε ε0, (f.cauchy ε0).imp $ λ i H j ij,
lt_of_le_of_lt (by simpa using abs_re_le_abs (f j - f i)) (H _ ij)

theorem is_cau_seq_im (f : cau_seq ℂ abs) : is_cau_seq abs' (λ n, (f n).im) :=
λ ε ε0, (f.cauchy ε0).imp $ λ i H j ij,
lt_of_le_of_lt (by simpa using abs_im_le_abs (f j - f i)) (H _ ij)

noncomputable def cau_seq_re (f : cau_seq ℂ abs) : cau_seq ℝ abs' :=
⟨_, is_cau_seq_re f⟩

noncomputable def cau_seq_im (f : cau_seq ℂ abs) : cau_seq ℝ abs' :=
⟨_, is_cau_seq_im f⟩

lemma is_cau_seq_abs {f : ℕ → ℂ} (hf : is_cau_seq abs f) :
  is_cau_seq abs' (abs ∘ f) :=
λ ε ε0, let ⟨i, hi⟩ := hf ε ε0 in
⟨i, λ j hj, lt_of_le_of_lt (abs_abs_sub_le_abs_sub _ _) (hi j hj)⟩

noncomputable def lim_aux (f : cau_seq ℂ abs) : ℂ :=
⟨cau_seq.lim (cau_seq_re f), cau_seq.lim (cau_seq_im f)⟩

theorem equiv_lim_aux (f : cau_seq ℂ abs) : f ≈ cau_seq.const abs (lim_aux f) :=
λ ε ε0, (exists_forall_ge_and
  (cau_seq.equiv_lim ⟨_, is_cau_seq_re f⟩ _ (half_pos ε0))
  (cau_seq.equiv_lim ⟨_, is_cau_seq_im f⟩ _ (half_pos ε0))).imp $
λ i H j ij, begin
  cases H _ ij with H₁ H₂,
  apply lt_of_le_of_lt (abs_le_abs_re_add_abs_im _),
  dsimp [lim_aux] at *,
  have := add_lt_add H₁ H₂,
  rwa add_halves at this,
end

noncomputable instance : cau_seq.is_complete ℂ abs :=
⟨λ f, ⟨lim_aux f, equiv_lim_aux f⟩⟩

open cau_seq

lemma lim_eq_lim_im_add_lim_re (f : cau_seq ℂ abs) : lim f =
  ↑(lim (cau_seq_re f)) + ↑(lim (cau_seq_im f)) * I :=
lim_eq_of_equiv_const $
calc f ≈ _ : equiv_lim_aux f
... = cau_seq.const abs (↑(lim (cau_seq_re f)) + ↑(lim (cau_seq_im f)) * I) :
  cau_seq.ext (λ _, complex.ext (by simp [lim_aux, cau_seq_re]) (by simp [lim_aux, cau_seq_im]))

lemma lim_re (f : cau_seq ℂ abs) : lim (cau_seq_re f) = (lim f).re :=
by rw [lim_eq_lim_im_add_lim_re]; simp

lemma lim_im (f : cau_seq ℂ abs) : lim (cau_seq_im f) = (lim f).im :=
by rw [lim_eq_lim_im_add_lim_re]; simp

lemma is_cau_seq_conj (f : cau_seq ℂ abs) : is_cau_seq abs (λ n, conj (f n)) :=
λ ε ε0, let ⟨i, hi⟩ := f.2 ε ε0 in
⟨i, λ j hj, by rw [← conj_sub, abs_conj]; exact hi j hj⟩

noncomputable def cau_seq_conj (f : cau_seq ℂ abs) : cau_seq ℂ abs := ⟨_, is_cau_seq_conj f⟩

lemma lim_conj (f : cau_seq ℂ abs) : lim (cau_seq_conj f) = conj (lim f) :=
complex.ext (by simp [cau_seq_conj, (lim_re _).symm, cau_seq_re])
  (by simp [cau_seq_conj, (lim_im _).symm, cau_seq_im, (lim_neg _).symm]; refl)

noncomputable def cau_seq_abs (f : cau_seq ℂ abs) : cau_seq ℝ abs' :=
⟨_, is_cau_seq_abs f.2⟩

lemma lim_abs (f : cau_seq ℂ abs) : lim (cau_seq_abs f) = abs (lim f) :=
lim_eq_of_equiv_const (λ ε ε0,
let ⟨i, hi⟩ := equiv_lim f ε ε0 in
⟨i, λ j hj, lt_of_le_of_lt (abs_abs_sub_le_abs_sub _ _) (hi j hj)⟩)

end complex

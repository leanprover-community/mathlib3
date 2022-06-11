/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
import data.real.sqrt

/-!
# The complex numbers

The complex numbers are modelled as ℝ^2 in the obvious way and it is shown that they form a field
of characteristic zero. The result that the complex numbers are algebraically closed, see
`field_theory.algebraic_closure`.
-/

open_locale big_operators

/-! ### Definition and basic arithmmetic -/

/-- Complex numbers consist of two `real`s: a real part `re` and an imaginary part `im`. -/
structure complex : Type :=
(re : ℝ) (im : ℝ)

notation `ℂ` := complex

namespace complex

open_locale complex_conjugate

noncomputable instance : decidable_eq ℂ := classical.dec_eq _

/-- The equivalence between the complex numbers and `ℝ × ℝ`. -/
@[simps] def equiv_real_prod : ℂ ≃ (ℝ × ℝ) :=
{ to_fun := λ z, ⟨z.re, z.im⟩,
  inv_fun := λ p, ⟨p.1, p.2⟩,
  left_inv := λ ⟨x, y⟩, rfl,
  right_inv := λ ⟨x, y⟩, rfl }

@[simp] theorem eta : ∀ z : ℂ, complex.mk z.re z.im = z
| ⟨a, b⟩ := rfl

@[ext]
theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
| ⟨zr, zi⟩ ⟨_, _⟩ rfl rfl := rfl

theorem ext_iff {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
⟨λ H, by simp [H], and.rec ext⟩

instance : has_coe ℝ ℂ := ⟨λ r, ⟨r, 0⟩⟩

@[simp, norm_cast] lemma of_real_re (r : ℝ) : (r : ℂ).re = r := rfl
@[simp, norm_cast] lemma of_real_im (r : ℝ) : (r : ℂ).im = 0 := rfl
lemma of_real_def (r : ℝ) : (r : ℂ) = ⟨r, 0⟩ := rfl

@[simp, norm_cast] theorem of_real_inj {z w : ℝ} : (z : ℂ) = w ↔ z = w :=
⟨congr_arg re, congr_arg _⟩

theorem of_real_injective : function.injective (coe : ℝ → ℂ) :=
λ z w, congr_arg re

instance : can_lift ℂ ℝ :=
{ cond := λ z, z.im = 0,
  coe := coe,
  prf := λ z hz, ⟨z.re, ext rfl hz.symm⟩ }

/-- The product of a set on the real axis and a set on the imaginary axis of the complex plane,
denoted by `s ×ℂ t`. -/
def _root_.set.re_prod_im (s t : set ℝ) : set ℂ := re ⁻¹' s ∩ im ⁻¹' t

infix ` ×ℂ `:72 := set.re_prod_im

lemma mem_re_prod_im {z : ℂ} {s t : set ℝ} : z ∈ s ×ℂ t ↔ z.re ∈ s ∧ z.im ∈ t := iff.rfl

instance : has_zero ℂ := ⟨(0 : ℝ)⟩
instance : inhabited ℂ := ⟨0⟩

@[simp] lemma zero_re : (0 : ℂ).re = 0 := rfl
@[simp] lemma zero_im : (0 : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma of_real_zero : ((0 : ℝ) : ℂ) = 0 := rfl

@[simp] theorem of_real_eq_zero {z : ℝ} : (z : ℂ) = 0 ↔ z = 0 := of_real_inj
theorem of_real_ne_zero {z : ℝ} : (z : ℂ) ≠ 0 ↔ z ≠ 0 := not_congr of_real_eq_zero

instance : has_one ℂ := ⟨(1 : ℝ)⟩

@[simp] lemma one_re : (1 : ℂ).re = 1 := rfl
@[simp] lemma one_im : (1 : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma of_real_one : ((1 : ℝ) : ℂ) = 1 := rfl

@[simp] theorem of_real_eq_one {z : ℝ} : (z : ℂ) = 1 ↔ z = 1 := of_real_inj
theorem of_real_ne_one {z : ℝ} : (z : ℂ) ≠ 1 ↔ z ≠ 1 := not_congr of_real_eq_one

instance : has_add ℂ := ⟨λ z w, ⟨z.re + w.re, z.im + w.im⟩⟩

@[simp] lemma add_re (z w : ℂ) : (z + w).re = z.re + w.re := rfl
@[simp] lemma add_im (z w : ℂ) : (z + w).im = z.im + w.im := rfl

@[simp] lemma bit0_re (z : ℂ) : (bit0 z).re = bit0 z.re := rfl
@[simp] lemma bit1_re (z : ℂ) : (bit1 z).re = bit1 z.re := rfl
@[simp] lemma bit0_im (z : ℂ) : (bit0 z).im = bit0 z.im := eq.refl _
@[simp] lemma bit1_im (z : ℂ) : (bit1 z).im = bit0 z.im := add_zero _

@[simp, norm_cast] lemma of_real_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
ext_iff.2 $ by simp

@[simp, norm_cast] lemma of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : ℂ) = bit0 r :=
ext_iff.2 $ by simp [bit0]

@[simp, norm_cast] lemma of_real_bit1 (r : ℝ) : ((bit1 r : ℝ) : ℂ) = bit1 r :=
ext_iff.2 $ by simp [bit1]

instance : has_neg ℂ := ⟨λ z, ⟨-z.re, -z.im⟩⟩

@[simp] lemma neg_re (z : ℂ) : (-z).re = -z.re := rfl
@[simp] lemma neg_im (z : ℂ) : (-z).im = -z.im := rfl
@[simp, norm_cast] lemma of_real_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r := ext_iff.2 $ by simp

instance : has_sub ℂ := ⟨λ z w, ⟨z.re - w.re, z.im - w.im⟩⟩

instance : has_mul ℂ := ⟨λ z w, ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp] lemma mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] lemma mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp, norm_cast] lemma of_real_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s := ext_iff.2 $ by simp

lemma of_real_mul_re (r : ℝ) (z : ℂ) : (↑r * z).re = r * z.re := by simp
lemma of_real_mul_im (r : ℝ) (z : ℂ) : (↑r * z).im = r * z.im := by simp
lemma of_real_mul' (r : ℝ) (z : ℂ) : (↑r * z) = ⟨r * z.re, r * z.im⟩ :=
ext (of_real_mul_re _ _) (of_real_mul_im _ _)

/-! ### The imaginary unit, `I` -/

/-- The imaginary unit. -/
def I : ℂ := ⟨0, 1⟩

@[simp] lemma I_re : I.re = 0 := rfl
@[simp] lemma I_im : I.im = 1 := rfl

@[simp] lemma I_mul_I : I * I = -1 := ext_iff.2 $ by simp
lemma I_mul (z : ℂ) : I * z = ⟨-z.im, z.re⟩ :=
ext_iff.2 $ by simp

lemma I_ne_zero : (I : ℂ) ≠ 0 := mt (congr_arg im) zero_ne_one.symm

lemma mk_eq_add_mul_I (a b : ℝ) : complex.mk a b = a + b * I :=
ext_iff.2 $ by simp

@[simp] lemma re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z :=
ext_iff.2 $ by simp

lemma mul_I_re (z : ℂ) : (z * I).re = -z.im := by simp
lemma mul_I_im (z : ℂ) : (z * I).im = z.re := by simp
lemma I_mul_re (z : ℂ) : (I * z).re = -z.im := by simp
lemma I_mul_im (z : ℂ) : (I * z).im = z.re := by simp

/-! ### Commutative ring instance and lemmas -/

/- We use a nonstandard formula for the `ℕ` and `ℤ` actions to make sure there is no
diamond from the other actions they inherit through the `ℝ`-action on `ℂ` and action transitivity
defined in `data.complex.module.lean`. -/
instance : comm_ring ℂ :=
by refine_struct
  { zero := (0 : ℂ),
    add := (+),
    neg := has_neg.neg,
    sub := has_sub.sub,
    one := 1,
    mul := (*),
    zero_add := λ z, by { apply ext_iff.2, simp },
    add_zero := λ z, by { apply ext_iff.2, simp },
    nsmul := λ n z, ⟨n • z.re - 0 * z.im, n • z.im + 0 * z.re⟩,
    npow := @npow_rec _ ⟨(1 : ℂ)⟩ ⟨(*)⟩,
    zsmul := λ n z, ⟨n • z.re - 0 * z.im, n • z.im + 0 * z.re⟩ };
intros; try { refl }; apply ext_iff.2; split; simp; {ring1 <|> ring_nf}

/-- This shortcut instance ensures we do not find `add_comm_group` via the noncomputable
`complex.normed_group` instance. -/
instance : add_comm_group ℂ := by apply_instance

/-- This shortcut instance ensures we do not find `ring` via the noncomputable `complex.field`
instance. -/
instance : ring ℂ := by apply_instance

/-- The "real part" map, considered as an additive group homomorphism. -/
def re_add_group_hom : ℂ →+ ℝ :=
{ to_fun := re,
  map_zero' := zero_re,
  map_add' := add_re }

@[simp] lemma coe_re_add_group_hom : (re_add_group_hom : ℂ → ℝ) = re := rfl

/-- The "imaginary part" map, considered as an additive group homomorphism. -/
def im_add_group_hom : ℂ →+ ℝ :=
{ to_fun := im,
  map_zero' := zero_im,
  map_add' := add_im }

@[simp] lemma coe_im_add_group_hom : (im_add_group_hom : ℂ → ℝ) = im := rfl

@[simp] lemma I_pow_bit0 (n : ℕ) : I ^ (bit0 n) = (-1) ^ n :=
by rw [pow_bit0', I_mul_I]

@[simp] lemma I_pow_bit1 (n : ℕ) : I ^ (bit1 n) = (-1) ^ n * I :=
by rw [pow_bit1', I_mul_I]

/-! ### Complex conjugation -/

/-- This defines the complex conjugate as the `star` operation of the `star_ring ℂ`. It
is recommended to use the ring endomorphism version `star_ring_end`, available under the
notation `conj` in the locale `complex_conjugate`. -/
instance : star_ring ℂ :=
{ star := λ z, ⟨z.re, -z.im⟩,
  star_involutive := λ x, by simp only [eta, neg_neg],
  star_mul := λ a b, by ext; simp [add_comm]; ring,
  star_add := λ a b, by ext; simp [add_comm] }

@[simp] lemma conj_re (z : ℂ) : (conj z).re = z.re := rfl
@[simp] lemma conj_im (z : ℂ) : (conj z).im = -z.im := rfl

lemma conj_of_real (r : ℝ) : conj (r : ℂ) = r := ext_iff.2 $ by simp [conj]

@[simp] lemma conj_I : conj I = -I := ext_iff.2 $ by simp

lemma conj_bit0 (z : ℂ) : conj (bit0 z) = bit0 (conj z) := ext_iff.2 $ by simp [bit0]
lemma conj_bit1 (z : ℂ) : conj (bit1 z) = bit1 (conj z) := ext_iff.2 $ by simp [bit0]

@[simp] lemma conj_neg_I : conj (-I) = I := ext_iff.2 $ by simp

lemma eq_conj_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
⟨λ h, ⟨z.re, ext rfl $ eq_zero_of_neg_eq (congr_arg im h)⟩,
 λ ⟨h, e⟩, by rw [e, conj_of_real]⟩

lemma eq_conj_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
eq_conj_iff_real.trans ⟨by rintro ⟨r, rfl⟩; simp, λ h, ⟨_, h.symm⟩⟩

lemma eq_conj_iff_im {z : ℂ} : conj z = z ↔ z.im = 0 :=
⟨λ h, add_self_eq_zero.mp (neg_eq_iff_add_eq_zero.mp (congr_arg im h)),
  λ h, ext rfl (neg_eq_iff_add_eq_zero.mpr (add_self_eq_zero.mpr h))⟩

-- `simp_nf` complains about this being provable by `is_R_or_C.star_def` even
-- though it's not imported by this file.
@[simp, nolint simp_nf] lemma star_def : (has_star.star : ℂ → ℂ) = conj := rfl

/-! ### Norm squared -/

/-- The norm squared function. -/
@[pp_nodot] def norm_sq : ℂ →*₀ ℝ :=
{ to_fun := λ z, z.re * z.re + z.im * z.im,
  map_zero' := by simp,
  map_one' := by simp,
  map_mul' := λ z w, by { dsimp, ring } }

lemma norm_sq_apply (z : ℂ) : norm_sq z = z.re * z.re + z.im * z.im := rfl

@[simp] lemma norm_sq_of_real (r : ℝ) : norm_sq r = r * r :=
by simp [norm_sq]

@[simp] lemma norm_sq_mk (x y : ℝ) : norm_sq ⟨x, y⟩ = x * x + y * y := rfl

lemma norm_sq_add_mul_I (x y : ℝ) : norm_sq (x + y * I) = x ^ 2 + y ^ 2 :=
by rw [← mk_eq_add_mul_I, norm_sq_mk, sq, sq]

lemma norm_sq_eq_conj_mul_self {z : ℂ} : (norm_sq z : ℂ) = conj z * z :=
by { ext; simp [norm_sq, mul_comm], }

@[simp] lemma norm_sq_zero : norm_sq 0 = 0 := norm_sq.map_zero
@[simp] lemma norm_sq_one : norm_sq 1 = 1 := norm_sq.map_one
@[simp] lemma norm_sq_I : norm_sq I = 1 := by simp [norm_sq]

lemma norm_sq_nonneg (z : ℂ) : 0 ≤ norm_sq z :=
add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

lemma norm_sq_eq_zero {z : ℂ} : norm_sq z = 0 ↔ z = 0 :=
⟨λ h, ext
  (eq_zero_of_mul_self_add_mul_self_eq_zero h)
  (eq_zero_of_mul_self_add_mul_self_eq_zero $ (add_comm _ _).trans h),
 λ h, h.symm ▸ norm_sq_zero⟩

@[simp] lemma norm_sq_pos {z : ℂ} : 0 < norm_sq z ↔ z ≠ 0 :=
(norm_sq_nonneg z).lt_iff_ne.trans $ not_congr (eq_comm.trans norm_sq_eq_zero)

@[simp] lemma norm_sq_neg (z : ℂ) : norm_sq (-z) = norm_sq z :=
by simp [norm_sq]

@[simp] lemma norm_sq_conj (z : ℂ) : norm_sq (conj z) = norm_sq z :=
by simp [norm_sq]

lemma norm_sq_mul (z w : ℂ) : norm_sq (z * w) = norm_sq z * norm_sq w :=
norm_sq.map_mul z w

lemma norm_sq_add (z w : ℂ) : norm_sq (z + w) =
  norm_sq z + norm_sq w + 2 * (z * conj w).re :=
by dsimp [norm_sq]; ring

lemma re_sq_le_norm_sq (z : ℂ) : z.re * z.re ≤ norm_sq z :=
le_add_of_nonneg_right (mul_self_nonneg _)

lemma im_sq_le_norm_sq (z : ℂ) : z.im * z.im ≤ norm_sq z :=
le_add_of_nonneg_left (mul_self_nonneg _)

theorem mul_conj (z : ℂ) : z * conj z = norm_sq z :=
ext_iff.2 $ by simp [norm_sq, mul_comm, sub_eq_neg_add, add_comm]

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
ext_iff.2 $ by simp [two_mul]

/-- The coercion `ℝ → ℂ` as a `ring_hom`. -/
def of_real : ℝ →+* ℂ := ⟨coe, of_real_one, of_real_mul, of_real_zero, of_real_add⟩

@[simp] lemma of_real_eq_coe (r : ℝ) : of_real r = r := rfl

@[simp] lemma I_sq : I ^ 2 = -1 := by rw [sq, I_mul_I]

@[simp] lemma sub_re (z w : ℂ) : (z - w).re = z.re - w.re := rfl
@[simp] lemma sub_im (z w : ℂ) : (z - w).im = z.im - w.im := rfl
@[simp, norm_cast] lemma of_real_sub (r s : ℝ) : ((r - s : ℝ) : ℂ) = r - s := ext_iff.2 $ by simp
@[simp, norm_cast] lemma of_real_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : ℂ) = r ^ n :=
by induction n; simp [*, of_real_mul, pow_succ]

theorem sub_conj (z : ℂ) : z - conj z = (2 * z.im : ℝ) * I :=
ext_iff.2 $ by simp [two_mul, sub_eq_add_neg]

lemma norm_sq_sub (z w : ℂ) : norm_sq (z - w) =
  norm_sq z + norm_sq w - 2 * (z * conj w).re :=
by { rw [sub_eq_add_neg, norm_sq_add],
     simp only [ring_hom.map_neg, mul_neg, neg_re,
                tactic.ring.add_neg_eq_sub, norm_sq_neg] }

/-! ### Inversion -/

noncomputable instance : has_inv ℂ := ⟨λ z, conj z * ((norm_sq z)⁻¹:ℝ)⟩

theorem inv_def (z : ℂ) : z⁻¹ = conj z * ((norm_sq z)⁻¹:ℝ) := rfl
@[simp] lemma inv_re (z : ℂ) : (z⁻¹).re = z.re / norm_sq z := by simp [inv_def, division_def]
@[simp] lemma inv_im (z : ℂ) : (z⁻¹).im = -z.im / norm_sq z := by simp [inv_def, division_def]

@[simp, norm_cast] lemma of_real_inv (r : ℝ) : ((r⁻¹ : ℝ) : ℂ) = r⁻¹ :=
ext_iff.2 $ by simp

protected lemma inv_zero : (0⁻¹ : ℂ) = 0 :=
by rw [← of_real_zero, ← of_real_inv, inv_zero]

protected theorem mul_inv_cancel {z : ℂ} (h : z ≠ 0) : z * z⁻¹ = 1 :=
by rw [inv_def, ← mul_assoc, mul_conj, ← of_real_mul,
  mul_inv_cancel (mt norm_sq_eq_zero.1 h), of_real_one]

/-! ### Field instance and lemmas -/

noncomputable instance : field ℂ :=
{ inv := has_inv.inv,
  exists_pair_ne := ⟨0, 1, mt (congr_arg re) zero_ne_one⟩,
  mul_inv_cancel := @complex.mul_inv_cancel,
  inv_zero := complex.inv_zero,
  ..complex.comm_ring }

@[simp] lemma I_zpow_bit0 (n : ℤ) : I ^ (bit0 n) = (-1) ^ n :=
by rw [zpow_bit0', I_mul_I]

@[simp] lemma I_zpow_bit1 (n : ℤ) : I ^ (bit1 n) = (-1) ^ n * I :=
by rw [zpow_bit1', I_mul_I]

lemma div_re (z w : ℂ) : (z / w).re = z.re * w.re / norm_sq w + z.im * w.im / norm_sq w :=
by simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg]
lemma div_im (z w : ℂ) : (z / w).im = z.im * w.re / norm_sq w - z.re * w.im / norm_sq w :=
by simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm]

lemma conj_inv (x : ℂ) : conj (x⁻¹) = (conj x)⁻¹ := star_inv' _

@[simp, norm_cast] lemma of_real_div (r s : ℝ) : ((r / s : ℝ) : ℂ) = r / s :=
of_real.map_div r s

@[simp, norm_cast] lemma of_real_zpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n :=
of_real.map_zpow r n

@[simp] lemma div_I (z : ℂ) : z / I = -(z * I) :=
(div_eq_iff_mul_eq I_ne_zero).2 $ by simp [mul_assoc]

@[simp] lemma inv_I : I⁻¹ = -I :=
by simp [inv_eq_one_div]

@[simp] lemma norm_sq_inv (z : ℂ) : norm_sq z⁻¹ = (norm_sq z)⁻¹ :=
norm_sq.map_inv z

@[simp] lemma norm_sq_div (z w : ℂ) : norm_sq (z / w) = norm_sq z / norm_sq w :=
norm_sq.map_div z w

/-! ### Cast lemmas -/

@[simp, norm_cast] theorem of_real_nat_cast (n : ℕ) : ((n : ℝ) : ℂ) = n :=
map_nat_cast of_real n

@[simp, norm_cast] lemma nat_cast_re (n : ℕ) : (n : ℂ).re = n :=
by rw [← of_real_nat_cast, of_real_re]

@[simp, norm_cast] lemma nat_cast_im (n : ℕ) : (n : ℂ).im = 0 :=
by rw [← of_real_nat_cast, of_real_im]

@[simp, norm_cast] theorem of_real_int_cast (n : ℤ) : ((n : ℝ) : ℂ) = n :=
of_real.map_int_cast n

@[simp, norm_cast] lemma int_cast_re (n : ℤ) : (n : ℂ).re = n :=
by rw [← of_real_int_cast, of_real_re]

@[simp, norm_cast] lemma int_cast_im (n : ℤ) : (n : ℂ).im = 0 :=
by rw [← of_real_int_cast, of_real_im]

@[simp, norm_cast] theorem of_real_rat_cast (n : ℚ) : ((n : ℝ) : ℂ) = n := map_rat_cast of_real n

@[simp, norm_cast] lemma rat_cast_re (q : ℚ) : (q : ℂ).re = q :=
by rw [← of_real_rat_cast, of_real_re]

@[simp, norm_cast] lemma rat_cast_im (q : ℚ) : (q : ℂ).im = 0 :=
by rw [← of_real_rat_cast, of_real_im]

/-! ### Characteristic zero -/

instance char_zero_complex : char_zero ℂ :=
char_zero_of_inj_zero $ λ n h,
by rwa [← of_real_nat_cast, of_real_eq_zero, nat.cast_eq_zero] at h

/-- A complex number `z` plus its conjugate `conj z` is `2` times its real part. -/
theorem re_eq_add_conj (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 :=
by simp only [add_conj, of_real_mul, of_real_one, of_real_bit0,
     mul_div_cancel_left (z.re:ℂ) two_ne_zero']

/-- A complex number `z` minus its conjugate `conj z` is `2i` times its imaginary part. -/
theorem im_eq_sub_conj (z : ℂ) : (z.im : ℂ) = (z - conj(z))/(2 * I) :=
by simp only [sub_conj, of_real_mul, of_real_one, of_real_bit0, mul_right_comm,
     mul_div_cancel_left _ (mul_ne_zero two_ne_zero' I_ne_zero : 2 * I ≠ 0)]

/-! ### Absolute value -/

/-- The complex absolute value function, defined as the square root of the norm squared. -/
@[pp_nodot] noncomputable def abs (z : ℂ) : ℝ := (norm_sq z).sqrt

local notation `abs'` := has_abs.abs

@[simp, norm_cast] lemma abs_of_real (r : ℝ) : abs r = |r| :=
by simp [abs, norm_sq_of_real, real.sqrt_mul_self_eq_abs]

lemma abs_of_nonneg {r : ℝ} (h : 0 ≤ r) : abs r = r :=
(abs_of_real _).trans (abs_of_nonneg h)

lemma abs_of_nat (n : ℕ) : complex.abs n = n :=
calc complex.abs n = complex.abs (n:ℝ) : by rw [of_real_nat_cast]
  ... = _ : abs_of_nonneg (nat.cast_nonneg n)

lemma mul_self_abs (z : ℂ) : abs z * abs z = norm_sq z :=
real.mul_self_sqrt (norm_sq_nonneg _)

lemma sq_abs (z : ℂ) : abs z ^ 2 = norm_sq z :=
real.sq_sqrt (norm_sq_nonneg _)

@[simp] lemma sq_abs_sub_sq_re (z : ℂ) : abs z ^ 2 - z.re ^ 2 = z.im ^ 2 :=
by rw [sq_abs, norm_sq_apply, ← sq, ← sq, add_sub_cancel']

@[simp] lemma sq_abs_sub_sq_im (z : ℂ) : abs z ^ 2 - z.im ^ 2 = z.re ^ 2 :=
by rw [← sq_abs_sub_sq_re, sub_sub_cancel]

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

lemma abs_ne_zero {z : ℂ} : abs z ≠ 0 ↔ z ≠ 0 :=
not_congr abs_eq_zero

@[simp] lemma abs_conj (z : ℂ) : abs (conj z) = abs z :=
by simp [abs]

@[simp] lemma abs_mul (z w : ℂ) : abs (z * w) = abs z * abs w :=
by rw [abs, norm_sq_mul, real.sqrt_mul (norm_sq_nonneg _)]; refl

/-- `complex.abs` as a `monoid_with_zero_hom`. -/
@[simps] noncomputable def abs_hom : ℂ →*₀ ℝ :=
{ to_fun := abs,
  map_zero' := abs_zero,
  map_one' := abs_one,
  map_mul' := abs_mul }

@[simp] lemma abs_prod {ι : Type*} (s : finset ι) (f : ι → ℂ) :
  abs (s.prod f) = s.prod (λ i, abs (f i)) :=
map_prod abs_hom _ _

@[simp] lemma abs_pow (z : ℂ) (n : ℕ) : abs (z ^ n) = abs z ^ n :=
map_pow abs_hom z n

@[simp] lemma abs_zpow (z : ℂ) (n : ℤ) : abs (z ^ n) = abs z ^ n :=
abs_hom.map_zpow z n

lemma abs_re_le_abs (z : ℂ) : |z.re| ≤ abs z :=
by rw [mul_self_le_mul_self_iff (_root_.abs_nonneg z.re) (abs_nonneg _),
       abs_mul_abs_self, mul_self_abs];
   apply re_sq_le_norm_sq

lemma abs_im_le_abs (z : ℂ) : |z.im| ≤ abs z :=
by rw [mul_self_le_mul_self_iff (_root_.abs_nonneg z.im) (abs_nonneg _),
       abs_mul_abs_self, mul_self_abs];
   apply im_sq_le_norm_sq

lemma re_le_abs (z : ℂ) : z.re ≤ abs z :=
(abs_le.1 (abs_re_le_abs _)).2

lemma im_le_abs (z : ℂ) : z.im ≤ abs z :=
(abs_le.1 (abs_im_le_abs _)).2

@[simp] lemma abs_re_lt_abs {z : ℂ} : |z.re| < abs z ↔ z.im ≠ 0 :=
by rw [abs, real.lt_sqrt (_root_.abs_nonneg _), norm_sq_apply, _root_.sq_abs, ← sq,
  lt_add_iff_pos_right, mul_self_pos]

@[simp] lemma abs_im_lt_abs {z : ℂ} : |z.im| < abs z ↔ z.re ≠ 0 :=
by simpa using @abs_re_lt_abs (z * I)

/--
The **triangle inequality** for complex numbers.
-/
lemma abs_add (z w : ℂ) : abs (z + w) ≤ abs z + abs w :=
(mul_self_le_mul_self_iff (abs_nonneg _)
  (add_nonneg (abs_nonneg _) (abs_nonneg _))).2 $
begin
  rw [mul_self_abs, add_mul_self_eq, mul_self_abs, mul_self_abs,
      add_right_comm, norm_sq_add, add_le_add_iff_left,
      mul_assoc, mul_le_mul_left (@zero_lt_two ℝ _ _)],
  simpa [-mul_re] using re_le_abs (z * conj w)
end

instance : is_absolute_value abs :=
{ abv_nonneg  := abs_nonneg,
  abv_eq_zero := λ _, abs_eq_zero,
  abv_add     := abs_add,
  abv_mul     := abs_mul }
open is_absolute_value

@[simp] lemma abs_abs (z : ℂ) : |(abs z)| = abs z :=
_root_.abs_of_nonneg (abs_nonneg _)

@[simp] lemma abs_pos {z : ℂ} : 0 < abs z ↔ z ≠ 0 := abv_pos abs
@[simp] lemma abs_neg : ∀ z, abs (-z) = abs z := abv_neg abs
lemma abs_sub_comm : ∀ z w, abs (z - w) = abs (w - z) := abv_sub abs
lemma abs_sub_le : ∀ a b c, abs (a - c) ≤ abs (a - b) + abs (b - c) := abv_sub_le abs
@[simp] theorem abs_inv : ∀ z, abs z⁻¹ = (abs z)⁻¹ := abv_inv abs
@[simp] theorem abs_div : ∀ z w, abs (z / w) = abs z / abs w := abv_div abs

lemma abs_abs_sub_le_abs_sub : ∀ z w, |abs z - abs w| ≤ abs (z - w) :=
abs_abv_sub_le_abv_sub abs

lemma abs_le_abs_re_add_abs_im (z : ℂ) : abs z ≤ |z.re| + |z.im| :=
by simpa [re_add_im] using abs_add z.re (z.im * I)

lemma abs_re_div_abs_le_one (z : ℂ) : |z.re / z.abs| ≤ 1 :=
if hz : z = 0 then by simp [hz, zero_le_one]
else by { simp_rw [_root_.abs_div, abs_abs, div_le_iff (abs_pos.2 hz), one_mul, abs_re_le_abs] }

lemma abs_im_div_abs_le_one (z : ℂ) : |z.im / z.abs| ≤ 1 :=
if hz : z = 0 then by simp [hz, zero_le_one]
else by { simp_rw [_root_.abs_div, abs_abs, div_le_iff (abs_pos.2 hz), one_mul, abs_im_le_abs] }

@[simp, norm_cast] lemma abs_cast_nat (n : ℕ) : abs (n : ℂ) = n :=
by rw [← of_real_nat_cast, abs_of_nonneg (nat.cast_nonneg n)]

@[simp, norm_cast] lemma int_cast_abs (n : ℤ) : ↑|n| = abs n :=
by rw [← of_real_int_cast, abs_of_real, int.cast_abs]

lemma norm_sq_eq_abs (x : ℂ) : norm_sq x = abs x ^ 2 :=
by rw [abs, sq, real.mul_self_sqrt (norm_sq_nonneg _)]

/--
We put a partial order on ℂ so that `z ≤ w` exactly if `w - z` is real and nonnegative.
Complex numbers with different imaginary parts are incomparable.
-/
protected def partial_order : partial_order ℂ :=
{ le := λ z w, z.re ≤ w.re ∧ z.im = w.im,
  lt := λ z w, z.re < w.re ∧ z.im = w.im,
  lt_iff_le_not_le := λ z w, by { dsimp, rw lt_iff_le_not_le, tauto },
  le_refl := λ x, ⟨le_rfl, rfl⟩,
  le_trans := λ x y z h₁ h₂, ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩,
  le_antisymm := λ z w h₁ h₂, ext (h₁.1.antisymm h₂.1) h₁.2 }

section complex_order

localized "attribute [instance] complex.partial_order" in complex_order

lemma le_def {z w : ℂ} : z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im := iff.rfl
lemma lt_def {z w : ℂ} : z < w ↔ z.re < w.re ∧ z.im = w.im := iff.rfl

@[simp, norm_cast] lemma real_le_real {x y : ℝ} : (x : ℂ) ≤ (y : ℂ) ↔ x ≤ y := by simp [le_def]

@[simp, norm_cast] lemma real_lt_real {x y : ℝ} : (x : ℂ) < (y : ℂ) ↔ x < y := by simp [lt_def]

@[simp, norm_cast] lemma zero_le_real {x : ℝ} : (0 : ℂ) ≤ (x : ℂ) ↔ 0 ≤ x := real_le_real
@[simp, norm_cast] lemma zero_lt_real {x : ℝ} : (0 : ℂ) < (x : ℂ) ↔ 0 < x := real_lt_real

lemma not_le_iff {z w : ℂ} : ¬(z ≤ w) ↔ w.re < z.re ∨ z.im ≠ w.im :=
by rw [le_def, not_and_distrib, not_le]

lemma not_lt_iff {z w : ℂ} : ¬(z < w) ↔ w.re ≤ z.re ∨ z.im ≠ w.im :=
by rw [lt_def, not_and_distrib, not_lt]

lemma not_le_zero_iff {z : ℂ} : ¬z ≤ 0 ↔ 0 < z.re ∨ z.im ≠ 0 := not_le_iff
lemma not_lt_zero_iff {z : ℂ} : ¬z < 0 ↔ 0 ≤ z.re ∨ z.im ≠ 0 := not_lt_iff

/--
With `z ≤ w` iff `w - z` is real and nonnegative, `ℂ` is an ordered ring.
-/
protected def ordered_comm_ring : ordered_comm_ring ℂ :=
{ zero_le_one := ⟨zero_le_one, rfl⟩,
  add_le_add_left := λ w z h y, ⟨add_le_add_left h.1 _, congr_arg2 (+) rfl h.2⟩,
  mul_pos := λ z w hz hw,
    by simp [lt_def, mul_re, mul_im, ← hz.2, ← hw.2, mul_pos hz.1 hw.1],
  .. complex.partial_order,
  .. complex.comm_ring }

localized "attribute [instance] complex.ordered_comm_ring" in complex_order

/--
With `z ≤ w` iff `w - z` is real and nonnegative, `ℂ` is a star ordered ring.
(That is, a star ring in which the nonnegative elements are those of the form `star z * z`.)
-/
protected def star_ordered_ring : star_ordered_ring ℂ :=
{ nonneg_iff := λ r, by
  { refine ⟨λ hr, ⟨real.sqrt r.re, _⟩, λ h, _⟩,
    { have h₁ : 0 ≤ r.re := by { rw [le_def] at hr, exact hr.1 },
      have h₂ : r.im = 0 := by { rw [le_def] at hr, exact hr.2.symm },
      ext,
      { simp only [of_real_im, star_def, of_real_re, sub_zero, conj_re, mul_re, mul_zero,
                   ←real.sqrt_mul h₁ r.re, real.sqrt_mul_self h₁] },
      { simp only [h₂, add_zero, of_real_im, star_def, zero_mul, conj_im,
                   mul_im, mul_zero, neg_zero] } },
    { obtain ⟨s, rfl⟩ := h,
      simp only [←norm_sq_eq_conj_mul_self, norm_sq_nonneg, zero_le_real, star_def] } },
  ..complex.ordered_comm_ring }

localized "attribute [instance] complex.star_ordered_ring" in complex_order

end complex_order

/-! ### Cauchy sequences -/

theorem is_cau_seq_re (f : cau_seq ℂ abs) : is_cau_seq abs' (λ n, (f n).re) :=
λ ε ε0, (f.cauchy ε0).imp $ λ i H j ij,
lt_of_le_of_lt (by simpa using abs_re_le_abs (f j - f i)) (H _ ij)

theorem is_cau_seq_im (f : cau_seq ℂ abs) : is_cau_seq abs' (λ n, (f n).im) :=
λ ε ε0, (f.cauchy ε0).imp $ λ i H j ij,
lt_of_le_of_lt (by simpa using abs_im_le_abs (f j - f i)) (H _ ij)

/-- The real part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cau_seq_re (f : cau_seq ℂ abs) : cau_seq ℝ abs' :=
⟨_, is_cau_seq_re f⟩

/-- The imaginary part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cau_seq_im (f : cau_seq ℂ abs) : cau_seq ℝ abs' :=
⟨_, is_cau_seq_im f⟩

lemma is_cau_seq_abs {f : ℕ → ℂ} (hf : is_cau_seq abs f) :
  is_cau_seq abs' (abs ∘ f) :=
λ ε ε0, let ⟨i, hi⟩ := hf ε ε0 in
⟨i, λ j hj, lt_of_le_of_lt (abs_abs_sub_le_abs_sub _ _) (hi j hj)⟩

/-- The limit of a Cauchy sequence of complex numbers. -/
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

instance : cau_seq.is_complete ℂ abs :=
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
⟨i, λ j hj, by rw [← ring_hom.map_sub, abs_conj]; exact hi j hj⟩

/-- The complex conjugate of a complex Cauchy sequence, as a complex Cauchy sequence. -/
noncomputable def cau_seq_conj (f : cau_seq ℂ abs) : cau_seq ℂ abs :=
⟨_, is_cau_seq_conj f⟩

lemma lim_conj (f : cau_seq ℂ abs) : lim (cau_seq_conj f) = conj (lim f) :=
complex.ext (by simp [cau_seq_conj, (lim_re _).symm, cau_seq_re])
  (by simp [cau_seq_conj, (lim_im _).symm, cau_seq_im, (lim_neg _).symm]; refl)

/-- The absolute value of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cau_seq_abs (f : cau_seq ℂ abs) : cau_seq ℝ abs' :=
⟨_, is_cau_seq_abs f.2⟩

lemma lim_abs (f : cau_seq ℂ abs) : lim (cau_seq_abs f) = abs (lim f) :=
lim_eq_of_equiv_const (λ ε ε0,
let ⟨i, hi⟩ := equiv_lim f ε ε0 in
⟨i, λ j hj, lt_of_le_of_lt (abs_abs_sub_le_abs_sub _ _) (hi j hj)⟩)

variables {α : Type*} (s : finset α)

@[simp, norm_cast] lemma of_real_prod (f : α → ℝ) :
  ((∏ i in s, f i : ℝ) : ℂ) = ∏ i in s, (f i : ℂ) :=
ring_hom.map_prod of_real _ _

@[simp, norm_cast] lemma of_real_sum (f : α → ℝ) :
  ((∑ i in s, f i : ℝ) : ℂ) = ∑ i in s, (f i : ℂ) :=
ring_hom.map_sum of_real _ _

@[simp] lemma re_sum (f : α → ℂ) : (∑ i in s, f i).re = ∑ i in s, (f i).re :=
re_add_group_hom.map_sum f s

@[simp] lemma im_sum (f : α → ℂ) : (∑ i in s, f i).im = ∑ i in s, (f i).im :=
im_add_group_hom.map_sum f s

end complex

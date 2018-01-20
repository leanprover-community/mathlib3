/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kevin Buzzard

The complex numbers, modelled as R^2 in the obvious way.

TODO: Add topology, and prove that the complexes are a topological ring.
-/
import data.real tactic.ring

structure complex : Type :=
(re : ℝ) (im : ℝ)

notation `ℂ` := complex

namespace complex

@[simp] theorem eta : ∀ z : ℂ, complex.mk z.re z.im = z
| ⟨a, b⟩ := rfl

theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
| ⟨zr, zi⟩ ⟨wr, wi⟩ rfl rfl := rfl

-- simp version

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
lemma of_real_zero : ((0 : ℝ) : ℂ) = 0 := rfl

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
@[simp] lemma of_real_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s := rfl

instance : has_neg ℂ := ⟨λ z, ⟨-z.re, -z.im⟩⟩

@[simp] lemma neg_re (z : ℂ) : (-z).re = -z.re := rfl
@[simp] lemma neg_im (z : ℂ) : (-z).im = -z.im := rfl
@[simp] lemma of_real_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r := ext_iff.2 $ by simp

instance : has_mul ℂ := ⟨λ z w, ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp] lemma mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] lemma mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] lemma of_real_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s := ext_iff.2 $ by simp

lemma mk_eq_add_mul_I (a b : ℝ) : complex.mk a b = a + b * I :=
ext_iff.2 $ by simp

def conj (z : ℂ) : ℂ := ⟨z.re, -z.im⟩

@[simp] lemma conj_re (z : ℂ) : (conj z).re = z.re := rfl
@[simp] lemma conj_im (z : ℂ) : (conj z).im = -z.im := rfl

@[simp] lemma conj_of_real (r : ℝ) : conj r = r :=
ext_iff.2 $ by simp

def norm_sq (z : ℂ) : ℝ := z.re * z.re + z.im * z.im

@[simp] lemma norm_sq_of_real (r : ℝ) : norm_sq r = r * r :=
by simp [norm_sq]

lemma norm_sq_zero : norm_sq 0 = 0 := by simp [norm_sq]
lemma norm_sq_one : norm_sq 1 = 1 := by simp [norm_sq]

lemma norm_sq_nonneg (z : ℂ) : 0 ≤ norm_sq z :=
add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

@[simp] lemma norm_sq_eq_zero {z : ℂ} : norm_sq z = 0 ↔ z = 0 :=
⟨λ h, ext
  (eq_zero_of_mul_self_add_mul_self_eq_zero h)
  (eq_zero_of_mul_self_add_mul_self_eq_zero $ (add_comm _ _).trans h),
 λ h, h.symm ▸ norm_sq_zero⟩

@[simp] lemma norm_sq_pos {z : ℂ} : 0 < norm_sq z ↔ z ≠ 0 :=
by rw [lt_iff_le_and_ne, ne, eq_comm]; simp [norm_sq_nonneg]

theorem mul_conj (z : ℂ) : z * conj z = norm_sq z :=
ext_iff.2 $ by simp [norm_sq, mul_comm]

instance : comm_ring ℂ :=
by refine { zero := 0, add := (+), neg := has_neg.neg, one := 1, mul := (*), ..};
   { intros, apply ext_iff.2; split; simp; ring }

@[simp] lemma sub_re (z w : ℂ) : (z - w).re = z.re - w.re := rfl
@[simp] lemma sub_im (z w : ℂ) : (z - w).im = z.im - w.im := rfl
@[simp] lemma of_real_sub (r s : ℝ) : ((r - s : ℝ) : ℂ) = r - s := rfl

noncomputable instance : has_inv ℂ := ⟨λ z, conj z * ((norm_sq z)⁻¹:ℝ)⟩

theorem inv_def (z : ℂ) : z⁻¹ = conj z * ((norm_sq z)⁻¹:ℝ) := rfl
@[simp] lemma inv_re (z : ℂ) : (z⁻¹).re = z.re / norm_sq z := by simp [inv_def, division_def]
@[simp] lemma inv_im (z : ℂ) : (z⁻¹).im = -z.im / norm_sq z := by simp [inv_def, division_def]

lemma of_real_inv (r : ℝ) : ((r⁻¹ : ℝ) : ℂ) = r⁻¹ :=
ext_iff.2 $ begin
  simp,
  by_cases r = 0, {simp [h]},
  rw [← div_div_eq_div_mul, div_self h, one_div_eq_inv]
end

lemma inv_zero : (0⁻¹ : ℂ) = 0 :=
by rw [← of_real_zero, ← of_real_inv, inv_zero]

theorem mul_inv_cancel {z : ℂ} (h : z ≠ 0) : z * z⁻¹ = 1 :=
by rw [inv_def, ← mul_assoc, mul_conj, ← of_real_mul,
  mul_inv_cancel (mt norm_sq_eq_zero.1 h), of_real_one]

noncomputable instance : discrete_field ℂ :=
{ inv := has_inv.inv,
  zero_ne_one := mt (congr_arg re) zero_ne_one,
  mul_inv_cancel := @mul_inv_cancel,
  inv_mul_cancel := λ z h, by rw [mul_comm, mul_inv_cancel h],
  inv_zero := inv_zero,
  has_decidable_eq := classical.dec_eq _,
  ..complex.comm_ring }

@[simp] theorem of_real_int_cast : ∀ n : ℤ, ((n : ℝ) : ℂ) = n :=
int.eq_cast (λ n, ((n : ℝ) : ℂ)) rfl (by simp)

@[simp] theorem of_real_nat_cast (n : ℕ) : ((n : ℝ) : ℂ) = n :=
by rw [← int.cast_coe_nat, of_real_int_cast]; refl

instance char_zero_complex : char_zero ℂ :=
add_group.char_zero_of_inj_zero $ λ n h,
by rwa [← of_real_nat_cast, of_real_eq_zero, nat.cast_eq_zero] at h

@[simp] theorem of_real_rat_cast : ∀ n : ℚ, ((n : ℝ) : ℂ) = n :=
by apply rat.eq_cast (λ n, ((n : ℝ) : ℂ)); simp

-- TODO : instance : topological_ring ℂ := missing

end complex

/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chris Hughes

The gaussian integers ℤ[i].
-/

import data.zsqrtd.basic data.complex.basic algebra.euclidean_domain
open zsqrtd complex

@[reducible] def gaussian_int : Type := zsqrtd (-1)

local notation `ℤ[i]` := gaussian_int

namespace gaussian_int

instance : has_repr ℤ[i] := ⟨λ x, "⟨" ++ repr x.re ++ ", " ++ repr x.im ++ "⟩"⟩

instance : comm_ring ℤ[i] := zsqrtd.comm_ring

def to_complex (x : ℤ[i]) : ℂ := x.re + x.im * I

instance : has_coe (ℤ[i]) ℂ := ⟨to_complex⟩

lemma to_complex_def (x : ℤ[i]) : (x : ℂ) = x.re + x.im * I := rfl

lemma to_complex_def' (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ) = x + y * I := by simp [to_complex_def]

lemma to_complex_def₂ (x : ℤ[i]) : (x : ℂ) = ⟨x.re, x.im⟩ :=
by apply complex.ext; simp [to_complex_def]

instance to_complex.is_ring_hom : is_ring_hom to_complex:=
by refine_struct {..}; intros; apply complex.ext; simp [to_complex]

instance : is_ring_hom (coe : ℤ[i] → ℂ) := to_complex.is_ring_hom

@[simp] lemma to_real_re (x : ℤ[i]) : ((x.re : ℤ) : ℝ) = (x : ℂ).re := by simp [to_complex_def]
@[simp] lemma to_real_im (x : ℤ[i]) : ((x.im : ℤ) : ℝ) = (x : ℂ).im := by simp [to_complex_def]
@[simp] lemma to_complex_re (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).re = x := by simp [to_complex_def]
@[simp] lemma to_complex_im (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).im = y := by simp [to_complex_def]
@[simp] lemma to_complex_add (x y : ℤ[i]) : ((x + y : ℤ[i]) : ℂ) = x + y := is_ring_hom.map_add coe
@[simp] lemma to_complex_mul (x y : ℤ[i]) : ((x * y : ℤ[i]) : ℂ) = x * y := is_ring_hom.map_mul coe
@[simp] lemma to_complex_one : ((1 : ℤ[i]) : ℂ) = 1 := is_ring_hom.map_one coe
@[simp] lemma to_complex_zero : ((0 : ℤ[i]) : ℂ) = 0 := is_ring_hom.map_zero coe
@[simp] lemma to_complex_neg (x : ℤ[i]) : ((-x : ℤ[i]) : ℂ) = -x := is_ring_hom.map_neg coe
@[simp] lemma to_complex_sub (x y : ℤ[i]) : ((x - y : ℤ[i]) : ℂ) = x - y := is_ring_hom.map_sub coe

@[simp] lemma to_complex_inj {x y : ℤ[i]} : (x : ℂ) = y ↔ x = y :=
by cases x; cases y; simp [to_complex_def₂]

@[simp] lemma to_complex_eq_zero {x : ℤ[i]} : (x : ℂ) = 0 ↔ x = 0 :=
by rw [← to_complex_zero, to_complex_inj]

@[simp] lemma nat_cast_real_norm (x : ℤ[i]) : (x.norm : ℝ) = (x : ℂ).norm_sq :=
by rw [norm, norm_sq]; simp

@[simp] lemma nat_cast_complex_norm (x : ℤ[i]) : (x.norm : ℂ) = (x : ℂ).norm_sq :=
by cases x; rw [norm, norm_sq]; simp

lemma norm_nonneg (x : ℤ[i]) : 0 ≤ norm x := norm_nonneg trivial _

@[simp] lemma norm_eq_zero {x : ℤ[i]} : norm x = 0 ↔ x = 0 :=
by rw [← @int.cast_inj ℝ _ _ _]; simp

lemma norm_pos {x : ℤ[i]} : 0 < norm x ↔ x ≠ 0 :=
by rw [lt_iff_le_and_ne, ne.def, eq_comm, norm_eq_zero]; simp [norm_nonneg]

@[simp] lemma coe_nat_abs_norm (x : ℤ[i]) : (x.norm.nat_abs : ℤ) = x.norm :=
int.nat_abs_of_nonneg (norm_nonneg _)

@[simp] lemma nat_cast_nat_abs_norm {α : Type*} [ring α]
  (x : ℤ[i]) : (x.norm.nat_abs : α) = x.norm :=
by rw [← int.cast_coe_nat, coe_nat_abs_norm]

lemma nat_abs_norm_eq (x : ℤ[i]) : x.norm.nat_abs =
  x.re.nat_abs * x.re.nat_abs + x.im.nat_abs * x.im.nat_abs :=
int.coe_nat_inj $ begin simp, simp [norm] end

protected def div (x y : ℤ[i]) : ℤ[i] :=
let n := (rat.of_int (norm y))⁻¹ in let c := y.conj in
⟨round (rat.of_int (x * c).re * n : ℚ),
 round (rat.of_int (x * c).im * n : ℚ)⟩

instance : has_div ℤ[i] := ⟨gaussian_int.div⟩

lemma div_def (x y : ℤ[i]) : x / y = ⟨round ((x * conj y).re / norm y : ℚ),
  round ((x * conj y).im / norm y : ℚ)⟩ := 
show zsqrtd.mk _ _ = _, by simp [rat.of_int_eq_mk, rat.mk_eq_div, div_eq_mul_inv]

lemma to_complex_div_re (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).re = round ((x / y : ℂ).re) :=
by rw [div_def, ← @rat.cast_round ℝ _ _];
  simp [-rat.cast_round, mul_assoc, div_eq_mul_inv, mul_add, add_mul]

lemma to_complex_div_im (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).im = round ((x / y : ℂ).im) :=
by rw [div_def, ← @rat.cast_round ℝ _ _, ← @rat.cast_round ℝ _ _];
  simp [-rat.cast_round, mul_assoc, div_eq_mul_inv, mul_add, add_mul]

local notation `abs'` := _root_.abs

lemma norm_sq_le_norm_sq_of_re_le_of_im_le {x y : ℂ} (hre : abs' x.re ≤ abs' y.re)
  (him : abs' x.im ≤ abs' y.im) : x.norm_sq ≤ y.norm_sq :=
by rw [norm_sq, norm_sq, ← _root_.abs_mul_self, _root_.abs_mul,
  ← _root_.abs_mul_self y.re, _root_.abs_mul y.re,
  ← _root_.abs_mul_self x.im, _root_.abs_mul x.im,
  ← _root_.abs_mul_self y.im, _root_.abs_mul y.im]; exact
(add_le_add (mul_self_le_mul_self (abs_nonneg _) hre)
  (mul_self_le_mul_self (abs_nonneg _) him))

lemma norm_sq_div_sub_div_lt_one (x y : ℤ[i]) :
  ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ)).norm_sq < 1 :=
calc ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ)).norm_sq =
    ((x / y : ℂ).re - ((x / y : ℤ[i]) : ℂ).re +
    ((x / y : ℂ).im - ((x / y : ℤ[i]) : ℂ).im) * I : ℂ).norm_sq :
      congr_arg _ $ by apply complex.ext; simp
  ... ≤ (1 / 2 + 1 / 2 * I).norm_sq :
  have abs' (2 / (2 * 2) : ℝ) = 1 / 2, by rw _root_.abs_of_nonneg; norm_num,
  norm_sq_le_norm_sq_of_re_le_of_im_le
    (by rw [to_complex_div_re]; simp [norm_sq, this];
      simpa using abs_sub_round (x / y : ℂ).re)
    (by rw [to_complex_div_im]; simp [norm_sq, this];
      simpa using abs_sub_round (x / y : ℂ).im)
  ... < 1 : by simp [norm_sq]; norm_num

protected def mod (x y : ℤ[i]) : ℤ[i] := x - y * (x / y)

instance : has_mod ℤ[i] := ⟨gaussian_int.mod⟩

lemma mod_def (x y : ℤ[i]) : x % y = x - y * (x / y) := rfl

lemma norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) : (x % y).norm < y.norm :=
have (y : ℂ) ≠ 0, by rwa [ne.def, ← to_complex_zero, to_complex_inj],
(@int.cast_lt ℝ _ _ _).1 $
  calc ↑(norm (x % y)) = (x - y * (x / y : ℤ[i]) : ℂ).norm_sq : by simp [mod_def]
  ... = (y : ℂ).norm_sq * (((x / y) - (x / y : ℤ[i])) : ℂ).norm_sq :
    by rw [← norm_sq_mul, mul_sub, mul_div_cancel' _ this]
  ... < (y : ℂ).norm_sq * 1 : mul_lt_mul_of_pos_left (norm_sq_div_sub_div_lt_one _ _)
    (norm_sq_pos.2 this)
  ... = norm y : by simp

lemma nat_abs_norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) :
  (x % y).norm.nat_abs < y.norm.nat_abs :=
int.coe_nat_lt.1 (by simp [-int.coe_nat_lt, norm_mod_lt x hy])

lemma norm_le_norm_mul_left (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) :
  (norm x).nat_abs ≤ (norm (x * y)).nat_abs :=
by rw [norm_mul, int.nat_abs_mul];
  exact le_mul_of_ge_one_right' (nat.zero_le _)
    (int.coe_nat_le.1 (by rw [coe_nat_abs_norm]; exact norm_pos.2 hy))

instance : nonzero_comm_ring ℤ[i] :=
{ zero_ne_one := dec_trivial, ..gaussian_int.comm_ring }

instance : euclidean_domain ℤ[i] :=
{ quotient := (/),
  remainder := (%),
  quotient_zero := λ _, by simp [div_def]; refl,
  quotient_mul_add_remainder_eq := λ _ _, by simp [mod_def],
  r := _,
  r_well_founded := measure_wf (int.nat_abs ∘ norm),
  remainder_lt := nat_abs_norm_mod_lt,
  mul_left_not_lt := λ a b hb0, not_lt_of_ge $ norm_le_norm_mul_left a hb0 }

end gaussian_int

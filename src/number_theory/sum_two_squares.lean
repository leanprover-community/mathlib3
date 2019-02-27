import number_theory.pell data.zmod.quadratic_reciprocity
import algebra.archimedean data.complex.basic

open zsqrtd complex

@[reducible] def gaussian_int : Type := zsqrtd (-1)

namespace gaussian_int

local notation `ℤ[i]` := gaussian_int

instance : has_repr ℤ[i] := ⟨λ x, "⟨" ++ repr x.re ++ ", " ++ repr x.im ++ "⟩"⟩

instance : comm_ring ℤ[i] := zsqrtd.comm_ring

def norm (x : ℤ[i]) : ℕ := x.re.nat_abs * x.re.nat_abs + x.im.nat_abs * x.im.nat_abs

def to_complex (x : ℤ[i]) : ℂ := x.re + x.im * I

instance : has_coe (ℤ[i]) ℂ := ⟨to_complex⟩

lemma to_complex_def (x : ℤ[i]) : (x : ℂ) = x.re + x.im * I := rfl

lemma to_complex_def' (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ) = x + y * I := by simp [to_complex_def]

lemma to_complex_def₂ (x : ℤ[i]) : (x : ℂ) = ⟨x.re, x.im⟩ :=
by apply complex.ext; simp [to_complex_def]

instance to_complex.is_ring_hom : is_ring_hom to_complex:=
by refine_struct {..}; intros; apply complex.ext; simp [to_complex]

instance : is_ring_hom (coe : ℤ[i] → ℂ) := to_complex.is_ring_hom

@[simp] lemma int_cast_re (x : ℤ[i]) : ((x.re : ℤ) : ℝ) = (x : ℂ).re := by simp [to_complex_def]
@[simp] lemma int_cast_im (x : ℤ[i]) : ((x.im : ℤ) : ℝ) = (x : ℂ).im := by simp [to_complex_def]
@[simp] lemma to_complex_re' (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).re = x := by simp [to_complex_def]
@[simp] lemma to_complex_im' (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).im = y := by simp [to_complex_def]
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
by rw [norm, nat.cast_add, ← int.cast_coe_nat, ← int.cast_coe_nat,
  int.nat_abs_mul_self, int.nat_abs_mul_self, complex.norm_sq]; simp

@[simp] lemma nat_cast_complex_norm (x : ℤ[i]) : (x.norm : ℂ) = (x : ℂ).norm_sq :=
by rw [← of_real_nat_cast, nat_cast_real_norm]

@[simp] lemma norm_mul (x y : ℤ[i]) : norm (x * y) = norm x * norm y :=
(@nat.cast_inj ℂ _ _ _ _ _).1 $ by simp

@[simp] lemma norm_eq_zero {x : ℤ[i]} : norm x = 0 ↔ x = 0 :=
by rw [← @nat.cast_inj ℝ _ _ _]; simp

lemma norm_pos {x : ℤ[i]} : 0 < norm x ↔ x ≠ 0 :=
by rw [nat.pos_iff_ne_zero', ne.def, norm_eq_zero]

protected def div (x y : ℤ[i]) : ℤ[i] :=
⟨round ((x * conj y).re / norm y : ℚ),
 round ((x * conj y).im / norm y : ℚ)⟩

instance : has_div ℤ[i] := ⟨gaussian_int.div⟩

lemma div_def (x y : ℤ[i]) : x / y = ⟨round ((x * conj y).re / norm y : ℚ),
 round ((x * conj y).im / norm y : ℚ)⟩ := rfl

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

protected lemma remainder_lt (x y : ℤ[i]) (hy : y ≠ 0) : (x % y).norm < y.norm :=
have (y : ℂ) ≠ 0, by rwa [ne.def, ← to_complex_zero, to_complex_inj],
(@nat.cast_lt ℝ _ _ _).1 $
  calc ↑(norm (x % y)) = (x - y * (x / y : ℤ[i]) : ℂ).norm_sq : by simp [mod_def]
  ... = (y : ℂ).norm_sq * (((x / y) - (x / y : ℤ[i])) : ℂ).norm_sq :
    by rw [← norm_sq_mul, mul_sub, mul_div_cancel' _ this]
  ... < (y : ℂ).norm_sq * 1 : mul_lt_mul_of_pos_left (norm_sq_div_sub_div_lt_one _ _)
    (norm_sq_pos.2 this)
  ... = norm y : by simp

instance : nonzero_comm_ring ℤ[i] :=
{ zero_ne_one := dec_trivial, ..gaussian_int.comm_ring }

instance : euclidean_domain ℤ[i] :=
{ quotient := (/),
  remainder := (%),
  quotient_zero := λ _, by simp [div_def]; refl,
  quotient_mul_add_remainder_eq := λ _ _, by simp [mod_def],
  r := λ x y, norm x < norm y,
  r_well_founded := measure_wf norm,
  remainder_lt := gaussian_int.remainder_lt,
  mul_left_not_lt := λ a b hb0, not_lt_of_ge $
    by rw [norm_mul];
      exact le_mul_of_ge_one_right' (nat.zero_le _) (norm_pos.2 hb0) }

#eval (⟨49, -17⟩ : ℤ[i]) % ⟨12, 11⟩

end gaussian_int

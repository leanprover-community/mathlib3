import number_theory.pell data.zmod.quadratic_reciprocity
import algebra.archimedean data.complex.basic ring_theory.principal_ideal_domain

open zsqrtd complex

@[reducible] def gaussian_int : Type := zsqrtd (-1)

local notation `ℤ[i]` := gaussian_int

namespace gaussian_int

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

lemma norm_nat_cast (x : ℕ) : norm x = x ^ 2 :=
by simp [norm, nat.pow_two]

@[simp] lemma norm_one : norm 1 = 1 := rfl
@[simp] lemma norm_zero : norm 0 = 0 := rfl

lemma norm_eq_one_iff {x : ℤ[i]} : norm x = 1 ↔ is_unit x :=
⟨λ h, is_unit_iff_dvd_one.2 begin
  rw [norm, nat.add_eq_one_iff, ← int.coe_nat_inj', ← int.coe_nat_inj',
    ← int.coe_nat_inj', ← int.coe_nat_inj', int.nat_abs_mul_self,
    int.nat_abs_mul_self] at h,
  cases h,
  { exact ⟨⟨0, -x.im⟩, by simp [zsqrtd.ext, *] at *⟩ },
  { exact ⟨⟨x.re, 0⟩, by simp [zsqrtd.ext, *] at *⟩ }
end,
λ h, let ⟨y, hy⟩ := is_unit_iff_dvd_one.1 h in begin
  have := congr_arg norm hy,
  rw [norm_one, norm_mul, eq_comm, nat.mul_eq_one_iff] at this,
  exact this.1
end⟩

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

lemma norm_le_norm_mul_left (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) :
  norm x ≤ norm (x * y) :=
by rw norm_mul; exact le_mul_of_ge_one_right' (nat.zero_le _) (norm_pos.2 hy)

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
  mul_left_not_lt := λ a b hb0, not_lt_of_ge $ norm_le_norm_mul_left a hb0 }

end gaussian_int

open gaussian_int principal_ideal_domain

lemma sum_two_squares {p : ℕ} (hp : p.prime) (hp1 : p % 4 = 1) :
  ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
let ⟨k, hk⟩ := (zmodp.neg_one_is_square_iff_mod_four_ne_three hp).2 $
  by rw hp1; exact dec_trivial in
have hpk : p ∣ k.val ^ 2 + 1,
  by rw [← zmodp.eq_zero_iff_dvd_nat hp]; simp *,
have hkmul : (k.val ^ 2 + 1 : ℤ[i]) = ⟨k.val, 1⟩ * ⟨k.val, -1⟩ :=
  by simp [pow_two, zsqrtd.ext],
have hpne1 : p ≠ 1, from (ne_of_lt (hp.gt_one)).symm,
have hkltp : 1 + k.val * k.val < p * p,
  from calc 1 + k.val * k.val ≤ k.val + k.val * k.val :
    add_le_add_right (nat.pos_of_ne_zero
      (λ hk0, by clear_aux_decl; simp [*, nat.pow_succ] at *)) _
  ... = k.val * (k.val + 1) : by simp [mul_add]
  ... < p * p : mul_lt_mul k.2 k.2 (nat.succ_pos _) (nat.zero_le _),
have hpk₁ : ¬ (p : ℤ[i]) ∣ ⟨k.val, -1⟩ :=
  λ ⟨x, hx⟩, lt_irrefl (p * x : ℤ[i]).norm $
    calc norm (p * x) = norm ⟨k.val, -1⟩ : congr_arg _ hx.symm
    ... < norm p : by simpa [norm] using hkltp
    ... ≤ norm (p * x) : norm_le_norm_mul_left _
      (λ hx0, (show (-1 : ℤ) ≠ 0, from dec_trivial) $
         by simpa [hx0] using congr_arg zsqrtd.im hx),
have hpk₂ : ¬ (p : ℤ[i]) ∣ ⟨k.val, 1⟩ :=
  λ ⟨x, hx⟩, lt_irrefl (p * x : ℤ[i]).norm $
    calc norm (p * x) = norm ⟨k.val, 1⟩ : congr_arg _ hx.symm
    ... < norm p : by simpa [norm] using hkltp
    ... ≤ norm (p * x) : norm_le_norm_mul_left _
      (λ hx0, (show (-1 : ℤ) ≠ 0, from dec_trivial) $
         by simpa [hx0] using congr_arg zsqrtd.im hx),
have hpu : ¬ is_unit (p : ℤ[i]), from mt norm_eq_one_iff.2 $
  by rw [norm_nat_cast, nat.pow_two, nat.mul_eq_one_iff];
  exact λ h, (ne_of_lt hp.gt_one).symm h.1,
let ⟨y, hy⟩ := hpk in
have hpi : ¬ irreducible (p : ℤ[i]),
  from mt irreducible_iff_prime.1
    (λ hp, by have := hp.2.2 ⟨k.val, 1⟩ ⟨k.val, -1⟩
        ⟨y, by rw [← hkmul, ← nat.cast_mul p, ← hy]; simp⟩;
      clear_aux_decl; tauto),
have hab : ∃ a b, (p : ℤ[i]) = a * b ∧ ¬ is_unit a ∧ ¬ is_unit b,
  by simpa [irreducible, hpu, classical.not_forall, not_or_distrib] using hpi,
let ⟨a, b, hpab, hau, hbu⟩ := hab in
have hnap : norm a = p, from ((mul_eq_prime_pow_two hp
    (mt norm_eq_one_iff.1 hau) (mt norm_eq_one_iff.1 hbu)).1 $
  by rw [← norm_mul, ← hpab, norm_nat_cast]).1,
⟨a.re.nat_abs, a.im.nat_abs, by simpa [norm, nat.pow_two] using hnap⟩

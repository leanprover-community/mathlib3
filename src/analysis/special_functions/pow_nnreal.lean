/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
import analysis.special_functions.pow_real

/-!
# Power function on `ℝ≥0` and `ℝ≥0∞`

We construct the power functions `x ^ y` where
* `x` is a nonnegative real number and `y` is a real number;
* `x` is a number from `[0, +∞]` (a.k.a. `ℝ≥0∞`) and `y` is a real number.

We also prove basic properties of these functions.
-/

noncomputable theory

open_locale classical real nnreal ennreal big_operators complex_conjugate
open finset set

namespace nnreal

/-- The nonnegative real power function `x^y`, defined for `x : ℝ≥0` and `y : ℝ ` as the
restriction of the real power function. For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`,
one sets `0 ^ 0 = 1` and `0 ^ y = 0` for `y ≠ 0`. -/
noncomputable def rpow (x : ℝ≥0) (y : ℝ) : ℝ≥0 :=
⟨(x : ℝ) ^ y, real.rpow_nonneg_of_nonneg x.2 y⟩

noncomputable instance : has_pow ℝ≥0 ℝ := ⟨rpow⟩

@[simp] lemma rpow_eq_pow (x : ℝ≥0) (y : ℝ) : rpow x y = x ^ y := rfl

@[simp, norm_cast] lemma coe_rpow (x : ℝ≥0) (y : ℝ) : ((x ^ y : ℝ≥0) : ℝ) = (x : ℝ) ^ y := rfl

@[simp] lemma rpow_zero (x : ℝ≥0) : x ^ (0 : ℝ) = 1 :=
nnreal.eq $ real.rpow_zero _

@[simp] lemma rpow_eq_zero_iff {x : ℝ≥0} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
begin
  rw [← nnreal.coe_eq, coe_rpow, ← nnreal.coe_eq_zero],
  exact real.rpow_eq_zero_iff_of_nonneg x.2
end

@[simp] lemma zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ≥0) ^ x = 0 :=
nnreal.eq $ real.zero_rpow h

@[simp] lemma rpow_one (x : ℝ≥0) : x ^ (1 : ℝ) = x :=
nnreal.eq $ real.rpow_one _

@[simp] lemma one_rpow (x : ℝ) : (1 : ℝ≥0) ^ x = 1 :=
nnreal.eq $ real.one_rpow _

lemma rpow_add {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z :=
nnreal.eq $ real.rpow_add (pos_iff_ne_zero.2 hx) _ _

lemma rpow_add' (x : ℝ≥0) {y z : ℝ} (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z :=
nnreal.eq $ real.rpow_add' x.2 h

lemma rpow_mul (x : ℝ≥0) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
nnreal.eq $ real.rpow_mul x.2 y z

lemma rpow_neg (x : ℝ≥0) (y : ℝ) : x ^ -y = (x ^ y)⁻¹ :=
nnreal.eq $ real.rpow_neg x.2 _

lemma rpow_neg_one (x : ℝ≥0) : x ^ (-1 : ℝ) = x ⁻¹ :=
by simp [rpow_neg]

lemma rpow_sub {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z :=
nnreal.eq $ real.rpow_sub (pos_iff_ne_zero.2 hx) y z

lemma rpow_sub' (x : ℝ≥0) {y z : ℝ} (h : y - z ≠ 0) :
  x ^ (y - z) = x ^ y / x ^ z :=
nnreal.eq $ real.rpow_sub' x.2 h

lemma rpow_inv_rpow_self {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0) : (x ^ y) ^ (1 / y) = x :=
by field_simp [← rpow_mul]

lemma rpow_self_rpow_inv {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0) : (x ^ (1 / y)) ^ y = x :=
by field_simp [← rpow_mul]

lemma inv_rpow (x : ℝ≥0) (y : ℝ) : (x⁻¹) ^ y = (x ^ y)⁻¹ :=
nnreal.eq $ real.inv_rpow x.2 y

lemma div_rpow (x y : ℝ≥0) (z : ℝ) : (x / y) ^ z = x ^ z / y ^ z :=
nnreal.eq $ real.div_rpow x.2 y.2 z

lemma sqrt_eq_rpow (x : ℝ≥0) : sqrt x = x ^ (1/(2:ℝ)) :=
begin
  refine nnreal.eq _,
  push_cast,
  exact real.sqrt_eq_rpow x.1,
end

@[simp, norm_cast] lemma rpow_nat_cast (x : ℝ≥0) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
nnreal.eq $ by simpa only [coe_rpow, coe_pow] using real.rpow_nat_cast x n

@[simp] lemma rpow_two (x : ℝ≥0) : x ^ (2 : ℝ) = x ^ 2 :=
by { rw ← rpow_nat_cast, simp only [nat.cast_bit0, nat.cast_one] }

lemma mul_rpow {x y : ℝ≥0} {z : ℝ}  : (x*y)^z = x^z * y^z :=
nnreal.eq $ real.mul_rpow x.2 y.2

lemma rpow_le_rpow {x y : ℝ≥0} {z: ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x^z ≤ y^z :=
real.rpow_le_rpow x.2 h₁ h₂

lemma rpow_lt_rpow {x y : ℝ≥0} {z: ℝ} (h₁ : x < y) (h₂ : 0 < z) : x^z < y^z :=
real.rpow_lt_rpow x.2 h₁ h₂

lemma rpow_lt_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
real.rpow_lt_rpow_iff x.2 y.2 hz

lemma rpow_le_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
real.rpow_le_rpow_iff x.2 y.2 hz

lemma le_rpow_one_div_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) :  x ≤ y ^ (1 / z) ↔ x ^ z ≤ y :=
by rw [← rpow_le_rpow_iff hz, rpow_self_rpow_inv hz.ne']

lemma rpow_one_div_le_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) :  x ^ (1 / z) ≤ y ↔ x ≤ y ^ z :=
by rw [← rpow_le_rpow_iff hz, rpow_self_rpow_inv hz.ne']

lemma rpow_lt_rpow_of_exponent_lt {x : ℝ≥0} {y z : ℝ} (hx : 1 < x) (hyz : y < z) : x^y < x^z :=
real.rpow_lt_rpow_of_exponent_lt hx hyz

lemma rpow_le_rpow_of_exponent_le {x : ℝ≥0} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) : x^y ≤ x^z :=
real.rpow_le_rpow_of_exponent_le hx hyz

lemma rpow_lt_rpow_of_exponent_gt {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
  x^y < x^z :=
real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz

lemma rpow_le_rpow_of_exponent_ge {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) :
  x^y ≤ x^z :=
real.rpow_le_rpow_of_exponent_ge hx0 hx1 hyz

lemma rpow_pos {p : ℝ} {x : ℝ≥0} (hx_pos : 0 < x) : 0 < x^p :=
begin
  have rpow_pos_of_nonneg : ∀ {p : ℝ}, 0 < p → 0 < x^p,
  { intros p hp_pos,
    rw ←zero_rpow hp_pos.ne',
    exact rpow_lt_rpow hx_pos hp_pos },
  rcases lt_trichotomy 0 p with hp_pos|rfl|hp_neg,
  { exact rpow_pos_of_nonneg hp_pos },
  { simp only [zero_lt_one, rpow_zero] },
  { rw [←neg_neg p, rpow_neg, inv_pos],
    exact rpow_pos_of_nonneg (neg_pos.mpr hp_neg) },
end

lemma rpow_lt_one {x : ℝ≥0} {z : ℝ} (hx1 : x < 1) (hz : 0 < z) : x^z < 1 :=
real.rpow_lt_one (coe_nonneg x) hx1 hz

lemma rpow_le_one {x : ℝ≥0} {z : ℝ} (hx2 : x ≤ 1) (hz : 0 ≤ z) : x^z ≤ 1 :=
real.rpow_le_one x.2 hx2 hz

lemma rpow_lt_one_of_one_lt_of_neg {x : ℝ≥0} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x^z < 1 :=
real.rpow_lt_one_of_one_lt_of_neg hx hz

lemma rpow_le_one_of_one_le_of_nonpos {x : ℝ≥0} {z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x^z ≤ 1 :=
real.rpow_le_one_of_one_le_of_nonpos hx hz

lemma one_lt_rpow {x : ℝ≥0} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x^z :=
real.one_lt_rpow hx hz

lemma one_le_rpow {x : ℝ≥0} {z : ℝ} (h : 1 ≤ x) (h₁ : 0 ≤ z) : 1 ≤ x^z :=
real.one_le_rpow h h₁

lemma one_lt_rpow_of_pos_of_lt_one_of_neg {x : ℝ≥0} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1)
  (hz : z < 0) : 1 < x^z :=
real.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz

lemma one_le_rpow_of_pos_of_le_one_of_nonpos {x : ℝ≥0} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1)
  (hz : z ≤ 0) : 1 ≤ x^z :=
real.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 hz

lemma rpow_le_self_of_le_one {x : ℝ≥0} {z : ℝ} (hx : x ≤ 1) (h_one_le : 1 ≤ z) : x ^ z ≤ x :=
begin
  rcases eq_bot_or_bot_lt x with rfl | (h : 0 < x),
  { have : z ≠ 0 := by linarith,
    simp [this] },
  nth_rewrite 1 ←nnreal.rpow_one x,
  exact nnreal.rpow_le_rpow_of_exponent_ge h hx h_one_le,
end

lemma rpow_left_injective {x : ℝ} (hx : x ≠ 0) : function.injective (λ y : ℝ≥0, y^x) :=
λ y z hyz, by simpa only [rpow_inv_rpow_self hx] using congr_arg (λ y, y ^ (1 / x)) hyz

lemma rpow_eq_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) : x ^ z = y ^ z ↔ x = y :=
(rpow_left_injective hz).eq_iff

lemma rpow_left_surjective {x : ℝ} (hx : x ≠ 0) : function.surjective (λ y : ℝ≥0, y^x) :=
λ y, ⟨y ^ x⁻¹, by simp_rw [←rpow_mul, _root_.inv_mul_cancel hx, rpow_one]⟩

lemma rpow_left_bijective {x : ℝ} (hx : x ≠ 0) : function.bijective (λ y : ℝ≥0, y^x) :=
⟨rpow_left_injective hx, rpow_left_surjective hx⟩

lemma eq_rpow_one_div_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) :  x = y ^ (1 / z) ↔ x ^ z = y :=
by rw [← rpow_eq_rpow_iff hz, rpow_self_rpow_inv hz]

lemma rpow_one_div_eq_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) :  x ^ (1 / z) = y ↔ x = y ^ z :=
by rw [← rpow_eq_rpow_iff hz, rpow_self_rpow_inv hz]

lemma pow_nat_rpow_nat_inv (x : ℝ≥0) {n : ℕ} (hn : n ≠ 0) :
  (x ^ n) ^ (n⁻¹ : ℝ) = x :=
by { rw [← nnreal.coe_eq, coe_rpow, nnreal.coe_pow], exact real.pow_nat_rpow_nat_inv x.2 hn }

lemma rpow_nat_inv_pow_nat (x : ℝ≥0) {n : ℕ} (hn : n ≠ 0) :
  (x ^ (n⁻¹ : ℝ)) ^ n = x :=
by { rw [← nnreal.coe_eq, nnreal.coe_pow, coe_rpow], exact real.rpow_nat_inv_pow_nat x.2 hn }

lemma _root_.real.to_nnreal_rpow_of_nonneg {x y : ℝ} (hx : 0 ≤ x) :
  real.to_nnreal (x ^ y) = (real.to_nnreal x) ^ y :=
begin
  nth_rewrite 0 ← real.coe_to_nnreal x hx,
  rw [←nnreal.coe_rpow, real.to_nnreal_coe],
end

end nnreal

namespace ennreal

/-- The real power function `x^y` on extended nonnegative reals, defined for `x : ℝ≥0∞` and
`y : ℝ` as the restriction of the real power function if `0 < x < ⊤`, and with the natural values
for `0` and `⊤` (i.e., `0 ^ x = 0` for `x > 0`, `1` for `x = 0` and `⊤` for `x < 0`, and
`⊤ ^ x = 1 / 0 ^ x`). -/
noncomputable def rpow : ℝ≥0∞ → ℝ → ℝ≥0∞
| (some x) y := if x = 0 ∧ y < 0 then ⊤ else (x ^ y : ℝ≥0)
| none     y := if 0 < y then ⊤ else if y = 0 then 1 else 0

noncomputable instance : has_pow ℝ≥0∞ ℝ := ⟨rpow⟩

@[simp] lemma rpow_eq_pow (x : ℝ≥0∞) (y : ℝ) : rpow x y = x ^ y := rfl

@[simp] lemma rpow_zero {x : ℝ≥0∞} : x ^ (0 : ℝ) = 1 :=
by cases x; { dsimp only [(^), rpow], simp [lt_irrefl] }

lemma top_rpow_def (y : ℝ) : (⊤ : ℝ≥0∞) ^ y = if 0 < y then ⊤ else if y = 0 then 1 else 0 :=
rfl

@[simp] lemma top_rpow_of_pos {y : ℝ} (h : 0 < y) : (⊤ : ℝ≥0∞) ^ y = ⊤ :=
by simp [top_rpow_def, h]

@[simp] lemma top_rpow_of_neg {y : ℝ} (h : y < 0) : (⊤ : ℝ≥0∞) ^ y = 0 :=
by simp [top_rpow_def, asymm h, ne_of_lt h]

@[simp] lemma zero_rpow_of_pos {y : ℝ} (h : 0 < y) : (0 : ℝ≥0∞) ^ y = 0 :=
begin
  rw [← ennreal.coe_zero, ← ennreal.some_eq_coe],
  dsimp only [(^), rpow],
  simp [h, asymm h, ne_of_gt h],
end

@[simp] lemma zero_rpow_of_neg {y : ℝ} (h : y < 0) : (0 : ℝ≥0∞) ^ y = ⊤ :=
begin
  rw [← ennreal.coe_zero, ← ennreal.some_eq_coe],
  dsimp only [(^), rpow],
  simp [h, ne_of_gt h],
end

lemma zero_rpow_def (y : ℝ) : (0 : ℝ≥0∞) ^ y = if 0 < y then 0 else if y = 0 then 1 else ⊤ :=
begin
  rcases lt_trichotomy 0 y with H|rfl|H,
  { simp [H, ne_of_gt, zero_rpow_of_pos, lt_irrefl] },
  { simp [lt_irrefl] },
  { simp [H, asymm H, ne_of_lt, zero_rpow_of_neg] }
end

@[simp] lemma zero_rpow_mul_self (y : ℝ) : (0 : ℝ≥0∞) ^ y * 0 ^ y = 0 ^ y :=
by { rw zero_rpow_def, split_ifs, exacts [zero_mul _, one_mul _, top_mul_top] }

@[norm_cast] lemma coe_rpow_of_ne_zero {x : ℝ≥0} (h : x ≠ 0) (y : ℝ) :
  (x : ℝ≥0∞) ^ y = (x ^ y : ℝ≥0) :=
begin
  rw [← ennreal.some_eq_coe],
  dsimp only [(^), rpow],
  simp [h]
end

@[norm_cast] lemma coe_rpow_of_nonneg (x : ℝ≥0) {y : ℝ} (h : 0 ≤ y) :
  (x : ℝ≥0∞) ^ y = (x ^ y : ℝ≥0) :=
begin
  by_cases hx : x = 0,
  { rcases le_iff_eq_or_lt.1 h with H|H,
    { simp [hx, H.symm] },
    { simp [hx, zero_rpow_of_pos H, nnreal.zero_rpow (ne_of_gt H)] } },
  { exact coe_rpow_of_ne_zero hx _ }
end

lemma coe_rpow_def (x : ℝ≥0) (y : ℝ) :
  (x : ℝ≥0∞) ^ y = if x = 0 ∧ y < 0 then ⊤ else (x ^ y : ℝ≥0) := rfl

@[simp] lemma rpow_one (x : ℝ≥0∞) : x ^ (1 : ℝ) = x :=
begin
  cases x,
  { exact dif_pos zero_lt_one },
  { change ite _ _ _ = _,
    simp only [nnreal.rpow_one, some_eq_coe, ite_eq_right_iff, top_ne_coe, and_imp],
    exact λ _, zero_le_one.not_lt }
end

@[simp] lemma one_rpow (x : ℝ) : (1 : ℝ≥0∞) ^ x = 1 :=
by { rw [← coe_one, coe_rpow_of_ne_zero one_ne_zero], simp }

@[simp] lemma rpow_eq_zero_iff {x : ℝ≥0∞} {y : ℝ} :
  x ^ y = 0 ↔ (x = 0 ∧ 0 < y) ∨ (x = ⊤ ∧ y < 0) :=
begin
  cases x,
  { rcases lt_trichotomy y 0 with H|H|H;
    simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt] },
  { by_cases h : x = 0,
    { rcases lt_trichotomy y 0 with H|H|H;
      simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt] },
    { simp [coe_rpow_of_ne_zero h, h] } }
end

@[simp] lemma rpow_eq_top_iff {x : ℝ≥0∞} {y : ℝ} :
  x ^ y = ⊤ ↔ (x = 0 ∧ y < 0) ∨ (x = ⊤ ∧ 0 < y) :=
begin
  cases x,
  { rcases lt_trichotomy y 0 with H|H|H;
    simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt] },
  { by_cases h : x = 0,
    { rcases lt_trichotomy y 0 with H|H|H;
      simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt] },
    { simp [coe_rpow_of_ne_zero h, h] } }
end

lemma rpow_eq_top_iff_of_pos {x : ℝ≥0∞} {y : ℝ} (hy : 0 < y) : x ^ y = ⊤ ↔ x = ⊤ :=
by simp [rpow_eq_top_iff, hy, asymm hy]

lemma rpow_eq_top_of_nonneg (x : ℝ≥0∞) {y : ℝ} (hy0 : 0 ≤ y) : x ^ y = ⊤ → x = ⊤ :=
begin
  rw ennreal.rpow_eq_top_iff,
  intro h,
  cases h,
  { exfalso, rw lt_iff_not_ge at h, exact h.right hy0, },
  { exact h.left, },
end

lemma rpow_ne_top_of_nonneg {x : ℝ≥0∞} {y : ℝ} (hy0 : 0 ≤ y) (h : x ≠ ⊤) : x ^ y ≠ ⊤ :=
mt (ennreal.rpow_eq_top_of_nonneg x hy0) h

lemma rpow_lt_top_of_nonneg {x : ℝ≥0∞} {y : ℝ} (hy0 : 0 ≤ y) (h : x ≠ ⊤) : x ^ y < ⊤ :=
lt_top_iff_ne_top.mpr (ennreal.rpow_ne_top_of_nonneg hy0 h)

lemma rpow_add {x : ℝ≥0∞} (y z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y + z) = x ^ y * x ^ z :=
begin
  cases x, { exact (h'x rfl).elim },
  have : x ≠ 0 := λ h, by simpa [h] using hx,
  simp [coe_rpow_of_ne_zero this, nnreal.rpow_add this]
end

lemma rpow_neg (x : ℝ≥0∞) (y : ℝ) : x ^ -y = (x ^ y)⁻¹ :=
begin
  cases x,
  { rcases lt_trichotomy y 0 with H|H|H;
    simp [top_rpow_of_pos, top_rpow_of_neg, H, neg_pos.mpr] },
  { by_cases h : x = 0,
    { rcases lt_trichotomy y 0 with H|H|H;
      simp [h, zero_rpow_of_pos, zero_rpow_of_neg, H, neg_pos.mpr] },
    { have A : x ^ y ≠ 0, by simp [h],
      simp [coe_rpow_of_ne_zero h, ← coe_inv A, nnreal.rpow_neg] } }
end

lemma rpow_sub {x : ℝ≥0∞} (y z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y - z) = x ^ y / x ^ z :=
by rw [sub_eq_add_neg, rpow_add _ _ hx h'x, rpow_neg, div_eq_mul_inv]

lemma rpow_neg_one (x : ℝ≥0∞) : x ^ (-1 : ℝ) = x ⁻¹ :=
by simp [rpow_neg]

lemma rpow_mul (x : ℝ≥0∞) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
begin
  cases x,
  { rcases lt_trichotomy y 0 with Hy|Hy|Hy;
    rcases lt_trichotomy z 0 with Hz|Hz|Hz;
    simp [Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
          mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg] },
  { by_cases h : x = 0,
    { rcases lt_trichotomy y 0 with Hy|Hy|Hy;
      rcases lt_trichotomy z 0 with Hz|Hz|Hz;
      simp [h, Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
            mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg] },
    { have : x ^ y ≠ 0, by simp [h],
      simp [coe_rpow_of_ne_zero h, coe_rpow_of_ne_zero this, nnreal.rpow_mul] } }
end

@[simp, norm_cast] lemma rpow_nat_cast (x : ℝ≥0∞) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
begin
  cases x,
  { cases n;
    simp [top_rpow_of_pos (nat.cast_add_one_pos _), top_pow (nat.succ_pos _)] },
  { simp [coe_rpow_of_nonneg _ (nat.cast_nonneg n)] }
end

@[simp] lemma rpow_two (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ 2 :=
by { rw ← rpow_nat_cast, simp only [nat.cast_bit0, nat.cast_one] }

lemma mul_rpow_eq_ite (x y : ℝ≥0∞) (z : ℝ) :
  (x * y) ^ z = if (x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0) ∧ z < 0 then ⊤ else x ^ z * y ^ z :=
begin
  rcases eq_or_ne z 0 with rfl|hz, { simp },
  replace hz := hz.lt_or_lt,
  wlog hxy : x ≤ y,
  { convert this y x z hz (le_of_not_le hxy) using 2; simp only [mul_comm, and_comm, or_comm], },
  rcases eq_or_ne x 0 with rfl|hx0,
  { induction y using with_top.rec_top_coe; cases hz with hz hz; simp [*, hz.not_lt] },
  rcases eq_or_ne y 0 with rfl|hy0, { exact (hx0 (bot_unique hxy)).elim },
  induction x using with_top.rec_top_coe, { cases hz with hz hz; simp [hz, top_unique hxy] },
  induction y using with_top.rec_top_coe, { cases hz with hz hz; simp * },
  simp only [*, false_and, and_false, false_or, if_false],
  norm_cast at *,
  rw [coe_rpow_of_ne_zero (mul_ne_zero hx0 hy0), nnreal.mul_rpow]
end

lemma mul_rpow_of_ne_top {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) (z : ℝ) :
  (x * y) ^ z = x^z * y^z :=
by simp [*, mul_rpow_eq_ite]

@[norm_cast] lemma coe_mul_rpow (x y : ℝ≥0) (z : ℝ) :
  ((x : ℝ≥0∞) * y) ^ z = x^z * y^z :=
mul_rpow_of_ne_top coe_ne_top coe_ne_top z

lemma mul_rpow_of_ne_zero {x y : ℝ≥0∞} (hx : x ≠ 0) (hy : y ≠ 0) (z : ℝ) :
  (x * y) ^ z = x ^ z * y ^ z :=
by simp [*, mul_rpow_eq_ite]

lemma mul_rpow_of_nonneg (x y : ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) :
  (x * y) ^ z = x ^ z * y ^ z :=
by simp [hz.not_lt, mul_rpow_eq_ite]

lemma inv_rpow (x : ℝ≥0∞) (y : ℝ) : (x⁻¹) ^ y = (x ^ y)⁻¹ :=
begin
  rcases eq_or_ne y 0 with rfl|hy, { simp only [rpow_zero, inv_one] },
  replace hy := hy.lt_or_lt,
  rcases eq_or_ne x 0 with rfl|h0, { cases hy; simp * },
  rcases eq_or_ne x ⊤ with rfl|h_top, { cases hy; simp * },
  apply ennreal.eq_inv_of_mul_eq_one_left,
  rw [← mul_rpow_of_ne_zero (ennreal.inv_ne_zero.2 h_top) h0, ennreal.inv_mul_cancel h0 h_top,
    one_rpow]
end

lemma div_rpow_of_nonneg (x y : ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) :
  (x / y) ^ z = x ^ z / y ^ z :=
by rw [div_eq_mul_inv, mul_rpow_of_nonneg _ _ hz, inv_rpow, div_eq_mul_inv]

lemma strict_mono_rpow_of_pos {z : ℝ} (h : 0 < z) : strict_mono (λ x : ℝ≥0∞, x ^ z) :=
begin
  intros x y hxy,
  lift x to ℝ≥0 using ne_top_of_lt hxy,
  rcases eq_or_ne y ∞ with rfl|hy,
  { simp only [top_rpow_of_pos h, coe_rpow_of_nonneg _ h.le, coe_lt_top] },
  { lift y to ℝ≥0 using hy,
    simp only [coe_rpow_of_nonneg _ h.le, nnreal.rpow_lt_rpow (coe_lt_coe.1 hxy) h, coe_lt_coe] }
end

lemma monotone_rpow_of_nonneg {z : ℝ} (h : 0 ≤ z) : monotone (λ x : ℝ≥0∞, x ^ z) :=
h.eq_or_lt.elim (λ h0, h0 ▸ by simp only [rpow_zero, monotone_const])
  (λ h0, (strict_mono_rpow_of_pos h0).monotone)

/-- Bundles `λ x : ℝ≥0∞, x ^ y` into an order isomorphism when `y : ℝ` is positive,
where the inverse is `λ x : ℝ≥0∞, x ^ (1 / y)`. -/
@[simps apply] def order_iso_rpow (y : ℝ) (hy : 0 < y) : ℝ≥0∞ ≃o ℝ≥0∞ :=
(strict_mono_rpow_of_pos hy).order_iso_of_right_inverse (λ x, x ^ y) (λ x, x ^ (1 / y))
  (λ x, by { dsimp, rw [←rpow_mul, one_div_mul_cancel hy.ne.symm, rpow_one] })

lemma order_iso_rpow_symm_apply (y : ℝ) (hy : 0 < y) :
  (order_iso_rpow y hy).symm = order_iso_rpow (1 / y) (one_div_pos.2 hy) :=
by { simp only [order_iso_rpow, one_div_one_div], refl }

lemma rpow_le_rpow {x y : ℝ≥0∞} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x^z ≤ y^z :=
monotone_rpow_of_nonneg h₂ h₁

lemma rpow_lt_rpow {x y : ℝ≥0∞} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x^z < y^z :=
strict_mono_rpow_of_pos h₂ h₁

lemma rpow_le_rpow_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
(strict_mono_rpow_of_pos hz).le_iff_le

lemma rpow_lt_rpow_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) :  x ^ z < y ^ z ↔ x < y :=
(strict_mono_rpow_of_pos hz).lt_iff_lt

lemma le_rpow_one_div_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) :  x ≤ y ^ (1 / z) ↔ x ^ z ≤ y :=
begin
  nth_rewrite 0 ←rpow_one x,
  nth_rewrite 0 ←@_root_.mul_inv_cancel _ _ z  hz.ne',
  rw [rpow_mul, ←one_div, @rpow_le_rpow_iff _ _ (1/z) (by simp [hz])],
end

lemma lt_rpow_one_div_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x < y ^ (1 / z) ↔ x ^ z < y :=
begin
  nth_rewrite 0 ←rpow_one x,
  nth_rewrite 0 ←@_root_.mul_inv_cancel _ _ z (ne_of_lt hz).symm,
  rw [rpow_mul, ←one_div, @rpow_lt_rpow_iff _ _ (1/z) (by simp [hz])],
end

lemma rpow_one_div_le_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ (1 / z) ≤ y ↔ x ≤ y ^ z :=
begin
  nth_rewrite 0 ← ennreal.rpow_one y,
  nth_rewrite 1 ← @_root_.mul_inv_cancel _ _ z hz.ne.symm,
  rw [ennreal.rpow_mul, ← one_div, ennreal.rpow_le_rpow_iff (one_div_pos.2 hz)],
end

lemma rpow_lt_rpow_of_exponent_lt {x : ℝ≥0∞} {y z : ℝ} (hx : 1 < x) (hx' : x ≠ ⊤) (hyz : y < z) :
  x^y < x^z :=
begin
  lift x to ℝ≥0 using hx',
  rw [one_lt_coe_iff] at hx,
  simp [coe_rpow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
        nnreal.rpow_lt_rpow_of_exponent_lt hx hyz]
end

lemma rpow_le_rpow_of_exponent_le {x : ℝ≥0∞} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) : x^y ≤ x^z :=
begin
  cases x,
  { rcases lt_trichotomy y 0 with Hy|Hy|Hy;
    rcases lt_trichotomy z 0 with Hz|Hz|Hz;
    simp [Hy, Hz, top_rpow_of_neg, top_rpow_of_pos, le_refl];
    linarith },
  { simp only [one_le_coe_iff, some_eq_coe] at hx,
    simp [coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
          nnreal.rpow_le_rpow_of_exponent_le hx hyz] }
end

lemma rpow_lt_rpow_of_exponent_gt {x : ℝ≥0∞} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
  x^y < x^z :=
begin
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx1 le_top),
  simp only [coe_lt_one_iff, coe_pos] at hx0 hx1,
  simp [coe_rpow_of_ne_zero (ne_of_gt hx0), nnreal.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz]
end

lemma rpow_le_rpow_of_exponent_ge {x : ℝ≥0∞} {y z : ℝ} (hx1 : x ≤ 1) (hyz : z ≤ y) :
  x^y ≤ x^z :=
begin
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx1 coe_lt_top),
  by_cases h : x = 0,
  { rcases lt_trichotomy y 0 with Hy|Hy|Hy;
    rcases lt_trichotomy z 0 with Hz|Hz|Hz;
    simp [Hy, Hz, h, zero_rpow_of_neg, zero_rpow_of_pos, le_refl];
    linarith },
  { rw [coe_le_one_iff] at hx1,
    simp [coe_rpow_of_ne_zero h,
          nnreal.rpow_le_rpow_of_exponent_ge (bot_lt_iff_ne_bot.mpr h) hx1 hyz] }
end

lemma rpow_le_self_of_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (h_one_le : 1 ≤ z) : x ^ z ≤ x :=
begin
  nth_rewrite 1 ←ennreal.rpow_one x,
  exact ennreal.rpow_le_rpow_of_exponent_ge hx h_one_le,
end

lemma le_rpow_self_of_one_le {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (h_one_le : 1 ≤ z) : x ≤ x ^ z :=
begin
  nth_rewrite 0 ←ennreal.rpow_one x,
  exact ennreal.rpow_le_rpow_of_exponent_le hx h_one_le,
end

lemma rpow_pos_of_nonneg {p : ℝ} {x : ℝ≥0∞} (hx_pos : 0 < x) (hp_nonneg : 0 ≤ p) : 0 < x^p :=
begin
  by_cases hp_zero : p = 0,
  { simp [hp_zero, zero_lt_one], },
  { rw ←ne.def at hp_zero,
    have hp_pos := lt_of_le_of_ne hp_nonneg hp_zero.symm,
    rw ←zero_rpow_of_pos hp_pos, exact rpow_lt_rpow hx_pos hp_pos, },
end

lemma rpow_pos {p : ℝ} {x : ℝ≥0∞} (hx_pos : 0 < x) (hx_ne_top : x ≠ ⊤) : 0 < x^p :=
begin
  cases lt_or_le 0 p with hp_pos hp_nonpos,
  { exact rpow_pos_of_nonneg hx_pos (le_of_lt hp_pos), },
  { rw [←neg_neg p, rpow_neg, ennreal.inv_pos],
    exact rpow_ne_top_of_nonneg (right.nonneg_neg_iff.mpr hp_nonpos) hx_ne_top, },
end

lemma rpow_lt_one {x : ℝ≥0∞} {z : ℝ} (hx : x < 1) (hz : 0 < z) : x^z < 1 :=
begin
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx le_top),
  simp only [coe_lt_one_iff] at hx,
  simp [coe_rpow_of_nonneg _ (le_of_lt hz), nnreal.rpow_lt_one hx hz],
end

lemma rpow_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (hz : 0 ≤ z) : x^z ≤ 1 :=
begin
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx coe_lt_top),
  simp only [coe_le_one_iff] at hx,
  simp [coe_rpow_of_nonneg _ hz, nnreal.rpow_le_one hx hz],
end

lemma rpow_lt_one_of_one_lt_of_neg {x : ℝ≥0∞} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x^z < 1 :=
begin
  cases x,
  { simp [top_rpow_of_neg hz, zero_lt_one] },
  { simp only [some_eq_coe, one_lt_coe_iff] at hx,
    simp [coe_rpow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
          nnreal.rpow_lt_one_of_one_lt_of_neg hx hz] },
end

lemma rpow_le_one_of_one_le_of_neg {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : z < 0) : x^z ≤ 1 :=
begin
  cases x,
  { simp [top_rpow_of_neg hz, zero_lt_one] },
  { simp only [one_le_coe_iff, some_eq_coe] at hx,
    simp [coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
          nnreal.rpow_le_one_of_one_le_of_nonpos hx (le_of_lt hz)] },
end

lemma one_lt_rpow {x : ℝ≥0∞} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x^z :=
begin
  cases x,
  { simp [top_rpow_of_pos hz] },
  { simp only [some_eq_coe, one_lt_coe_iff] at hx,
    simp [coe_rpow_of_nonneg _ (le_of_lt hz), nnreal.one_lt_rpow hx hz] }
end

lemma one_le_rpow {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : 0 < z) : 1 ≤ x^z :=
begin
  cases x,
  { simp [top_rpow_of_pos hz] },
  { simp only [one_le_coe_iff, some_eq_coe] at hx,
    simp [coe_rpow_of_nonneg _ (le_of_lt hz), nnreal.one_le_rpow hx (le_of_lt hz)] },
end

lemma one_lt_rpow_of_pos_of_lt_one_of_neg {x : ℝ≥0∞} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1)
  (hz : z < 0) : 1 < x^z :=
begin
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx2 le_top),
  simp only [coe_lt_one_iff, coe_pos] at ⊢ hx1 hx2,
  simp [coe_rpow_of_ne_zero (ne_of_gt hx1), nnreal.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz],
end

lemma one_le_rpow_of_pos_of_le_one_of_neg {x : ℝ≥0∞} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1)
  (hz : z < 0) : 1 ≤ x^z :=
begin
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx2 coe_lt_top),
  simp only [coe_le_one_iff, coe_pos] at ⊢ hx1 hx2,
  simp [coe_rpow_of_ne_zero (ne_of_gt hx1),
        nnreal.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 (le_of_lt hz)],
end

lemma to_nnreal_rpow (x : ℝ≥0∞) (z : ℝ) : (x.to_nnreal) ^ z = (x ^ z).to_nnreal :=
begin
  rcases lt_trichotomy z 0 with H|H|H,
  { cases x, { simp [H, ne_of_lt] },
    by_cases hx : x = 0,
    { simp [hx, H, ne_of_lt] },
    { simp [coe_rpow_of_ne_zero hx] } },
  { simp [H] },
  { cases x, { simp [H, ne_of_gt] },
    simp [coe_rpow_of_nonneg _ (le_of_lt H)] }
end

lemma to_real_rpow (x : ℝ≥0∞) (z : ℝ) : (x.to_real) ^ z = (x ^ z).to_real :=
by rw [ennreal.to_real, ennreal.to_real, ←nnreal.coe_rpow, ennreal.to_nnreal_rpow]

lemma of_real_rpow_of_pos {x p : ℝ} (hx_pos : 0 < x) :
  ennreal.of_real x ^ p = ennreal.of_real (x ^ p) :=
begin
  simp_rw ennreal.of_real,
  rw [coe_rpow_of_ne_zero, coe_eq_coe, real.to_nnreal_rpow_of_nonneg hx_pos.le],
  simp [hx_pos],
end

lemma of_real_rpow_of_nonneg {x p : ℝ} (hx_nonneg : 0 ≤ x) (hp_nonneg : 0 ≤ p) :
  ennreal.of_real x ^ p = ennreal.of_real (x ^ p) :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0], },
  by_cases hx0 : x = 0,
  { rw ← ne.def at hp0,
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg hp0.symm,
    simp [hx0, hp_pos, hp_pos.ne.symm], },
  rw ← ne.def at hx0,
  exact of_real_rpow_of_pos (hx_nonneg.lt_of_ne hx0.symm),
end

lemma rpow_left_injective {x : ℝ} (hx : x ≠ 0) :
  function.injective (λ y : ℝ≥0∞, y^x) :=
begin
  intros y z hyz,
  dsimp only at hyz,
  rw [←rpow_one y, ←rpow_one z, ←_root_.mul_inv_cancel hx, rpow_mul, rpow_mul, hyz],
end

lemma rpow_left_surjective {x : ℝ} (hx : x ≠ 0) :
  function.surjective (λ y : ℝ≥0∞, y^x) :=
λ y, ⟨y ^ x⁻¹, by simp_rw [←rpow_mul, _root_.inv_mul_cancel hx, rpow_one]⟩

lemma rpow_left_bijective {x : ℝ} (hx : x ≠ 0) :
  function.bijective (λ y : ℝ≥0∞, y^x) :=
⟨rpow_left_injective hx, rpow_left_surjective hx⟩

end ennreal

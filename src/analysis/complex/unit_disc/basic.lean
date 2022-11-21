/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.complex.circle
import analysis.normed_space.ball_action

/-!
# Poincaré disc

In this file we define `complex.unit_disc` to be the unit disc in the complex plane. We also
introduce some basic operations on this disc.
-/

open set function metric
open_locale big_operators
noncomputable theory

local notation `conj'` := star_ring_end ℂ

namespace complex

/-- Complex unit disc. -/
@[derive [comm_semigroup, has_distrib_neg, λ α, has_coe α ℂ, topological_space]]
def unit_disc : Type := ball (0 : ℂ) 1
localized "notation `𝔻` := complex.unit_disc" in unit_disc

namespace unit_disc

lemma coe_injective : injective (coe : 𝔻 → ℂ) := subtype.coe_injective

lemma abs_lt_one (z : 𝔻) : abs (z : ℂ) < 1 := mem_ball_zero_iff.1 z.2

lemma abs_ne_one (z : 𝔻) : abs (z : ℂ) ≠ 1 := z.abs_lt_one.ne

lemma norm_sq_lt_one (z : 𝔻) : norm_sq z < 1 :=
@one_pow ℝ _ 2 ▸ (real.sqrt_lt' one_pos).1 z.abs_lt_one

lemma coe_ne_one (z : 𝔻) : (z : ℂ) ≠ 1 :=
ne_of_apply_ne abs $ (map_one abs).symm ▸ z.abs_ne_one

lemma coe_ne_neg_one (z : 𝔻) : (z : ℂ) ≠ -1 :=
ne_of_apply_ne abs $ by { rw [abs.map_neg, map_one], exact z.abs_ne_one }

lemma one_add_coe_ne_zero (z : 𝔻) : (1 + z : ℂ) ≠ 0 :=
mt neg_eq_iff_add_eq_zero.2 z.coe_ne_neg_one.symm

@[simp, norm_cast] lemma coe_mul (z w : 𝔻) : ↑(z * w) = (z * w : ℂ) := rfl

/-- A constructor that assumes `abs z < 1` instead of `dist z 0 < 1` and returns an element 
of `𝔻` instead of `↥metric.ball (0 : ℂ) 1`. -/
def mk (z : ℂ) (hz : abs z < 1) : 𝔻 := ⟨z, mem_ball_zero_iff.2 hz⟩

@[simp] lemma coe_mk (z : ℂ) (hz : abs z < 1) : (mk z hz : ℂ) = z := rfl

@[simp] lemma mk_coe (z : 𝔻) (hz : abs (z : ℂ) < 1 := z.abs_lt_one) :
  mk z hz = z :=
subtype.eta _ _

@[simp] lemma mk_neg (z : ℂ) (hz : abs (-z) < 1) :
  mk (-z) hz = -mk z (abs.map_neg z ▸ hz) :=
rfl

instance : semigroup_with_zero 𝔻 :=
{ zero := mk 0 $ (map_zero _).trans_lt one_pos,
  zero_mul := λ z, coe_injective $ zero_mul _,
  mul_zero := λ z, coe_injective $ mul_zero _,
  .. unit_disc.comm_semigroup}

@[simp] lemma coe_zero : ((0 : 𝔻) : ℂ) = 0 := rfl
@[simp] lemma coe_eq_zero {z : 𝔻} : (z : ℂ) = 0 ↔ z = 0 := coe_injective.eq_iff' coe_zero
instance : inhabited 𝔻 := ⟨0⟩

instance circle_action : mul_action circle 𝔻 := mul_action_sphere_ball

instance is_scalar_tower_circle_circle : is_scalar_tower circle circle 𝔻 :=
is_scalar_tower_sphere_sphere_ball

instance is_scalar_tower_circle : is_scalar_tower circle 𝔻 𝔻 := is_scalar_tower_sphere_ball_ball
instance smul_comm_class_circle : smul_comm_class circle 𝔻 𝔻 := smul_comm_class_sphere_ball_ball
instance smul_comm_class_circle' : smul_comm_class 𝔻 circle 𝔻 := smul_comm_class.symm _ _ _

@[simp, norm_cast] lemma coe_smul_circle (z : circle) (w : 𝔻) : ↑(z • w) = (z * w : ℂ) := rfl

instance closed_ball_action : mul_action (closed_ball (0 : ℂ) 1) 𝔻 := mul_action_closed_ball_ball

instance is_scalar_tower_closed_ball_closed_ball :
  is_scalar_tower (closed_ball (0 : ℂ) 1) (closed_ball (0 : ℂ) 1) 𝔻 :=
is_scalar_tower_closed_ball_closed_ball_ball

instance is_scalar_tower_closed_ball : is_scalar_tower (closed_ball (0 : ℂ) 1) 𝔻 𝔻 :=
is_scalar_tower_closed_ball_ball_ball

instance smul_comm_class_closed_ball : smul_comm_class (closed_ball (0 : ℂ) 1) 𝔻 𝔻 :=
⟨λ a b c, subtype.ext $ mul_left_comm _ _ _⟩

instance smul_comm_class_closed_ball' : smul_comm_class 𝔻 (closed_ball (0 : ℂ) 1) 𝔻 :=
smul_comm_class.symm _ _ _

instance smul_comm_class_circle_closed_ball : smul_comm_class circle (closed_ball (0 : ℂ) 1) 𝔻 :=
smul_comm_class_sphere_closed_ball_ball

instance smul_comm_class_closed_ball_circle : smul_comm_class (closed_ball (0 : ℂ) 1) circle 𝔻 :=
smul_comm_class.symm _ _ _

@[simp, norm_cast]
lemma coe_smul_closed_ball (z : closed_ball (0 : ℂ) 1) (w : 𝔻) : ↑(z • w) = (z * w : ℂ) := rfl

/-- Real part of a point of the unit disc. -/
def re (z : 𝔻) : ℝ := re z

/-- Imaginary part of a point of the unit disc. -/
def im (z : 𝔻) : ℝ := im z

@[simp, norm_cast] lemma re_coe (z : 𝔻) : (z : ℂ).re = z.re := rfl
@[simp, norm_cast] lemma im_coe (z : 𝔻) : (z : ℂ).im = z.im := rfl
@[simp] lemma re_neg (z : 𝔻) : (-z).re = -z.re := rfl
@[simp] lemma im_neg (z : 𝔻) : (-z).im = -z.im := rfl

/-- Conjugate point of the unit disc. -/
def conj (z : 𝔻) : 𝔻 := mk (conj' ↑z) $ (abs_conj z).symm ▸ z.abs_lt_one

@[simp, norm_cast] lemma coe_conj (z : 𝔻) : (z.conj : ℂ) = conj' ↑z := rfl
@[simp] lemma conj_zero : conj 0 = 0 := coe_injective (map_zero conj')
@[simp] lemma conj_conj (z : 𝔻) : conj (conj z) = z := coe_injective $ complex.conj_conj z
@[simp] lemma conj_neg (z : 𝔻) : (-z).conj = -z.conj := rfl
@[simp] lemma re_conj (z : 𝔻) : z.conj.re = z.re := rfl
@[simp] lemma im_conj (z : 𝔻) : z.conj.im = -z.im := rfl
@[simp] lemma conj_mul (z w : 𝔻) : (z * w).conj = z.conj * w.conj := subtype.ext $ map_mul _ _ _

end unit_disc

end complex

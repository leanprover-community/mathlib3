/-
Copyright (c) 2021 Shadman Sakib. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shadman Sakib
-/
import analysis.special_functions.trigonometric.complex
import group_theory.specific_groups.dihedral

/-! # Realization of the dihedral group as isometries of ℂ

The definition `dihedral_to_complex_hom` provides the canonical homomorphism of the dihedral group
into the linear isometries of ℂ. -/

noncomputable theory

open complex dihedral_group

local notation `π` := real.pi

variables (m : ℕ) [fact (0 < m)]

/-- The additive homomorphism embedding `zmod m` in the group of real numbers modulo `2 * π`. -/
def zmod_to_angle : zmod m →+ real.angle :=
zmod.lift m ⟨gmultiples_hom real.angle ↑(2 * π / m),
  begin
    suffices : m • (2 * π / m) = 2 * π,
    { simpa using congr_arg (coe : _ → real.angle) this },
    have : (m: ℝ) ≠ 0 := by exact_mod_cast (fact.out _ : 0 < m).ne',
    field_simp,
    ring,
  end⟩

namespace dihedral_group

/-- A function mapping `dihedral_group` to linear isometries of ℂ.
Auxiliary construction for `dihedral_to_complex_hom`. -/
def to_linear_isometry : dihedral_group m → ℂ ≃ₗᵢ[ℝ] ℂ
| (r i) := rotation (angle_to_circle (zmod_to_angle m i))
| (sr i) := conj_lie * rotation (angle_to_circle (zmod_to_angle m i))

variables {m}

lemma to_linear_isometry_r_mul_r (i j : zmod m) :
  to_linear_isometry m (r i) * to_linear_isometry m (r j) = to_linear_isometry m (r (i + j)) :=
by simp only [to_linear_isometry, (zmod_to_angle m).map_add, angle_to_circle_add, rotation.map_mul]

lemma to_linear_isometry_r_mul_sr (i j : zmod m) :
  to_linear_isometry m (r i) * to_linear_isometry m (sr j) = to_linear_isometry m (sr (j - i)) :=
show rotation _ * (conj_lie * rotation _) = conj_lie * rotation _,
by rw [← mul_assoc, rotation_mul_conj_lie, (zmod_to_angle m).map_sub,
    angle_to_circle_sub, div_eq_mul_inv, mul_comm, rotation.map_mul, mul_assoc]

lemma to_linear_isometry_sr_mul_r (i j : zmod m) :
  to_linear_isometry m (sr i) * to_linear_isometry m (r j) = to_linear_isometry m (sr (i + j)) :=
by simp only [to_linear_isometry, (zmod_to_angle m).map_add, angle_to_circle_add,
  rotation.map_mul, mul_assoc]

lemma to_linear_isometry_sr_mul_sr (i j : zmod m) :
  to_linear_isometry m (sr i) * to_linear_isometry m (sr j) = to_linear_isometry m (r (j - i)) :=
show (conj_lie * rotation _) * (conj_lie * rotation _) = rotation _,
by rw [← mul_assoc, mul_assoc conj_lie, rotation_mul_conj_lie, ← mul_assoc, conj_lie_mul_conj_lie,
    one_mul, ← rotation.map_mul, (zmod_to_angle m).map_sub, angle_to_circle_sub,
    div_eq_mul_inv, mul_comm]

variables (m)

/-- A homomorphism mapping the dihedral group to linear isometries of ℂ. -/
@[simps]
def to_linear_isometry_hom : dihedral_group m →* (ℂ ≃ₗᵢ[ℝ] ℂ) :=
{ to_fun :=  to_linear_isometry m,
  map_one' := by { show to_linear_isometry m (r 0) = _, ext1 z, simp [to_linear_isometry] },
  map_mul' :=
  begin
    rintros (i | i) (j | j);
    simp only [to_linear_isometry_r_mul_r, to_linear_isometry_r_mul_sr,
        to_linear_isometry_sr_mul_r, to_linear_isometry_sr_mul_sr];
    refl,
  end }

end dihedral_group

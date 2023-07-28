/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
import data.fintype.parity
import linear_algebra.matrix.special_linear_group
import analysis.complex.basic
import group_theory.group_action.defs
import linear_algebra.matrix.general_linear_group
import tactic.linear_combination

/-!
# The upper half plane and its automorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `upper_half_plane` to be the upper half plane in `ℂ`.

We furthermore equip it with the structure of an `GL_pos 2 ℝ` action by
fractional linear transformations.

We define the notation `ℍ` for the upper half plane available in the locale
`upper_half_plane` so as not to conflict with the quaternions.
-/

noncomputable theory

open matrix matrix.special_linear_group

open_locale classical big_operators matrix_groups

local attribute [instance] fintype.card_fin_even

/- Disable these instances as they are not the simp-normal form, and having them disabled ensures
we state lemmas in this file without spurious `coe_fn` terms. -/
local attribute [-instance] matrix.special_linear_group.has_coe_to_fun
local attribute [-instance] matrix.general_linear_group.has_coe_to_fun

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _
local notation `↑ₘ[`:1024 R `]` := @coe _ (matrix (fin 2) (fin 2) R) _

local notation `GL(` n `, ` R `)`⁺ := matrix.GL_pos (fin n) R

/-- The open upper half plane -/
@[derive [λ α, has_coe α ℂ]]
def upper_half_plane := {point : ℂ // 0 < point.im}

localized "notation (name := upper_half_plane) `ℍ` := upper_half_plane" in upper_half_plane

namespace upper_half_plane

instance : inhabited ℍ := ⟨⟨complex.I, by simp⟩⟩

instance can_lift : can_lift ℂ ℍ coe (λ z, 0 < z.im) := subtype.can_lift (λ z, 0 < z.im)

/-- Imaginary part -/
def im (z : ℍ) := (z : ℂ).im

/-- Real part -/
def re (z : ℍ) := (z : ℂ).re

/-- Constructor for `upper_half_plane`. It is useful if `⟨z, h⟩` makes Lean use a wrong
typeclass instance. -/
def mk (z : ℂ) (h : 0 < z.im) : ℍ := ⟨z, h⟩

@[simp] lemma coe_im (z : ℍ) : (z : ℂ).im = z.im := rfl

@[simp] lemma coe_re (z : ℍ) : (z : ℂ).re = z.re := rfl

@[simp] lemma mk_re (z : ℂ) (h : 0 < z.im) : (mk z h).re = z.re := rfl
@[simp] lemma mk_im (z : ℂ) (h : 0 < z.im) : (mk z h).im = z.im := rfl
@[simp] lemma coe_mk (z : ℂ) (h : 0 < z.im) : (mk z h : ℂ) = z := rfl
@[simp] lemma mk_coe (z : ℍ) (h : 0 < (z : ℂ).im := z.2) : mk z h = z := subtype.eta z h

lemma re_add_im (z : ℍ) : (z.re + z.im * complex.I : ℂ) = z :=
complex.re_add_im z

lemma im_pos (z : ℍ) : 0 < z.im := z.2

lemma im_ne_zero (z : ℍ) : z.im ≠ 0 := z.im_pos.ne'

lemma ne_zero (z : ℍ) : (z : ℂ) ≠ 0 :=
mt (congr_arg complex.im) z.im_ne_zero

lemma norm_sq_pos (z : ℍ) : 0 < complex.norm_sq (z : ℂ) :=
by { rw complex.norm_sq_pos, exact z.ne_zero }

lemma norm_sq_ne_zero (z : ℍ) : complex.norm_sq (z : ℂ) ≠ 0 := (norm_sq_pos z).ne'

lemma im_inv_neg_coe_pos (z : ℍ) : 0 < ((-z : ℂ)⁻¹).im :=
by simpa using div_pos z.property (norm_sq_pos z)

/-- Numerator of the formula for a fractional linear transformation -/
@[simp] def num (g : GL(2, ℝ)⁺) (z : ℍ) : ℂ := (↑ₘg 0 0 : ℝ) * z + (↑ₘg 0 1 : ℝ)

/-- Denominator of the formula for a fractional linear transformation -/
@[simp] def denom (g : GL(2, ℝ)⁺) (z : ℍ) : ℂ := (↑ₘg 1 0 : ℝ) * z + (↑ₘg 1 1 : ℝ)

lemma linear_ne_zero (cd : fin 2 → ℝ) (z : ℍ) (h : cd ≠ 0) : (cd 0 : ℂ) * z + cd 1 ≠ 0 :=
begin
  contrapose! h,
  have : cd 0 = 0, -- we will need this twice
  { apply_fun complex.im at h,
    simpa only [z.im_ne_zero, complex.add_im, add_zero, coe_im, zero_mul, or_false,
      complex.of_real_im, complex.zero_im, complex.mul_im, mul_eq_zero] using h, },
  simp only [this, zero_mul, complex.of_real_zero, zero_add, complex.of_real_eq_zero] at h,
  ext i,
  fin_cases i; assumption,
end

lemma denom_ne_zero (g : GL(2, ℝ)⁺) (z : ℍ) : denom g z ≠ 0 :=
begin
  intro H,
  have DET := (mem_GL_pos _).1 g.prop,
  have hz := z.prop,
  simp only [general_linear_group.coe_det_apply] at DET,
  have H1 : (↑ₘg 1 0 : ℝ) = 0 ∨ z.im = 0, by simpa using congr_arg complex.im H,
  cases H1,
  { simp only [H1, complex.of_real_zero, denom, coe_fn_eq_coe, zero_mul, zero_add,
    complex.of_real_eq_zero] at H,
    rw [←coe_coe, (matrix.det_fin_two (↑g : matrix (fin 2) (fin 2) ℝ))] at DET,
    simp only [coe_coe,H, H1, mul_zero, sub_zero, lt_self_iff_false] at DET,
    exact DET, },
  { change z.im > 0 at hz,
    linarith, }
end

lemma norm_sq_denom_pos (g : GL(2, ℝ)⁺) (z : ℍ) : 0 < complex.norm_sq (denom g z) :=
complex.norm_sq_pos.mpr (denom_ne_zero g z)

lemma norm_sq_denom_ne_zero (g : GL(2, ℝ)⁺) (z : ℍ) : complex.norm_sq (denom g z) ≠ 0 :=
ne_of_gt (norm_sq_denom_pos g z)

/-- Fractional linear transformation, also known as the Moebius transformation -/
def smul_aux' (g : GL(2, ℝ)⁺) (z : ℍ) : ℂ := num g z / denom g z

lemma smul_aux'_im (g : GL(2, ℝ)⁺) (z : ℍ) :
  (smul_aux' g z).im = ((det ↑ₘg) * z.im) / (denom g z).norm_sq :=
begin
  rw [smul_aux', complex.div_im],
  set NsqBot := (denom g z).norm_sq,
  have : NsqBot ≠ 0,
  { simp only [denom_ne_zero g z, map_eq_zero, ne.def, not_false_iff], },
  field_simp [smul_aux', -coe_coe],
  rw (matrix.det_fin_two (↑ₘg)),
  ring,
end

/-- Fractional linear transformation, also known as the Moebius transformation -/
def smul_aux (g : GL(2, ℝ)⁺) (z : ℍ) : ℍ :=
 ⟨smul_aux' g z, begin
  rw smul_aux'_im,
  convert (mul_pos ((mem_GL_pos _).1 g.prop)
    (div_pos z.im_pos (complex.norm_sq_pos.mpr (denom_ne_zero g z)))),
  simp only [general_linear_group.coe_det_apply, coe_coe],
  ring
end⟩

lemma denom_cocycle (x y : GL(2, ℝ)⁺) (z : ℍ) :
  denom (x * y) z = denom x (smul_aux y z) * denom y z :=
begin
  change _ = (_ * (_ / _) + _) * _,
  field_simp [denom_ne_zero, -denom, -num],
  simp only [matrix.mul, dot_product, fin.sum_univ_succ, denom, num, coe_coe, subgroup.coe_mul,
    general_linear_group.coe_mul, fintype.univ_of_subsingleton, fin.mk_zero,
    finset.sum_singleton, fin.succ_zero_eq_one, complex.of_real_add, complex.of_real_mul],
  ring
end

lemma mul_smul' (x y : GL(2, ℝ)⁺) (z : ℍ) :
  smul_aux (x * y) z = smul_aux x (smul_aux y z) :=
begin
  ext1,
  change _ / _ = (_ * (_ / _) + _) * _,
  rw denom_cocycle,
  field_simp [denom_ne_zero, -denom, -num],
  simp only [matrix.mul, dot_product, fin.sum_univ_succ, num, denom, coe_coe, subgroup.coe_mul,
    general_linear_group.coe_mul, fintype.univ_of_subsingleton, fin.mk_zero,
    finset.sum_singleton, fin.succ_zero_eq_one, complex.of_real_add, complex.of_real_mul],
  ring
end

/-- The action of ` GL_pos 2 ℝ` on the upper half-plane by fractional linear transformations. -/
instance : mul_action (GL(2, ℝ)⁺) ℍ :=
{ smul := smul_aux,
  one_smul := λ z, by { ext1, change _ / _ = _,
   simp [coe_fn_coe_base'] },
  mul_smul := mul_smul' }

section modular_scalar_towers

variable (Γ : subgroup (special_linear_group (fin 2) ℤ))

instance SL_action {R : Type*} [comm_ring R] [algebra R ℝ] : mul_action SL(2, R) ℍ :=
mul_action.comp_hom ℍ $ (special_linear_group.to_GL_pos).comp $ map (algebra_map R ℝ)

instance : has_coe SL(2,ℤ) (GL(2, ℝ)⁺) := ⟨λ g , ((g : SL(2, ℝ)) : (GL(2, ℝ)⁺))⟩

instance SL_on_GL_pos : has_smul SL(2,ℤ) (GL(2, ℝ)⁺) := ⟨λ s g, s * g⟩

lemma SL_on_GL_pos_smul_apply (s : SL(2,ℤ)) (g : (GL(2, ℝ)⁺)) (z : ℍ) :
  (s • g) • z = ( (s : GL(2, ℝ)⁺) * g) • z := rfl

instance SL_to_GL_tower : is_scalar_tower SL(2,ℤ) (GL(2, ℝ)⁺) ℍ :=
{ smul_assoc := by {intros s g z, simp only [SL_on_GL_pos_smul_apply, coe_coe], apply mul_smul',},}

instance subgroup_GL_pos : has_smul Γ (GL(2, ℝ)⁺) := ⟨λ s g, s * g⟩

lemma subgroup_on_GL_pos_smul_apply (s : Γ) (g : (GL(2, ℝ)⁺)) (z : ℍ) :
  (s • g) • z = ( (s : GL(2, ℝ)⁺) * g) • z := rfl

instance subgroup_on_GL_pos : is_scalar_tower Γ (GL(2, ℝ)⁺) ℍ :=
{ smul_assoc :=
  by {intros s g z, simp only [subgroup_on_GL_pos_smul_apply, coe_coe], apply mul_smul',},}

instance subgroup_SL : has_smul Γ SL(2,ℤ) := ⟨λ s g, s * g⟩

lemma subgroup_on_SL_apply (s : Γ) (g : SL(2,ℤ) ) (z : ℍ) :
  (s • g) • z = ( (s : SL(2, ℤ)) * g) • z := rfl

instance subgroup_to_SL_tower : is_scalar_tower Γ SL(2,ℤ) ℍ :=
{ smul_assoc := λ s g z, by { rw subgroup_on_SL_apply, apply mul_action.mul_smul } }

end modular_scalar_towers

lemma special_linear_group_apply {R : Type*} [comm_ring R] [algebra R ℝ] (g : SL(2, R)) (z : ℍ) :
  g • z = mk ((((↑(↑ₘ[R] g 0 0) : ℝ) : ℂ) * z + ((↑(↑ₘ[R] g 0 1) : ℝ) : ℂ)) /
              (((↑(↑ₘ[R] g 1 0) : ℝ) : ℂ) * z + ((↑(↑ₘ[R] g 1 1) : ℝ) : ℂ))) (g • z).property :=
rfl

@[simp] lemma coe_smul (g : GL(2, ℝ)⁺) (z : ℍ) : ↑(g • z) = num g z / denom g z := rfl
@[simp] lemma re_smul (g : GL(2, ℝ)⁺) (z : ℍ) : (g • z).re = (num g z / denom g z).re := rfl
lemma im_smul (g : GL(2, ℝ)⁺) (z : ℍ) : (g • z).im = (num g z / denom g z).im := rfl

lemma im_smul_eq_div_norm_sq (g : GL(2, ℝ)⁺) (z : ℍ) :
  (g • z).im = (det ↑ₘg * z.im) / (complex.norm_sq (denom g z)) := smul_aux'_im g z

@[simp] lemma neg_smul (g : GL(2, ℝ)⁺) (z : ℍ) : -g • z = g • z :=
begin
  ext1,
  change _ / _ = _ / _,
  field_simp [denom_ne_zero, -denom, -num],
  simp only [num, denom, coe_coe, complex.of_real_neg, neg_mul, GL_pos.coe_neg_GL, units.coe_neg,
    pi.neg_apply],
  ring_nf,
end

section SL_modular_action

variables (g : SL(2, ℤ)) (z : ℍ) (Γ : subgroup SL(2,ℤ))

@[simp] lemma sl_moeb (A : SL(2,ℤ)) (z : ℍ) : A • z = (A : (GL(2, ℝ)⁺)) • z := rfl
lemma subgroup_moeb (A : Γ) (z : ℍ) : A • z = (A : (GL(2, ℝ)⁺)) • z := rfl
@[simp] lemma subgroup_to_sl_moeb (A : Γ) (z : ℍ) : A • z = (A : SL(2,ℤ)) • z := rfl

@[simp] lemma SL_neg_smul (g : SL(2,ℤ)) (z : ℍ) : -g • z = g • z :=
begin
simp only [coe_GL_pos_neg, sl_moeb, coe_coe, coe_int_neg, neg_smul],
end

lemma c_mul_im_sq_le_norm_sq_denom (z : ℍ) (g : SL(2, ℝ)) :
  ((↑ₘg 1 0 : ℝ) * (z.im))^2 ≤ complex.norm_sq (denom g z) :=
begin
  let c := (↑ₘg 1 0 : ℝ),
  let d := (↑ₘg 1 1 : ℝ),
  calc (c * z.im)^2 ≤ (c * z.im)^2 + (c * z.re + d)^2 : by nlinarith
                ... = complex.norm_sq (denom g z) : by simp [complex.norm_sq]; ring,
end

lemma special_linear_group.im_smul_eq_div_norm_sq :
  (g • z).im = z.im / (complex.norm_sq (denom g z)) :=
begin
  convert (im_smul_eq_div_norm_sq g z),
  simp only [coe_coe, general_linear_group.coe_det_apply,coe_GL_pos_coe_GL_coe_matrix,
    int.coe_cast_ring_hom,(g : SL(2,ℝ)).prop, one_mul],
end

lemma denom_apply (g : SL(2, ℤ)) (z : ℍ) : denom g z = (↑g : matrix (fin 2) (fin 2) ℤ) 1 0 * z +
  (↑g : matrix (fin 2) (fin 2) ℤ) 1 1 := by simp

end SL_modular_action

section pos_real_action

instance pos_real_action : mul_action {x : ℝ // 0 < x} ℍ :=
{ smul := λ x z, mk ((x : ℝ) • z) $ by simpa using mul_pos x.2 z.2,
  one_smul := λ z, subtype.ext $ one_smul _ _,
  mul_smul := λ x y z, subtype.ext $ mul_smul (x : ℝ) y (z : ℂ) }

variables (x : {x : ℝ // 0 < x}) (z : ℍ)

@[simp] lemma coe_pos_real_smul : ↑(x • z) = (x : ℝ) • (z : ℂ) := rfl
@[simp] lemma pos_real_im : (x • z).im = x * z.im := complex.smul_im _ _
@[simp] lemma pos_real_re : (x • z).re = x * z.re := complex.smul_re _ _

end pos_real_action

section real_add_action

instance : add_action ℝ ℍ :=
{ vadd := λ x z, mk (x + z) $ by simpa using z.im_pos,
  zero_vadd := λ z, subtype.ext $ by simp,
  add_vadd := λ x y z, subtype.ext $ by simp [add_assoc] }

variables (x : ℝ) (z : ℍ)

@[simp] lemma coe_vadd : ↑(x +ᵥ z) = (x + z : ℂ) := rfl
@[simp] lemma vadd_re : (x +ᵥ z).re = x + z.re := rfl
@[simp] lemma vadd_im : (x +ᵥ z).im = z.im := zero_add _

end real_add_action

/- these next few lemmas are *not* flagged `@simp` because of the constructors on the RHS;
instead we use the versions with coercions to `ℂ` as simp lemmas instead. -/
lemma modular_S_smul (z : ℍ) : modular_group.S • z = mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos :=
by { rw special_linear_group_apply, simp [modular_group.S, neg_div, inv_neg], }

lemma modular_T_zpow_smul (z : ℍ) (n : ℤ) : modular_group.T ^ n • z = (n : ℝ) +ᵥ z :=
begin
  rw [←subtype.coe_inj, coe_vadd, add_comm, special_linear_group_apply, coe_mk,
    modular_group.coe_T_zpow],
  simp only [of_apply, cons_val_zero, algebra_map.coe_one, complex.of_real_one, one_mul,
    cons_val_one, head_cons, algebra_map.coe_zero, zero_mul, zero_add, div_one],
end

lemma modular_T_smul (z : ℍ) : modular_group.T • z = (1 : ℝ) +ᵥ z :=
by simpa only [algebra_map.coe_one] using modular_T_zpow_smul z 1

lemma exists_SL2_smul_eq_of_apply_zero_one_eq_zero (g : SL(2, ℝ)) (hc : ↑ₘ[ℝ] g 1 0 = 0) :
  ∃ (u : {x : ℝ // 0 < x}) (v : ℝ),
    ((•) g : ℍ → ℍ) = (λ z, v +ᵥ z) ∘ (λ z, u • z) :=
begin
  obtain ⟨a, b, ha, rfl⟩ := g.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero hc,
  refine ⟨⟨_, mul_self_pos.mpr ha⟩, b * a, _⟩,
  ext1 ⟨z, hz⟩, ext1,
  suffices : ↑a * z * a + b * a = b * a + a * a * z,
  { rw special_linear_group_apply, simpa [add_mul], },
  ring,
end

lemma exists_SL2_smul_eq_of_apply_zero_one_ne_zero (g : SL(2, ℝ)) (hc : ↑ₘ[ℝ] g 1 0 ≠ 0) :
  ∃ (u : {x : ℝ // 0 < x}) (v w : ℝ),
    ((•) g : ℍ → ℍ) = ((+ᵥ) w : ℍ → ℍ) ∘ ((•) modular_group.S : ℍ → ℍ)
                     ∘ ((+ᵥ) v : ℍ → ℍ) ∘ ((•) u : ℍ → ℍ) :=
begin
  have h_denom := denom_ne_zero g,
  induction g using matrix.special_linear_group.fin_two_induction with a b c d h,
  replace hc : c ≠ 0, { simpa using hc, },
  refine ⟨⟨_, mul_self_pos.mpr hc⟩, c * d, a / c, _⟩,
  ext1 ⟨z, hz⟩, ext1,
  suffices : (↑a * z + b) / (↑c * z + d) = a / c - (c * d + ↑c * ↑c * z)⁻¹,
  { rw special_linear_group_apply,
    simpa only [inv_neg, modular_S_smul, subtype.coe_mk, coe_vadd, complex.of_real_mul,
      coe_pos_real_smul, complex.real_smul, function.comp_app, complex.of_real_div] },
  replace hc : (c : ℂ) ≠ 0, { norm_cast, assumption, },
  replace h_denom : ↑c * z + d ≠ 0, { simpa using h_denom ⟨z, hz⟩, },
  have h_aux : (c : ℂ) * d + ↑c * ↑c * z ≠ 0,
  { rw [mul_assoc, ← mul_add, add_comm], exact mul_ne_zero hc h_denom, },
  replace h : (a * d - b * c : ℂ) = (1 : ℂ), { norm_cast, assumption, },
  field_simp,
  linear_combination (-(z * ↑c ^ 2) - ↑c * ↑d) * h,
end

end upper_half_plane

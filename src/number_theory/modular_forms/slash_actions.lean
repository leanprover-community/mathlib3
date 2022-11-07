/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import analysis.complex.upper_half_plane.basic
import linear_algebra.general_linear_group
import linear_algebra.special_linear_group

/-!
# Slash actions

This file defines a class of slash actions, which are families of right actions of a given group
parametrized by some Type. This is modeled on the slash action of `GL_pos (fin 2) ℝ` on the space
of modular forms.
-/

open complex upper_half_plane

open_locale upper_half_plane

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

local notation `GL(` n `, ` R `)`⁺ := matrix.GL_pos (fin n) R

local notation `SL(` n `, ` R `)` := matrix.special_linear_group (fin n) R

/--A general version of the slash action of the space of modular forms.-/
class slash_action (β G α δ γ : Type*) [group G] [has_zero (α → δ)]
[has_one (α → δ)] [has_smul γ δ] [has_add (α → δ)] :=
(map : β → G → (α → δ) → (α → δ))
(mul_zero : ∀ (k : β) (g : G), map k g 0 = 0)
(one_mul : ∀ (k : β) (a : (α → δ)) , map k 1 a = a)
(right_action : ∀ (k : β) (g h : G) (a : α → δ), map k h (map k g a) = map k (g * h) a )
(smul_action : ∀ (k : β) (g : G) (a : α → δ) (z : γ), map k g (z • a) = z • (map k g a))
(add_action : ∀ (k : β) (g : G) (a b :  α → δ), map k g (a + b) = map k g a + map k g b)

/-
instance scaler_tower_slash_action {β G H α δ γ γ' : Type*} [group G] [has_zero (α → δ)]
  [has_one (α → δ)] [has_smul γ δ] [has_add (α → δ)] [group H] [has_smul γ' γ]
  [has_smul γ' δ] [is_scalar_tower γ' γ δ]
  [slash_action β G α δ γ] : slash_action β G α δ γ' := sorry
-/


/--Slash_action induced by a monoid homomorphism.-/
def monoid_hom_slash_action {β G H α δ γ : Type*} [group G] [has_zero (α → δ)]
  [has_one (α → δ)] [has_smul γ δ] [has_add (α → δ)] [group H] [slash_action β G α δ γ]
  (h : H →* G) : slash_action β H α δ γ :=
{ map := λ k g , slash_action.map γ k (h g) ,
  mul_zero := by {intros k g, apply slash_action.mul_zero k (h g), },
  one_mul := by {intros k a, simp only [map_one], apply slash_action.one_mul,},
  right_action := by {simp only [map_mul], intros k g gg a, apply slash_action.right_action,},
  smul_action := by {intros k g a z, apply slash_action.smul_action, },
  add_action := by {intros k g a b, apply slash_action.add_action, }, }

namespace modular_forms

noncomputable theory

/--The weight `k` action of `GL(2, ℝ)⁺` on functions `f : ℍ → ℂ`. -/
def slash (k : ℤ) (γ : GL(2, ℝ)⁺) (f : ℍ → ℂ) (x : ℍ) : ℂ :=
f (γ • x) * (((↑ₘ γ).det) : ℝ)^(k-1) * (upper_half_plane.denom γ x)^(-k)

variables {Γ : subgroup SL(2, ℤ)} {k: ℤ} (f : ℍ → ℂ)

localized "notation (name := modular_forms.slash) f ` ∣[`:100 k `]`:0 γ :100 :=
  modular_forms.slash k γ f" in modular_forms

lemma slash_right_action (k : ℤ) (A B : GL(2, ℝ)⁺) (f : ℍ → ℂ) :
  (f ∣[k] A) ∣[k] B = f ∣[k] (A * B) :=
begin
  ext1,
  simp_rw [slash,(upper_half_plane.denom_cocycle A B x)],
  have e3 : (A * B) • x = A • B • x , by { convert (upper_half_plane.mul_smul' A B x), } ,
  rw e3,
  simp only [upper_half_plane.num, upper_half_plane.denom, of_real_mul, subgroup.coe_mul, coe_coe,
    upper_half_plane.coe_smul, units.coe_mul, matrix.mul_eq_mul, matrix.det_mul,
    upper_half_plane.smul_aux, upper_half_plane.smul_aux', subtype.coe_mk] at *,
  field_simp,
  have : (((↑(↑A : GL (fin 2) ℝ) : (matrix (fin 2) (fin 2) ℝ)).det : ℂ) *
    ((↑(↑B : GL (fin 2) ℝ) : (matrix (fin 2) (fin 2) ℝ)).det : ℂ))^(k-1) =
    ((↑(↑A : GL (fin 2) ℝ) : (matrix (fin 2) (fin 2) ℝ)).det : ℂ)^(k-1) *
    ((↑(↑B : GL (fin 2) ℝ) : (matrix (fin 2) (fin 2) ℝ)).det : ℂ)^(k-1) ,
    by {simp_rw [←mul_zpow]},
  simp_rw [this, ← mul_assoc, ←mul_zpow],
end

lemma slash_add (k : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
  (f + g) ∣[k] A = (f ∣[k] A) + (g ∣[k] A) :=
begin
  ext1,
  simp only [slash, pi.add_apply, denom, coe_coe, zpow_neg],
  ring,
end

lemma slash_mul_one (k : ℤ) (f : ℍ → ℂ) : (f ∣[k] 1) = f :=
begin
 ext1,
 simp [slash],
end

lemma smul_slash (k : ℤ) (A : GL(2, ℝ)⁺) (f : ℍ → ℂ) (c : ℂ) : (c • f) ∣[k] A = c • (f ∣[k] A) :=
begin
  ext1,
  simp_rw slash,
  simp only [slash, algebra.id.smul_eq_mul, matrix.general_linear_group.coe_det_apply,
    pi.smul_apply, subtype.val_eq_coe, coe_coe],
  ring,
end

lemma neg_slash (k : ℤ) (A : GL(2, ℝ)⁺) (f : ℍ → ℂ) : (-f) ∣[k] A = - (f ∣[k] A) :=
begin
  ext1,
  simp [slash],
end

instance : slash_action ℤ GL(2, ℝ)⁺ ℍ ℂ ℂ :=
{ map := slash,
  mul_zero := by {intros k g, funext, simp only [slash, pi.zero_apply, zero_mul], },
  one_mul := by {apply slash_mul_one,},
  right_action := by {apply slash_right_action},
  smul_action := by {apply smul_slash},
  add_action := by {apply slash_add},}

instance subgroup_action (Γ : subgroup SL(2, ℤ)) : slash_action ℤ Γ ℍ ℂ ℂ :=
monoid_hom_slash_action (monoid_hom.comp (matrix.special_linear_group.to_GL_pos)
  (monoid_hom.comp (matrix.special_linear_group.map (int.cast_ring_hom ℝ)) (subgroup.subtype Γ)))

@[simp] lemma subgroup_slash (Γ : subgroup SL(2, ℤ)) (γ  : Γ):
  (slash_action.map ℂ k γ f) = slash k (γ : GL(2,ℝ)⁺) f := rfl

instance SL_action : slash_action ℤ SL(2, ℤ) ℍ ℂ ℂ :=
monoid_hom_slash_action (monoid_hom.comp (matrix.special_linear_group.to_GL_pos)
  (matrix.special_linear_group.map (int.cast_ring_hom ℝ)))

@[simp] lemma SL_slash (γ  : SL(2, ℤ)):
  (slash_action.map ℂ k γ f) = slash k (γ : GL(2,ℝ)⁺) f := rfl

local notation f `∣[`:73 k:0, A `]`  :72 := slash_action.map ℂ k A f

/-- The constant function 1 is invariant under any subgroup of `SL(2, ℤ)`. -/
lemma const_one_form_is_invar (A : SL(2, ℤ)) : (1 : ℍ → ℂ) ∣[(0 : ℤ), A] = (1 : ℍ → ℂ) :=
begin
  rw [SL_slash],
  have : (((↑ₘ(A : GL(2,ℝ)⁺)).det) : ℝ) = 1,
  { simp only [coe_coe,
      matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
      matrix.special_linear_group.det_coe], },
  funext,
  rw [slash, zero_sub, this],
  simp,
end

/-- A function `f : ℍ → ℂ` is weakly modular, of weight `k ∈ ℤ` and level `Γ`, if for every matrix .
 `γ ∈ Γ` we have `f(γ • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`, and it acts on `ℍ`
  via Möbius transformations. -/
lemma slash_action_eq'_iff (k : ℤ) (Γ : subgroup SL(2, ℤ)) (f : ℍ → ℂ) (γ : Γ) :
  ∀ z : ℍ, f ∣[k, γ] z = f z ↔  f (γ • z) = ((↑ₘγ 1 0 : ℝ) * z +(↑ₘγ 1 1 : ℝ))^k * f z :=
begin
  intro z,
  simp only [subgroup_slash, modular_forms.slash],
  convert inv_mul_eq_iff_eq_mul₀ _ using 2,
  { rw mul_comm,
    simp [-matrix.special_linear_group.coe_matrix_coe] },
  { exact zpow_ne_zero _ (denom_ne_zero _ _) },
end

lemma slash_mul (k1 k2 : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
  (f * g) ∣[k1 + k2, A] = (((↑ₘ A).det) : ℝ) • (f ∣[k1, A]) * (g ∣[k2, A]) :=
begin
  ext1,
  simp only [slash_action.map, slash, matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe,
    pi.mul_apply, pi.smul_apply, algebra.smul_mul_assoc, real_smul],
  set d : ℂ := ↑((↑ₘ A).det : ℝ),
  have h1 : d ^ (k1 + k2 - 1) = d * d ^ (k1 - 1) * d ^ (k2 - 1),
  { have : d ≠ 0,
    { dsimp [d],
      norm_cast,
      exact matrix.GL_pos.det_ne_zero A },
    rw [← zpow_one_add₀ this, ← zpow_add₀ this],
    ring_exp },
  have h22 : denom A x ^ (- (k1 + k2)) = denom A x ^ (- k1) * denom A x ^ (- k2),
  { rw [int.neg_add, zpow_add₀],
    exact upper_half_plane.denom_ne_zero A x, },
  rw [h1, h22],
  ring,
end

lemma slash_mul_SL2 (k1 k2 : ℤ) (A : SL(2, ℤ)) (f g : ℍ → ℂ) :
  (f * g) ∣[k1 + k2, A] = (f ∣[k1, A]) * (g ∣[k2, A]) :=
calc (f * g) ∣[k1 + k2, (A : GL(2, ℝ)⁺)] = _ • (f ∣[k1, A]) * (g ∣[k2, A]) : slash_mul _ _ _ _ _
... = (1:ℝ) • (f ∣[k1, A]) * (g ∣[k2, A]) : by simp [-matrix.special_linear_group.coe_matrix_coe]
... = (f ∣[k1, A]) * (g ∣[k2, A]) : by simp

lemma slash_mul_subgroup (k1 k2 : ℤ) (Γ : subgroup SL(2, ℤ)) (A : Γ) (f g : ℍ → ℂ) :
  (f * g) ∣[k1 + k2, A] = (f ∣[k1, A]) * (g ∣[k2, A]) :=
slash_mul_SL2 k1 k2 A f g

end modular_forms

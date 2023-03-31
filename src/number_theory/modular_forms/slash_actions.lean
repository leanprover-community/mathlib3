/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import analysis.complex.upper_half_plane.basic
import linear_algebra.matrix.general_linear_group
import linear_algebra.matrix.special_linear_group
/-!
# Slash actions

This file defines a class of slash actions, which are families of right actions of a given group
parametrized by some Type. This is modeled on the slash action of `GL_pos (fin 2) ℝ` on the space
of modular forms.
-/

open complex upper_half_plane

open_locale upper_half_plane

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

-- like `↑ₘ`, but allows the user to specify the ring `R`. Useful to help Lean elaborate.
local notation `↑ₘ[` R `]` := @coe _ (matrix (fin 2) (fin 2) R) _

local notation `GL(` n `, ` R `)`⁺ := matrix.GL_pos (fin n) R

local notation `SL(` n `, ` R `)` := matrix.special_linear_group (fin n) R

/--A general version of the slash action of the space of modular forms.-/
class slash_action (β G α γ : Type*) [group G] [has_zero α] [has_smul γ α] [has_add α] :=
(map : β → G → α → α)
(zero_slash : ∀ (k : β) (g : G), map k g 0 = 0)
(slash_one : ∀ (k : β) (a : α) , map k 1 a = a)
(right_action : ∀ (k : β) (g h : G) (a : α), map k h (map k g a) = map k (g * h) a )
(smul_action : ∀ (k : β) (g : G) (a : α) (z : γ), map k g (z • a) = z • (map k g a))
(add_action : ∀ (k : β) (g : G) (a b : α), map k g (a + b) = map k g a + map k g b)

/--Slash_action induced by a monoid homomorphism.-/
def monoid_hom_slash_action {β G H α γ : Type*} [group G] [has_zero α] [has_smul γ α] [has_add α]
  [group H] [slash_action β G α γ] (h : H →* G) : slash_action β H α γ :=
{ map := λ k g, slash_action.map γ k (h g),
  zero_slash := λ k g, slash_action.zero_slash k (h g),
  slash_one := λ k a, by simp only [map_one, slash_action.slash_one],
  right_action := λ k g gg a, by simp only [map_mul, slash_action.right_action],
  smul_action := λ _ _, slash_action.smul_action _ _,
  add_action := λ _ g _ _, slash_action.add_action _ (h g) _ _,}

namespace modular_form

noncomputable theory

/--The weight `k` action of `GL(2, ℝ)⁺` on functions `f : ℍ → ℂ`. -/
def slash (k : ℤ) (γ : GL(2, ℝ)⁺) (f : ℍ → ℂ) (x : ℍ) : ℂ :=
f (γ • x) * (((↑ₘ γ).det) : ℝ)^(k-1) * (upper_half_plane.denom γ x)^(-k)

variables {Γ : subgroup SL(2, ℤ)} {k: ℤ} (f : ℍ → ℂ)

localized "notation (name := modular_form.slash) f ` ∣[`:100 k `]`:0 γ :100 :=
  modular_form.slash k γ f" in modular_form

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

@[simp] lemma slash_add (k : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
  (f + g) ∣[k] A = (f ∣[k] A) + (g ∣[k] A) :=
begin
  ext1,
  simp only [slash, pi.add_apply, denom, coe_coe, zpow_neg],
  ring,
end

@[simp] lemma slash_one (k : ℤ) (f : ℍ → ℂ) : (f ∣[k] 1) = f :=
funext $ by simp [slash]

variables {α : Type*} [has_smul α ℂ] [is_scalar_tower α ℂ ℂ]

@[simp] lemma smul_slash (k : ℤ) (A : GL(2, ℝ)⁺) (f : ℍ → ℂ) (c : α) :
  (c • f) ∣[k] A = c • (f ∣[k] A) :=
begin
  simp_rw [←smul_one_smul ℂ c f, ←smul_one_smul ℂ c (f ∣[k] A)],
  ext1,
  simp_rw slash,
  simp only [slash, algebra.id.smul_eq_mul, matrix.general_linear_group.coe_det_apply,
    pi.smul_apply, subtype.val_eq_coe, coe_coe],
  ring,
end

@[simp] lemma neg_slash (k : ℤ) (A : GL(2, ℝ)⁺) (f : ℍ → ℂ) : (-f) ∣[k] A = - (f ∣[k] A) :=
funext $ by simp [slash]

@[simp] lemma zero_slash (k : ℤ) (A : GL(2, ℝ)⁺) : (0 : ℍ → ℂ) ∣[k] A = 0 :=
funext $ λ _, by simp only [slash, pi.zero_apply, zero_mul]

instance : slash_action ℤ GL(2, ℝ)⁺ (ℍ → ℂ) ℂ :=
{ map := slash,
  zero_slash := zero_slash,
  slash_one := slash_one,
  right_action := slash_right_action,
  smul_action := smul_slash,
  add_action := slash_add }

instance subgroup_action (Γ : subgroup SL(2, ℤ)) : slash_action ℤ Γ (ℍ → ℂ) ℂ :=
monoid_hom_slash_action (monoid_hom.comp (matrix.special_linear_group.to_GL_pos)
  (monoid_hom.comp (matrix.special_linear_group.map (int.cast_ring_hom ℝ)) (subgroup.subtype Γ)))

@[simp] lemma subgroup_slash (Γ : subgroup SL(2, ℤ)) (γ : Γ):
  (slash_action.map ℂ k γ f) = slash k (γ : GL(2,ℝ)⁺) f := rfl

instance SL_action : slash_action ℤ SL(2, ℤ) (ℍ → ℂ) ℂ :=
monoid_hom_slash_action (monoid_hom.comp (matrix.special_linear_group.to_GL_pos)
  (matrix.special_linear_group.map (int.cast_ring_hom ℝ)))

@[simp] lemma SL_slash (γ : SL(2, ℤ)):
  (slash_action.map ℂ k γ f) = slash k (γ : GL(2,ℝ)⁺) f := rfl

local notation f `∣[`:73 k:0, A `]` :72 := slash_action.map ℂ k A f

/-- The constant function 1 is invariant under any element of `SL(2, ℤ)`. -/
@[simp] lemma is_invariant_one (A : SL(2, ℤ)) : (1 : ℍ → ℂ) ∣[(0 : ℤ), A] = (1 : ℍ → ℂ) :=
begin
  have : (((↑ₘ(A : GL(2,ℝ)⁺)).det) : ℝ) = 1,
  { simp only [coe_coe,
      matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
      matrix.special_linear_group.det_coe], },
  funext,
  rw [SL_slash, slash, zero_sub, this],
  simp,
end

/-- A function `f : ℍ → ℂ` is `slash_invariant`, of weight `k ∈ ℤ` and level `Γ`,
  if for every matrix `γ ∈ Γ` we have `f(γ • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`,
  and it acts on `ℍ` via Möbius transformations. -/
lemma slash_action_eq'_iff (k : ℤ) (Γ : subgroup SL(2, ℤ)) (f : ℍ → ℂ) (γ : Γ)  (z : ℍ) :
  f ∣[k, γ] z = f z ↔ f (γ • z) = ((↑ₘ[ℤ]γ 1 0 : ℂ) * z + (↑ₘ[ℤ]γ 1 1 : ℂ))^k * f z :=
begin
  simp only [subgroup_slash, modular_form.slash],
  convert inv_mul_eq_iff_eq_mul₀ _ using 2,
  { rw mul_comm,
    simp only [denom, coe_coe, matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix, zpow_neg,
      matrix.special_linear_group.det_coe, of_real_one, one_zpow, mul_one, subgroup_to_sl_moeb,
      sl_moeb],
    refl, },
  { convert zpow_ne_zero k (denom_ne_zero γ z) },
end

lemma mul_slash (k1 k2 : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
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

@[simp] lemma mul_slash_SL2 (k1 k2 : ℤ) (A : SL(2, ℤ)) (f g : ℍ → ℂ) :
  (f * g) ∣[k1 + k2, A] = (f ∣[k1, A]) * (g ∣[k2, A]) :=
calc (f * g) ∣[k1 + k2, (A : GL(2, ℝ)⁺)] = _ • (f ∣[k1, A]) * (g ∣[k2, A]) : mul_slash _ _ _ _ _
... = (1:ℝ) • (f ∣[k1, A]) * (g ∣[k2, A]) : by simp [-matrix.special_linear_group.coe_matrix_coe]
... = (f ∣[k1, A]) * (g ∣[k2, A]) : by simp

lemma mul_slash_subgroup (k1 k2 : ℤ) (Γ : subgroup SL(2, ℤ)) (A : Γ) (f g : ℍ → ℂ) :
  (f * g) ∣[k1 + k2, A] = (f ∣[k1, A]) * (g ∣[k2, A]) :=
mul_slash_SL2 k1 k2 A f g

end modular_form

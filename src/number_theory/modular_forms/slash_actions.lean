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
class slash_action (β : Type*) (G : Type*) (α : Type*) (γ : Type*) [group G] [ring α]
  [has_smul γ α] :=
(map : β → G → α → α)
(mul_zero : ∀ (k : β) (g : G), map k g 0 = 0)
(one_mul : ∀ (k : β) (a : α) , map k 1 a = a)
(right_action : ∀ (k : β) (g h : G) (a : α), map k h (map k g a) = map k (g * h) a )
(smul_action : ∀ (k : β) (g : G) (a : α) (z : γ), map k g (z • a) = z • (map k g a))
(add_action : ∀ (k : β) (g : G) (a b : α), map k g (a + b) = map k g a + map k g b)

/--Slash_action induced by a monoid homomorphism.-/
def monoid_hom_slash_action { β : Type*} {G : Type*} {H : Type*} {α : Type*} {γ : Type*}
  [group G] [ring α] [has_smul γ α] [group H] [slash_action β G α γ] (h : H →* G) :
  slash_action β H α γ:=
{ map := (λ k g a, slash_action.map γ k (h(g)) a),
  mul_zero := by {intros k g, apply slash_action.mul_zero k (h g), },
  one_mul := by {intros k a, simp only [map_one], apply slash_action.one_mul,},
  right_action := by {simp only [map_mul], intros k g gg a, apply slash_action.right_action,},
  smul_action := by {intros k g a z, apply slash_action.smul_action, },
  add_action := by {intros k g a b, apply slash_action.add_action, }, }

namespace modular_forms

noncomputable theory

/--The weight `k` action of `GL(2, ℝ)⁺` on functions `f : ℍ → ℂ`. -/
def slash : ℤ → GL(2, ℝ)⁺ → (ℍ → ℂ) → (ℍ → ℂ) := λ k γ f,
  (λ (x : ℍ), f (γ • x) * (((↑ₘ γ).det) : ℝ)^(k-1) * (upper_half_plane.denom γ x)^(-k))

variables {Γ : subgroup SL(2,ℤ)} {k: ℤ} (f : (ℍ → ℂ))

localized "notation f ` ∣[`:100 k `]`:0 γ :100 := slash k γ f" in modular_forms

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
  simp only [slash, pi.add_apply, matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe,
    coe_coe],
  ext1,
  simp only [pi.add_apply],
  ring,
end

lemma slash_mul_one (k : ℤ) (f : ℍ → ℂ) : (f ∣[k] 1) = f :=
begin
 simp_rw slash,
 ext1,
 simp,
end

lemma smul_slash (k : ℤ) (A : GL(2, ℝ)⁺) (f : ℍ → ℂ) (c : ℂ) : (c • f) ∣[k] A = c • (f ∣[k] A) :=
begin
  ext1,
  simp_rw slash,
  simp only [slash, algebra.id.smul_eq_mul, matrix.general_linear_group.coe_det_apply,
    pi.smul_apply, subtype.val_eq_coe, coe_coe],
  ring,
end

instance : slash_action ℤ GL(2, ℝ)⁺ (ℍ → ℂ) ℂ :=
{ map := slash,
  mul_zero := by {intros k g, rw slash, simp only [pi.zero_apply, zero_mul], refl, },
  one_mul := by {apply slash_mul_one,},
  right_action := by {apply slash_right_action},
  smul_action := by {apply smul_slash},
  add_action := by {apply slash_add},}

instance subgroup_action (Γ : subgroup SL(2,ℤ)) : slash_action ℤ Γ (ℍ → ℂ) ℂ :=
monoid_hom_slash_action (monoid_hom.comp (matrix.special_linear_group.to_GL_pos)
  (monoid_hom.comp (matrix.special_linear_group.map (int.cast_ring_hom ℝ)) (subgroup.subtype Γ)))

instance SL_action : slash_action ℤ SL(2,ℤ) (ℍ → ℂ) ℂ :=
monoid_hom_slash_action (monoid_hom.comp (matrix.special_linear_group.to_GL_pos)
  (matrix.special_linear_group.map (int.cast_ring_hom ℝ)))

end modular_forms

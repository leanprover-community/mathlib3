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

@[derive group]
def slash_act {β : Type*} (G : Type*) [group G] (b : β) :=
mul_opposite G

def slash_act.of {β : Type*} {G : Type*} [group G] (b : β) (g : G) : slash_act G b :=
mul_opposite.op g

def slash_act.map {β : Type*} {G H : Type*} [group G] [group H] (b : β) (f : G →* H) :
  slash_act G b →* slash_act H b :=
f.op

/--A general version of the slash action of the space of modular forms.-/
@[reducible] def slash_action (β G α : Type*) [group G] [add_monoid α] :=
Π b : β, distrib_mul_action (slash_act G b) α

@[reducible] def slash_action.map {β G α : Type*} (b : β) [group G] [add_monoid α]
  [slash_action β G α] (a : α) (g : G) : α :=
slash_act.of b g • a

/--Slash_action induced by a monoid homomorphism.-/
def monoid_hom_slash_action {β G H α : Type*} [group G] [add_monoid α] [group H]
  [slash_action β G α] (h : H →* G) : slash_action β H α :=
λ b, distrib_mul_action.comp_hom _ $ slash_act.map _ h

namespace modular_form

noncomputable theory

/--The weight `k` action of `GL(2, ℝ)⁺` on functions `f : ℍ → ℂ`. -/
def slash (k : ℤ) (γ : GL(2, ℝ)⁺) (f : ℍ → ℂ) (x : ℍ) : ℂ :=
f (γ • x) * (((↑ₘ γ).det) : ℝ)^(k-1) * (upper_half_plane.denom γ x)^(-k)

variables {Γ : subgroup SL(2, ℤ)} {k: ℤ} (f : ℍ → ℂ)
section

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

instance : slash_action ℤ GL(2, ℝ)⁺ (ℍ → ℂ) :=
λ z,
  { smul := λ x, slash z x.unop,
    one_smul := slash_one z,
    mul_smul := λ a b f, (slash_right_action z _ _ _).symm,
    smul_zero := λ a, zero_slash z a.unop,
    smul_add := λ a b, slash_add z _ _ }

instance {z : ℤ} : smul_comm_class ℂ (slash_act GL(2, ℝ)⁺ z) (ℍ → ℂ) :=
⟨λ _ _ _, (smul_slash z _ _ _).symm⟩

end

local notation f ` ∣[`:73 k:0 `] ` A :72 := slash_action.map k f A

lemma slash_def (A : GL(2, ℝ)⁺) : f ∣[k] A = slash k A f := rfl

instance subgroup_action (Γ : subgroup SL(2, ℤ)) : slash_action ℤ Γ (ℍ → ℂ) :=
monoid_hom_slash_action (monoid_hom.comp (matrix.special_linear_group.to_GL_pos)
  (monoid_hom.comp (matrix.special_linear_group.map (int.cast_ring_hom ℝ)) (subgroup.subtype Γ)))

@[simp] lemma subgroup_slash (Γ : subgroup SL(2, ℤ)) (γ : Γ):
  (f ∣[k] γ) = f ∣[k] (γ : GL(2,ℝ)⁺) := rfl

instance SL_action : slash_action ℤ SL(2, ℤ) (ℍ → ℂ) :=
monoid_hom_slash_action (monoid_hom.comp (matrix.special_linear_group.to_GL_pos)
  (matrix.special_linear_group.map (int.cast_ring_hom ℝ)))

@[simp] lemma SL_slash (γ : SL(2, ℤ)) : (f ∣[k] γ) = f ∣[k] (γ : GL(2,ℝ)⁺) := rfl


/-- The constant function 1 is invariant under any element of `SL(2, ℤ)`. -/
@[simp] lemma is_invariant_one (A : SL(2, ℤ)) : (1 : ℍ → ℂ) ∣[(0 : ℤ)] A = (1 : ℍ → ℂ) :=
begin
  have : (((↑ₘ(A : GL(2,ℝ)⁺)).det) : ℝ) = 1,
  { simp only [coe_coe,
      matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
      matrix.special_linear_group.det_coe], },
  funext,
  rw [SL_slash, slash_def, slash, zero_sub, this],
  simp,
end

/-- A function `f : ℍ → ℂ` is `slash_invariant`, of weight `k ∈ ℤ` and level `Γ`,
  if for every matrix `γ ∈ Γ` we have `f(γ • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`,
  and it acts on `ℍ` via Möbius transformations. -/
lemma slash_action_eq'_iff (k : ℤ) (Γ : subgroup SL(2, ℤ)) (f : ℍ → ℂ) (γ : Γ)  (z : ℍ) :
  (f ∣[k] γ) z = f z ↔ f (γ • z) = ((↑ₘ[ℤ]γ 1 0 : ℂ) * z + (↑ₘ[ℤ]γ 1 1 : ℂ))^k * f z :=
begin
  simp only [subgroup_slash, slash_def, modular_form.slash],
  convert inv_mul_eq_iff_eq_mul₀ _ using 2,
  { rw mul_comm,
    simp only [denom, coe_coe, matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix, zpow_neg,
      matrix.special_linear_group.det_coe, of_real_one, one_zpow, mul_one, subgroup_to_sl_moeb,
      sl_moeb],
    refl, },
  { convert zpow_ne_zero k (denom_ne_zero γ z) },
end

lemma mul_slash (k1 k2 : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
  (f * g) ∣[k1 + k2] A = (((↑ₘ A).det) : ℝ) • (f ∣[k1] A) * (g ∣[k2] A) :=
begin
  ext1,
  simp only [slash_action.map, slash_def, slash, matrix.general_linear_group.coe_det_apply,
    subtype.val_eq_coe,
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
  (f * g) ∣[k1 + k2] A = (f ∣[k1, A]) * (g ∣[k2, A]) :=
calc (f * g) ∣[k1 + k2, (A : GL(2, ℝ)⁺)] = _ • (f ∣[k1, A]) * (g ∣[k2, A]) : mul_slash _ _ _ _ _
... = (1:ℝ) • (f ∣[k1, A]) * (g ∣[k2, A]) : by simp [-matrix.special_linear_group.coe_matrix_coe]
... = (f ∣[k1, A]) * (g ∣[k2, A]) : by simp

lemma mul_slash_subgroup (k1 k2 : ℤ) (Γ : subgroup SL(2, ℤ)) (A : Γ) (f g : ℍ → ℂ) :
  (f * g) ∣[k1 + k2, A] = (f ∣[k1, A]) * (g ∣[k2, A]) :=
mul_slash_SL2 k1 k2 A f g

end modular_form

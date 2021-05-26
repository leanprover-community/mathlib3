/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import geometry.manifold.derivation_bundle
import ring_theory.derivation

/-!

# Left invariant derivations

In this file we define the concept of left invariant derivation for a Lie group. The concept is the
analogous to the more classical concept of left invariant vector fields, and this analogy "commutes"
with the isomorphism between global derivations and left invariant vector fields.

Moreover we prove that `left_invariant_derivation I G` has the structure of a Lie algebra, hence
implementing one of the possible definitions of Lie algebra.

-/

noncomputable theory

open_locale lie_group manifold

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
(G : Type*) [topological_space G] [charted_space H G]
  [group G] [lie_group I G] (g h : G)

variable (G)

-- Generate trivial has_sizeof instance.
local attribute [instance, priority 10000]
private def disable_has_sizeof {α} : has_sizeof α := ⟨λ _, 0⟩

/--
Left-invariant global derivations.

A global derivation is left-invariant if it is equal to its pullback along left multiplication by
an arbitrary element of `G`.
-/
structure left_invariant_derivation extends derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯ :=
(left_invariant'' : ∀ f g, 𝒅(𝑳 I g) 1 (derivation.eval_at 1 to_derivation) f =
  derivation.eval_at g to_derivation f)

variables {I G}

namespace left_invariant_derivation

instance : has_coe (left_invariant_derivation I G) (derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯)
:= ⟨λ X, X.to_derivation⟩

instance : has_coe_to_fun (left_invariant_derivation I G) := ⟨_, λ X, X.to_derivation.to_fun⟩

variables
{M : Type*} [topological_space M] [charted_space H M] {x : M}
{X Y : left_invariant_derivation I G} {f f' : C^∞⟮I, G; 𝕜⟯} {r : 𝕜}

lemma to_fun_eq_coe : X.to_fun = ⇑X := rfl
lemma coe_fn_coe : ⇑(X : C^∞⟮I, G; 𝕜⟯ →ₗ[𝕜] C^∞⟮I, G; 𝕜⟯) = X := rfl
@[simp] lemma to_derivation_eq_coe : X.to_derivation = X := rfl

lemma coe_injective (h : ⇑X = Y) : X = Y :=
by { cases X, cases Y, congr', exact derivation.coe_injective h }

@[ext] theorem ext (h : ∀ f, X f = Y f) : X = Y :=
coe_injective $ funext h

variables (X Y f)

@[simp] lemma coe_lift_eq_coe :
  ⇑(X : derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = (X : C^∞⟮I, G; 𝕜⟯ → C^∞⟮I, G; 𝕜⟯) := rfl

lemma left_invariant' : (𝒅(𝑳 I g)) (1 : G) (derivation.eval_at (1 : G) ↑X) f =
  derivation.eval_at g ↑X f := by rw [←to_derivation_eq_coe]; exact left_invariant'' X f g

instance : has_zero (left_invariant_derivation I G) := ⟨⟨0, λ f g,
  by simp only [linear_map.map_zero, derivation.coe_zero]⟩⟩

instance : inhabited (left_invariant_derivation I G) := ⟨0⟩

instance : has_add (left_invariant_derivation I G) :=
{ add := λ X Y, ⟨X + Y, λ f g, by simp only [linear_map.map_add,
          derivation.coe_add, left_invariant', pi.add_apply]⟩ }

instance : has_neg (left_invariant_derivation I G) :=
{ neg := λ X, ⟨-X, λ f g, by simp only [linear_map.map_neg, derivation.coe_neg,
          left_invariant', pi.neg_apply]⟩ }

@[simp] lemma coe_add : ⇑(X + Y) = X + Y := rfl
@[simp] lemma coe_zero : ⇑(0 : left_invariant_derivation I G) = 0 := rfl
@[simp] lemma coe_neg : ⇑(-X) = -X := rfl
@[simp, norm_cast] lemma lift_add :
  (↑(X + Y) : derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = X + Y := rfl
@[simp, norm_cast] lemma lift_zero :
  (↑(0 : left_invariant_derivation I G) : derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = 0 := rfl
@[simp] lemma map_add : X (f + f') = X f + X f' := is_add_hom.map_add X f f'
@[simp] lemma map_zero : X 0 = 0 := is_add_monoid_hom.map_zero X
@[simp] lemma map_neg : X (-f) = -X f := linear_map.map_neg X f
@[simp] lemma map_sub : X (f - f') = X f - X f' := linear_map.map_sub X f f'

instance : add_comm_group (left_invariant_derivation I G) :=
{ add_assoc := λ X Y Z, by { ext1 f, simp only [coe_add], rw add_assoc ⇑X Y Z },
  zero_add := λ X, by { ext1 f, simp only [coe_add, coe_zero], rw zero_add ⇑X },
  add_zero := λ X,by { ext1 f, simp only [coe_add, coe_zero], rw add_zero ⇑X },
  add_comm := λ X Y, by { ext1 f, simp only [coe_add], rw add_comm ⇑X Y },
  add_left_neg := λ X, by { ext1 f, simp only [coe_add, coe_neg, coe_zero], rw add_left_neg ⇑X },
  ..left_invariant_derivation.has_zero,
  ..left_invariant_derivation.has_add,
  ..left_invariant_derivation.has_neg }

@[simp] lemma coe_sub : ⇑(X - Y) = X - Y := by simp only [sub_eq_add_neg, coe_add, coe_neg]

instance : module 𝕜 (left_invariant_derivation I G) :=
module.of_core $
{ smul := λ r X, ⟨r • X, λ f g, by { simp only [derivation.Rsmul_apply, algebra.id.smul_eq_mul,
            mul_eq_mul_left_iff, linear_map.map_smul, left_invariant'], left, refl }⟩,
  mul_smul := λ r s X, ext $ λ b, mul_smul _ _ _,
  one_smul := λ X, ext $ λ b, one_smul 𝕜 _,
  smul_add := λ r X Y, ext $ λ b, smul_add _ _ _,
  add_smul := λ r s X, ext $ λ b, add_smul _ _ _ }

@[simp] lemma map_smul : X (r • f) = r • X f := linear_map.map_smul X r f
@[simp] lemma smul_map : (r • X) f = r • (X f) := rfl
@[simp] lemma leibniz : X (f * f') = f • X f' + f' • X f := X.leibniz' _ _
@[simp] lemma lift_smul (k : 𝕜) : (↑(k • X) : derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = k • X := rfl

/-- Evaluation at a point for left invariant derivation. Same thing as for generic global
derivations.-/
def eval_at : (left_invariant_derivation I G) →ₗ[𝕜] (point_derivation I G g) :=
{ to_fun := λ X, derivation.eval_at g ↑X,
  map_add' := λ X Y, rfl,
  map_smul' := λ k X, rfl }

lemma eval_at_apply : eval_at g X f = (X f) g := rfl

@[simp] lemma eval_at_coe : derivation.eval_at g ↑X = eval_at g X := rfl

lemma left_invariant : (𝒅(𝑳 I g)) (1 : G) (eval_at (1 : G) X) f = eval_at g X f :=
(X.left_invariant'' f g)

lemma eval_at_mul : eval_at (g * h) X f = (𝒅(𝑳 I g)) h (eval_at h X) f :=
by rw [←left_invariant, L_mul, ←fdifferential_comp, apply_fdifferential, linear_map.comp_apply,
  apply_fdifferential, left_invariant]

lemma comp_L : (X f).comp (𝑳 I g) = X (f.comp (𝑳 I g)) :=
by ext h; rw [times_cont_mdiff_map.comp_apply, L_apply, ←eval_at_apply, eval_at_mul,
  apply_fdifferential, eval_at_apply]

instance : has_bracket (left_invariant_derivation I G) (left_invariant_derivation I G) :=
{ bracket := λ X Y, ⟨⁅(X : derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯), Y⁆, λ f g, begin
    have hX := left_invariant' g X (Y f), have hY := left_invariant' g Y (X f),
    rw [apply_fdifferential, derivation.eval_apply] at hX hY ⊢, rw [comp_L] at hX hY,
    rw [derivation.commutator_apply, smooth_map.coe_sub, pi.sub_apply, coe_lift_eq_coe],
    rw [coe_lift_eq_coe] at hX hY ⊢, rw [hX, hY], refl end⟩ }

@[simp] lemma commutator_coe_derivation :
  ⇑⁅X, Y⁆ = (⁅(X : derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯), Y⁆ :
  derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) := rfl

lemma commutator_apply : ⁅X, Y⁆ f = X (Y f) - Y (X f) := rfl

instance : lie_ring (left_invariant_derivation I G) :=
{ add_lie := λ X Y Z, by { ext1, simp only [commutator_apply, coe_add, pi.add_apply,
              linear_map.map_add, left_invariant_derivation.map_add], ring },
  lie_add := λ X Y Z, by { ext1, simp only [commutator_apply, coe_add, pi.add_apply,
              linear_map.map_add, left_invariant_derivation.map_add], ring },
  lie_self := λ X, by { ext1, simp only [commutator_apply, sub_self], refl },
  leibniz_lie := λ X Y Z, by { ext1, simp only [commutator_apply, coe_add, coe_sub, map_sub,
              pi.add_apply], ring, } }

instance : lie_algebra 𝕜 (left_invariant_derivation I G) :=
{ lie_smul := λ r Y Z, by { ext1, simp only [commutator_apply, map_smul, smul_sub, smul_map] } }

end left_invariant_derivation

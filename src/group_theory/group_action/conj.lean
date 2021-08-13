/-
Copyright (c) 2021 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.group_action.basic
/-!
# Conjugation action of a group on itself
This file defines the conjugation action of a group on itself. See also `mul_aut.conj` for
the definition of conjugation as a homomorphism into the automorphism group.

## Main definitions
A type alias `conj G` is introduced for a group `G`. The group `conj G` acts on `G` by conjugation.
-/

variables (G : Type*)

/-- A type alias for a group `G`. `conj G` acts on `G` by conjugation -/
def conj : Type* := G

namespace conj
open mul_action subgroup

variable {G}

instance : Π [group G], group (conj G) := id
instance : Π [fintype G], fintype (conj G) := id

@[simp] lemma card [fintype G] : fintype.card (conj G) = fintype.card G := rfl

@[simp] lemma «forall» (p : conj G → Prop) :
  (∀ (x : conj G), p x) ↔ ∀ x : G, p (to_conj x) := iff.rfl

variable [group G]

instance : inhabited (conj G) := ⟨1⟩

/-- Reinterpret `g : conj G` as an element of `G`. -/
def of_conj : conj G ≃* G := ⟨id, id, λ _, rfl, λ _, rfl, λ _ _, rfl⟩

/-- Reinterpret `g : G` as an element of `conj G`. -/
def to_conj : G ≃* conj G := of_conj.symm

@[simp] lemma of_mul_symm_eq : (@of_conj G _).symm = to_conj := rfl
@[simp] lemma to_mul_symm_eq : (@to_conj G _).symm = of_conj := rfl
@[simp] lemma to_conj_of_conj (x : conj G) : to_conj (of_conj x) = x := rfl
@[simp] lemma of_conj_to_conj (x : G) : of_conj (to_conj x) = x := rfl
@[simp] lemma of_conj_one : of_conj (1 : conj G) = 1 := rfl
@[simp] lemma to_conj_one : to_conj (1 : G) = 1 := rfl
@[simp] lemma of_conj_inv (x : conj G) : of_conj (x⁻¹) = (of_conj x)⁻¹ := rfl
@[simp] lemma to_conj_inv (x : G) : to_conj (x⁻¹) = (to_conj x)⁻¹ := rfl
@[simp] lemma of_conj_mul (x y : conj G) : of_conj (x * y) = of_conj x * of_conj y := rfl
@[simp] lemma to_conj_mul (x y : G) : to_conj (x * y) = to_conj x * to_conj y := rfl

instance : mul_action (conj G) G :=
{ smul := λ g h, of_conj g * h * (of_conj g)⁻¹,
  one_smul := by simp,
  mul_smul := by simp [mul_assoc] }

lemma smul_def (g : conj G) (h : G) : g • h = of_conj g * h * (of_conj g)⁻¹ := rfl

lemma smul_eq_conj (g : conj G) (h : G) : g • h = mul_aut.conj g h := rfl

/-- The set of fixed points of the conjugation action of `G` on itself is the center of `G`. -/
lemma fixed_points_eq_center : fixed_points (conj G) G = center G :=
begin
  ext x,
  simp [mem_center_iff, smul_def, mul_inv_eq_iff_eq_mul]
end

end conj

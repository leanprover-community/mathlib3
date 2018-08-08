/-
Copyright (c) 2018 Kevin Buzzard and Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot.

This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.
-/


import group_theory.coset

universes u v 

variables {G : Type u} [group G] (N : set G) [normal_subgroup N] {H : Type v} [group H]

local attribute [instance] left_rel normal_subgroup.to_is_subgroup

definition quotient_group := left_cosets N 

local notation ` Q ` := quotient_group N

instance : group Q := left_cosets.group N 

namespace group.quotient

instance inhabited : inhabited Q := ⟨1⟩

def mk : G → Q := λ g, ⟦g⟧

instance is_group_hom_quotient_mk : is_group_hom (mk N) := by refine {..}; intros; refl 

def lift (φ : G → H) [Hφ : is_group_hom φ] (HN : ∀x∈N, φ x = 1) (q : Q) : H :=
q.lift_on φ $ assume a b (hab : a⁻¹ * b ∈ N),
(calc φ a = φ a * 1           : by simp
...       = φ a * φ (a⁻¹ * b) : by rw HN (a⁻¹ * b) hab
...       = φ (a * (a⁻¹ * b)) : by rw is_group_hom.mul φ a (a⁻¹ * b)
...       = φ b               : by simp)

@[simp] lemma lift_mk {φ : G → H} [Hφ : is_group_hom φ] (HN : ∀x∈N, φ x = 1) (g : G) :
  lift N φ HN ⟦g⟧ = φ g := rfl

@[simp] lemma lift_mk' {φ : G → H} [Hφ : is_group_hom φ] (HN : ∀x∈N, φ x = 1) (g : G) :
  lift N φ HN (mk N g) = φ g := rfl

variables (φ : G → H) [Hφ : is_group_hom φ] (HN : ∀x∈N, φ x = 1)
include Hφ
instance is_group_hom_quotient_lift  :
  is_group_hom (lift N φ HN) := 
⟨λ q r, quotient.induction_on₂ q r $ λ a b, show φ (a * b) = φ a * φ b, from is_group_hom.mul φ a b⟩

open function is_group_hom

lemma injective_ker_lift : injective (lift (ker φ) φ $ λ x h, (mem_ker φ).1 h) :=
assume a b, quotient.induction_on₂ a b $ assume a b (h : φ a = φ b), quotient.sound $ 
show a⁻¹ * b ∈ ker φ, by rw [mem_ker φ, Hφ.mul,←h,is_group_hom.inv φ,inv_mul_self]

end group.quotient

namespace group
variables {cG : Type u} [comm_group cG] (cN : set cG) [normal_subgroup cN] 

instance : comm_group (quotient_group cN) := 
{ mul_comm := λ a b,quotient.induction_on₂ a b $ λ g h, 
    show ⟦g * h⟧ = ⟦h * g⟧, 
    by rw [mul_comm g h],
  ..left_cosets.group cN
}
end group
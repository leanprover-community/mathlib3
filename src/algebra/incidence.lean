/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.ring
import data.finset.locally_finite

/-!
# Incidence algebras
-/

open finset
open_locale big_operators

variables (𝕜 α : Type*)

/-- The `𝕜`-incidence algebra over `α`. -/
def incidence_algebra := α → α → 𝕜

instance [inhabited 𝕜] : inhabited (incidence_algebra 𝕜 α) := ⟨λ _ _, default 𝕜⟩

namespace incidence_algebra
section one
variables [decidable_eq α] [has_zero 𝕜] [has_one 𝕜]

instance : has_one (incidence_algebra 𝕜 α) := ⟨λ a b, if a = b then 1 else 0⟩

@[simp] lemma one_apply (a b : α) : (1 : incidence_algebra 𝕜 α) a b = if a = b then 1 else 0 := rfl

end one

section mul
variables [preorder α] [locally_finite_order α] [add_comm_monoid 𝕜] [has_mul 𝕜]

instance : has_mul (incidence_algebra 𝕜 α) := ⟨λ f g a b, ∑ x in Icc a b, f a x * g x b⟩

@[simp] lemma mul_apply (f g : incidence_algebra 𝕜 α) (a b : α) :
  (f * g) a b = ∑ x in Icc a b, f a x * g x b := rfl

end mul

instance [decidable_eq α] [preorder α] [locally_finite_order α] [non_assoc_semiring 𝕜] :
  monoid (incidence_algebra 𝕜 α) :=
{ mul := (*),
  mul_assoc := λ f g h, begin
    ext a b,
    simp only [mul_apply, sum_mul, mul_sum],
    sorry
  end,
  one := (1),
  one_mul := λ f, begin
    ext a b,
    simp_rw [mul_apply, one_apply, sum_boole_mul],
    refine if_pos (left_mem_Icc.2 _),
    sorry
  end,
  mul_one := λ f, begin
    ext a b,
    simp_rw [mul_apply, one_apply, eq_comm, sum_mul_boole],
    convert (if_pos $ right_mem_Icc.2 _).symm,
    sorry
  end }

section zeta
variables [has_le α] [@decidable_rel α (≤)] [has_zero 𝕜] [has_one 𝕜]

def zeta : incidence_algebra 𝕜 α := λ a b, if a ≤ b then 1 else 0

variables {𝕜 α}

@[simp] lemma zeta_apply (a b : α) : zeta 𝕜 α a b = if a ≤ b then 1 else 0 := rfl

lemma zeta_of_le {a b : α} (h : a ≤ b) : zeta 𝕜 α a b = 1 := if_pos h

end zeta

lemma zeta_mul_zeta [preorder α] [locally_finite_order α] [@decidable_rel α (≤)] [add_comm_monoid 𝕜]
  [mul_one_class 𝕜] (a b : α) :
  (zeta 𝕜 α * zeta 𝕜 α) a b = (Icc a b).card :=
begin
  rw [mul_apply, card_eq_sum_ones, nat.cast_sum, nat.cast_one],
  refine sum_congr rfl (λ x hx, _),
  rw mem_Icc at hx,
  rw [zeta_of_le hx.1, zeta_of_le hx.2, one_mul],
end

section mu
variables [preorder α] [locally_finite_order α] [decidable_eq α] [add_comm_monoid 𝕜] [has_one 𝕜]

def mu_aux (a : α) : α → 𝕜
| b := if a = b then 1 else begin
  exact ∑ x in (Ico a b).attach, have (Icc a x).card < (Icc a b).card := begin
    refine card_lt_card _,
    sorry
  end, mu_aux x,
end
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ b, (Icc a b).card)⟩] }

def mu : incidence_algebra 𝕜 α := mu_aux 𝕜 α

variables {𝕜 α}

lemma mu_apply (a b : α) : mu 𝕜 α a b = if a = b then 1 else ∑ x in Ico a b, mu 𝕜 α a x :=
begin
  sorry
end

end mu

section mu_zeta
variables [preorder α] [locally_finite_order α] [decidable_eq α] [@decidable_rel α (≤)]
  [add_comm_monoid 𝕜] [mul_one_class 𝕜]

lemma mu_mul_zeta : mu 𝕜 α * zeta 𝕜 α = 1 :=
begin
  ext a b,
  rw [mul_apply, one_apply],
  sorry
end

lemma zeta_mul_mu : zeta 𝕜 α * mu 𝕜 α = 1 :=
begin
  ext a b,
  rw [mul_apply, one_apply],
  sorry
end

end mu_zeta
end incidence_algebra

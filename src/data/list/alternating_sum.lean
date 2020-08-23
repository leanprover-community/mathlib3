/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Chris Wong
-/
import algebra.group_power

namespace list

/-- The alternating sum of a list. -/
def alternating_sum {G : Type*} [has_zero G] [has_add G] [has_neg G] : list G → G
| [] := 0
| (g :: []) := g
| (g :: h :: t) := g + -h + alternating_sum t

/-- The alternating product of a list. -/
@[to_additive] def alternating_prod {G : Type*} [has_one G] [has_mul G] [has_inv G] : list G → G
| [] := 1
| (g :: []) := g
| (g :: h :: t) := g * h⁻¹ * alternating_prod t

variables {G : Type*} [comm_group G]

@[simp, to_additive] lemma alternating_prod_nil :
  alternating_prod ([] : list G) = 1 := rfl

@[to_additive] lemma alternating_prod_singleton (g : G) :
  alternating_prod [g] = g := rfl

@[to_additive alternating_sum_cons_cons']
lemma alternating_prod_cons_cons (g h : G) (l : list G) :
  alternating_prod (g :: h :: l) = g * h⁻¹ * alternating_prod l := rfl

lemma alternating_sum_cons_cons {G : Type*} [add_comm_group G] (g h : G) (l : list G) :
  alternating_sum (g :: h :: l) = g - h + alternating_sum l := rfl

@[to_additive alternating_sum_cons']
lemma alternating_prod_cons :
  ∀ (g : G) (l : list G), alternating_prod (g :: l) = g * (alternating_prod l)⁻¹
| g [] := by { rw [alternating_prod_nil, one_inv, mul_one], refl }
| g (h :: l) :=
by rw [alternating_prod_cons_cons, alternating_prod_cons h l, mul_inv, inv_inv, mul_assoc]

-- Add the `@[simp]` separately so that it isn't picked up by `@[to_additive]`
attribute [simp] alternating_prod_cons

@[simp]
lemma alternating_sum_cons {G : Type*} [add_comm_group G] :
  ∀ (g : G) (l : list G), alternating_sum (g :: l) = g - alternating_sum l := alternating_sum_cons'

lemma alternating_prod_append :
  ∀ (l₁ l₂ : list G), alternating_prod (l₁ ++ l₂)
    = alternating_prod l₁ * alternating_prod l₂ ^ (-1 : ℤ) ^ length l₁
| [] l₂ := by simp
| (g :: l₁) l₂ :=
begin
  have := alternating_prod_append l₁ l₂,
  simp [-mul_inv_rev, mul_inv, mul_assoc, pow_succ, this]
end

lemma alternating_sum_append {G : Type*} [add_comm_group G] :
  ∀ (l₁ l₂ : list G), alternating_sum (l₁ ++ l₂)
    = alternating_sum l₁ + (-1) ^ length l₁ •ℤ alternating_sum l₂
| [] l₂ := by simp
| (g :: l₁) l₂ :=
begin
  have := alternating_sum_append l₁ l₂,
  simp [pow_succ, sub_add, this]
end

lemma alternating_prod_reverse :
  ∀ (l : list G), alternating_prod (reverse l) = alternating_prod l ^ (-1 : ℤ) ^ (length l + 1)
| [] := by simp
| (g :: l) :=
begin
  have := alternating_prod_reverse l,
  simp [alternating_prod_append, inv_gpow, mul_gpow, pow_succ, this], ac_refl
end

lemma alternating_sum_reverse {G : Type*} [add_comm_group G] :
  ∀ (l : list G), alternating_sum (reverse l) = (-1) ^ (length l + 1) •ℤ alternating_sum l
| [] := by simp
| (g :: l) :=
begin
  have := alternating_sum_reverse l,
  simp [alternating_sum_append, gsmul_sub, neg_add_eq_sub, pow_succ, this]
end

end list

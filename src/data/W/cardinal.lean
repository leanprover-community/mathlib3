/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import set_theory.cardinal_ordinal
import data.W.basic
/-!
# Cardinality of W-types

This file proves some theorems about the cardinality of W-types. The main result is
`cardinal_mk_le_max_omega_of_fintype` which says that if for any `a : α`,
`β a` is finite, then the cardinality of `W_type β` is at most the maximum of the
cardinality of `α` and `cardinal.omega`.
This can be used to prove theorems about the cardinality of algebraic constructions such as
polynomials. There is a surjection from a `W_type` to `mv_polynomial` for example, and
this surjection can be used to put an upper bound on the cardinality of `mv_polynomial`.

## Tags

W, W type, cardinal, first order
-/
universe u

variables {α : Type u} {β : α → Type u}

noncomputable theory

namespace W_type

open_locale cardinal

open cardinal

lemma cardinal_mk_eq_sum : #(W_type β) = sum (λ a : α, #(W_type β) ^ #(β a)) :=
begin
  simp only [cardinal.power_def, ← cardinal.mk_sigma],
  exact mk_congr (equiv_sigma β)
end

/-- `#(W_type β)` is the least cardinal `κ` such that `sum (λ a : α, κ ^ #(β a)) ≤ κ` -/
lemma cardinal_mk_le_of_le {κ : cardinal.{u}} (hκ : sum (λ a : α, κ ^ #(β a)) ≤ κ) :
  #(W_type β) ≤ κ :=
begin
  induction κ using cardinal.induction_on with γ,
  simp only [cardinal.power_def, ← cardinal.mk_sigma, cardinal.le_def] at hκ,
  cases hκ,
  exact cardinal.mk_le_of_injective (elim_injective _ hκ.1 hκ.2)
end

/-- If, for any `a : α`, `β a` is finite, then the cardinality of `W_type β`
  is at most the maximum of the cardinality of `α` and `ω`  -/
lemma cardinal_mk_le_max_omega_of_fintype [Π a, fintype (β a)] : #(W_type β) ≤ max (#α) ω :=
(is_empty_or_nonempty α).elim
  (begin
    introI h,
    rw [cardinal.mk_eq_zero (W_type β)],
    exact zero_le _
  end) $
λ hn,
let m := max (#α) ω in
cardinal_mk_le_of_le $
calc cardinal.sum (λ a : α, m ^ #(β a))
    ≤ #α * cardinal.sup.{u u}
      (λ a : α, m ^ cardinal.mk (β a)) :
  cardinal.sum_le_sup _
... ≤ m * cardinal.sup.{u u}
      (λ a : α, m ^ #(β a)) :
  mul_le_mul' (le_max_left _ _) (le_refl _)
... = m : mul_eq_left.{u} (le_max_right _ _)
  (cardinal.sup_le.2 (λ i, begin
    cases lt_omega.1 (lt_omega_iff_fintype.2 ⟨show fintype (β i), by apply_instance⟩) with n hn,
    rw [hn],
    exact power_nat_le (le_max_right _ _)
  end))
  (pos_iff_ne_zero.1 (succ_le.1
    begin
      rw [succ_zero],
      obtain ⟨a⟩ : nonempty α, from hn,
      refine le_trans _ (le_sup _ a),
      rw [← @power_zero m],
      exact power_le_power_left (pos_iff_ne_zero.1
        (lt_of_lt_of_le omega_pos (le_max_right _ _))) (zero_le _)
    end))

end W_type

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
`cardinal_mk_le_of_fintype` which says that if `α` is infinite, and for any `a : α`,
`β a` is finite, then the cardinality of `W_type β` is at most the cardinality of `α`.
This has applications in first order logic, and can be used to prove that in the
cardinality of the set of terms in a language with infinitely many function or constant symbols
is bound by the cardinality of the set of function and constant symbols.

## Tags

W, W type, cardinal, first order
-/
universe u

variables {α : Type u} {β : α → Type u}

noncomputable theory

open cardinal

namespace W_type

lemma cardinal_mk_eq_sum : cardinal.mk (W_type β) =
  cardinal.sum (λ a : α, cardinal.mk (W_type β) ^ cardinal.mk (β a)) :=
begin
  simp only [cardinal.lift_mk, cardinal.power_def, cardinal.sum_mk],
  exact cardinal.eq.2 ⟨equiv_sigma β⟩
end

lemma cardinal_mk_le_of_le {κ : cardinal.{u}}
  (hκ : cardinal.sum (λ a : α, κ ^ cardinal.mk (β a)) ≤ κ) :
  cardinal.mk (W_type β) ≤ κ :=
begin
  conv_rhs { rw ← cardinal.mk_out κ},
  rw [← cardinal.mk_out κ] at hκ,
  simp only [cardinal.power_def, cardinal.sum_mk, cardinal.le_def] at hκ,
  cases hκ,
  exact cardinal.mk_le_of_injective (to_type_injective _ hκ.1 hκ.2)
end

/-- If `α` is infinite, and for any `a : α`, `β a` is finite, then the cardinality of `W_type β`
  is at most the cardinality of `α`. -/
lemma cardinal_mk_le_of_fintype [Π a, fintype (β a)]
  (hα : omega ≤ cardinal.mk α) : cardinal.mk (W_type β) ≤ cardinal.mk α :=
cardinal_mk_le_of_le $
calc cardinal.sum (λ a : α, cardinal.mk α ^ cardinal.mk.{u} (β a))
    ≤ (cardinal.mk α) * cardinal.sup.{u u}
      (λ a : α, cardinal.mk α ^ cardinal.mk.{u} (β a)) :
  cardinal.sum_le_sup _
... = cardinal.mk α : mul_eq_left.{u} hα
  (cardinal.sup_le.2 (λ i, begin
    cases lt_omega.1 (lt_omega_iff_fintype.2 ⟨show fintype (β i), by apply_instance⟩) with n hn,
    rw [hn],
    exact power_nat_le hα
  end))
  (pos_iff_ne_zero.1 (succ_le.1
    begin
      rw [succ_zero],
      obtain ⟨a⟩ : nonempty α,
        from ne_zero_iff_nonempty.1 (pos_iff_ne_zero.1 (lt_of_lt_of_le omega_pos hα)),
      refine le_trans _ (le_sup _ a),
      rw [← @power_zero (cardinal.mk α)],
      exact power_le_power_left (pos_iff_ne_zero.1 (lt_of_lt_of_le omega_pos hα)) (zero_le _)
    end))

end W_type

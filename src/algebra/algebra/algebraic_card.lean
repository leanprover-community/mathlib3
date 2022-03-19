/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import data.real.basic
import data.polynomial.cardinal
import data.rat.denumerable
import ring_theory.algebraic
import set_theory.cardinal_ordinal

open cardinal polynomial
open_locale cardinal

theorem nat_is_algebraic (n : ℕ) : is_algebraic ℚ (n : ℝ) :=
sorry

theorem algebraic_card : #{x : ℝ | is_algebraic ℚ x} = ω :=
begin
  apply le_antisymm,
  {
    classical,
    let f : polynomial ℚ × ℚ × ℚ → {x : ℝ | is_algebraic ℚ x} := λ ⟨p, a, b⟩,
      if hr : p ≠ 0 ∧ ∃ r : ℝ, r ∈ set.Ioo (a : ℝ) b ∧ aeval r p = 0
      then ⟨classical.some hr.2, p, hr.1, (classical.some_spec hr.2).2⟩
      else ⟨0, begin
        apply algebraic_zero
      end⟩,
    suffices : function.surjective f,
    {
      apply (mk_le_of_surjective this).trans,
      simp [mk_rat],
      rw ←max_eq_right (@mk_le_omega ℚ _),
      exact cardinal_mk_le_max
    },

  },
  {
    let g : ulift ℕ → {x : ℝ | is_algebraic ℚ x} := λ n, ⟨_, nat_is_algebraic n.down⟩,
    have hg : function.injective g := λ m n hmn, begin
      have := nat.cast_inj.1 (subtype.mk.inj hmn),
      apply_fun @ulift.up ℕ at this,
      rwa [ulift.up_down, ulift.up_down] at this
    end,
    exact mk_le_of_injective hg
  }
end

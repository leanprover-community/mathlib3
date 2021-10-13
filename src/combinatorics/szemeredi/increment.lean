/-
Copyright (c) 2021 Yaël DIllies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël DIllies, Bhavik Mehta
-/
import .chunk
import .index

/-!
# Increment
-/

open finset fintype simple_graph
open_locale classical

variables {α : Type*} [fintype α] {P : finpartition α} (hP : P.is_equipartition)
  (G : simple_graph α) (ε : ℝ)

local notation `m` := (card α/exp_bound P.size : ℕ)
local notation `a` := (card α/P.size - m * 4^P.size : ℕ)

/-- The work-horse of SRL. This says that if we have an equipartition which is *not* uniform, then
we can make a (much bigger) equipartition with a slightly higher index. This is helpful since the
index is bounded by a constant (see `index_le_half`), so this process eventually terminates and
yields a not-too-big uniform equipartition. -/
noncomputable def finpartition_on.is_equipartition.increment : finpartition α :=
P.bind (λ U, hP.chunk_increment G ε)

open finpartition_on finpartition_on.is_equipartition

variables {G ε}

namespace increment

protected lemma size (hPα : P.size * 16^P.size ≤ card α) (hPG : ¬P.is_uniform G ε) :
  (hP.increment G ε).size = exp_bound P.size :=
begin
  have hPα' : exp_bound P.size ≤ card α :=
    (nat.mul_le_mul_of_nonneg_left $ nat.pow_le_pow_of_le_left (by norm_num) _).trans hPα,
  have hPpos : 0 < exp_bound P.size := exp_bound_pos.2 ((nat.eq_zero_or_pos _).resolve_left $ λ h,
    hPG $ finpartition_on.empty_is_uniform (by rw [←finset.card_eq_zero, ←finpartition_on.size, h])
    _ _),
  rw [is_equipartition, finset.equitable_on_iff] at hP,
  rw [increment, bind_size],
  simp_rw [finpartition_on.is_equipartition.chunk_increment, apply_dite finpartition_on.size],
  rw [sum_dite, sum_const_nat, sum_const_nat, card_attach, card_attach], rotate,
  exact λ x hx, finpartition_on.equitabilise.size (nat.div_pos hPα' hPpos) _,
  exact λ x hx, finpartition_on.equitabilise.size (nat.div_pos hPα' hPpos) _,
  rw [nat.sub_add_cancel a_add_one_le_four_pow_size, nat.sub_add_cancel ((nat.le_succ _).trans
    a_add_one_le_four_pow_size), ←add_mul],
  congr,
  rw [filter_card_add_filter_neg_card_eq_card, card_attach, finpartition_on.size],
end

protected lemma is_equipartition (hP : P.is_equipartition) (G : simple_graph α) (ε : ℝ) :
  (hP.increment G ε).is_equipartition :=
begin
  rw [is_equipartition, set.equitable_on_iff_exists_eq_eq_add_one],
  refine ⟨m, λ A hA, _⟩,
  rw [mem_coe, increment, mem_bind_parts] at hA,
  obtain ⟨U, hU, hA⟩ := hA,
  exact card_eq_of_mem_parts_chunk_increment hA,
end

protected lemma index [nonempty α] (hP : P.is_equipartition) (hP₁₀₀ : 100 ≤ P.size)
  (hε : 100 < ε^5 * 4^P.size) (hPα : P.size * 16^P.size ≤ card α) (hPG : ¬P.is_uniform G ε) :
  P.index G + ε^5 / 8 ≤ (hP.increment G ε).index G :=
begin
  calc
    index G P + ε^5/8
        ≤ index G P - ε^5/25 + 1/P.size^2 * ε * (P.size.choose 2) * ε^4/3
        : begin
          have hP₀ : (0 : ℝ) < P.size := nat.cast_pos.2 ((nat.zero_lt_succ _).trans_le hP₁₀₀),
          rw [sub_eq_add_neg, add_assoc, ←neg_div, nat.cast_choose_two],
          refine add_le_add_left _ _,
          calc
            - ε^5/25 + 1/P.size^2 * ε * (P.size * (P.size - 1)/2) * ε^4/3
                = ε^5 * ((P.size * (P.size - 1))/P.size^2/6 - 1/25)
                : by ring
            ... = ε^5 * ((1 - 1/P.size)/6 - 1/25)
                : by rw [sq, mul_div_mul_left _ _ hP₀.ne', sub_div, div_self hP₀.ne']
            ... ≥ ε^5/8
                : begin
                  rw @div_eq_mul_inv ℝ _ _ 8,
                  refine mul_le_mul_of_nonneg_left _ _,
                  rw [le_sub_iff_add_le, le_div_iff (by norm_num : (0 : ℝ) < 6),
                    le_sub_iff_add_le, ←le_sub_iff_add_le', div_le_iff hP₀, ←div_le_iff'],
                  norm_num,
                  exact_mod_cast hP₁₀₀,
                  norm_num,
                  exact nonneg_of_mul_nonneg_right ((by norm_num : (0 : ℝ) ≤ 100).trans hε.le)
                    (pow_pos zero_lt_four _),
                end
        end
    ... ≤ index G (hP.increment G ε) :
    begin
      conv_rhs { rw index },
      rw finpartition_on.is_uniform at hPG,
      sorry
    end
end.

end increment

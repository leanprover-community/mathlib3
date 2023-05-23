/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import algebra.star.order
import data.rat.lemmas
import group_theory.submonoid.membership

/-! # Star order structure on ℚ

Here we put the trivial `star` operation on `ℚ` for convenience and show that it is a
`star_ordered_ring`. In particular, this means that every element of `ℚ` is a sum of squares.
-/

namespace rat

instance : star_ring ℚ :=
{ star := id,
  star_involutive := λ _, rfl,
  star_mul := λ _ _, mul_comm _ _,
  star_add := λ _ _, rfl }

instance : has_trivial_star ℚ :=
{ star_trivial := λ _, rfl }

instance : star_ordered_ring ℚ :=
{ star := star,
  add_le_add_left := λ _ _, add_le_add_left,
  nonneg_iff := λ x,
  begin
    refine ⟨λ hx, _, λ hx, add_submonoid.closure_induction hx
      (by { rintro - ⟨s, rfl⟩, exact mul_self_nonneg s }) le_rfl (λ _ _, add_nonneg)⟩,
    suffices : (finset.range (x.num.nat_abs * x.denom)).sum
      (function.const ℕ (rat.mk_pnat 1 ⟨x.denom, x.pos⟩ * rat.mk_pnat 1 ⟨x.denom, x.pos⟩)) = x,
    { exact this ▸ sum_mem (λ n hn, add_submonoid.subset_closure ⟨_, rfl⟩) },
    simp only [function.const_apply, finset.sum_const, finset.card_range, nsmul_eq_mul, mk_pnat_eq],
    rw [←int.cast_coe_nat, int.coe_nat_mul, int.coe_nat_abs,
      abs_of_nonneg (num_nonneg_iff_zero_le.mpr hx), int.cast_mul, int.cast_coe_nat],
    simp only [int.cast_mul, int.cast_coe_nat, coe_int_eq_mk, coe_nat_eq_mk],
    rw [mul_assoc, ←mul_assoc (mk (x.denom : ℤ) 1), mk_mul_mk_cancel one_ne_zero,
      ←one_mul (x.denom : ℤ), div_mk_div_cancel_left (by simpa using x.pos.ne' : (x.denom : ℤ) ≠ 0),
      one_mul, mk_one_one, one_mul, mk_mul_mk_cancel one_ne_zero, rat.num_denom],
  end,
  .. rat.star_ring }

end rat

/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.direct_sum.algebra
import data.fin.vec_notation

/-! # Tuples `fin na → α` form a graded ring under append -/

namespace fin

variables {α : Type*} {α' : Type*} {na nb nc : ℕ}

instance pi_graded_monoid {α : Type*} : graded_monoid.gmonoid (λ n, fin n → α) :=
{ mul := λ i j, fin.append,
  one := fin.elim0,
  one_mul := λ b, sigma_eq_of_eq_comp_cast _ (elim0'_append _),
  mul_one := λ a, sigma_eq_of_eq_comp_cast _ (append_elim0' _),
  mul_assoc := λ a b c,
    sigma_eq_of_eq_comp_cast (add_assoc _ _ _) $ (append_assoc a.2 b.2 c.2).trans rfl,
  gnpow := λ n i a, repeat n a,
  gnpow_zero' := λ a, sigma_eq_of_eq_comp_cast _ (repeat_zero _),
  gnpow_succ' := λ a n, sigma_eq_of_eq_comp_cast _ (repeat_succ _ _) }

end fin

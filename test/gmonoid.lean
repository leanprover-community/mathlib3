/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.direct_sum.ring
import data.fin.tuple.basic

/-! # Tuples `fin n → α` form a graded monoid with `*` as `fin.append`

Defining multiplication as concatenation isn't particularly canonical, so we do not provide
this in mathlib. We could safely provide this instance on a type alias, but for now we just put
this in `tests` to verify that this definition is possible. -/

namespace fin

variables {α : Type*} {α' : Type*} {na nb nc : ℕ}

example {α : Type*} : graded_monoid.gmonoid (λ n, fin n → α) :=
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

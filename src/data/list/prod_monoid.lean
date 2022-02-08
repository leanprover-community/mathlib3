/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import data.list.big_operators

/-!
# Products / sums of lists of terms of a monoid

This file provides basic results about `list.prod` (definition in `data.list.defs`) in a monoid.
-/

open nat

namespace list

universes u v
variables {α : Type u}

@[simp, priority 500, to_additive]
theorem prod_repeat [monoid α] (a : α) (n : ℕ) : (repeat a n).prod = a ^ n :=
begin
  induction n with n ih,
  { rw pow_zero, refl },
  { rw [list.repeat_succ, list.prod_cons, ih, pow_succ] }
end

@[to_additive]
lemma prod_le_of_forall_le [ordered_comm_monoid α] (l : list α) (n : α) (h : ∀ (x ∈ l), x ≤ n) :
  l.prod ≤ n ^ l.length :=
begin
  induction l with y l IH,
  { simp },
  { specialize IH (λ x hx, h x (mem_cons_of_mem _ hx)),
    have hy : y ≤ n := h y (mem_cons_self _ _),
    simpa [pow_succ] using mul_le_mul' hy IH }
end

end list

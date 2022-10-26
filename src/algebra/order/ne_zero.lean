/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import algebra.ne_zero
import algebra.order.ring

/-!
# `ne_zero` instances for ordered structures
-/

namespace ne_zero

variables {R S M F : Type*} {r : R} {x y : M} {n p : ℕ} {a : ℕ+}

lemma pos (r : R) [canonically_ordered_add_monoid R] [ne_zero r] : 0 < r :=
(zero_le r).lt_of_ne $ ne_zero.out.symm

lemma of_gt  [canonically_ordered_add_monoid M] (h : x < y) : ne_zero y := of_pos $ pos_of_gt h

-- 1 < p is still an often-used `fact`, due to `nat.prime` implying it, and it implying `nontrivial`
-- on `zmod`'s ring structure. We cannot just set this to be any `x < y`, else that becomes a
-- metavariable and it will hugely slow down typeclass inference.
@[priority 10]
instance of_gt' [canonically_ordered_add_monoid M] [has_one M] [fact (1 < y)] : ne_zero y :=
of_gt $ fact.out $ 1 < y

instance bit0 [canonically_ordered_add_monoid M] [ne_zero x] : ne_zero (bit0 x) :=
of_pos $ bit0_pos $ ne_zero.pos x

instance bit1 [canonically_ordered_comm_semiring M] [nontrivial M] : ne_zero (bit1 x) :=
⟨mt (λ h, le_iff_exists_add'.2 ⟨_, h.symm⟩) zero_lt_one.not_le⟩

end ne_zero

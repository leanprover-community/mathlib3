/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import algebra.algebra.basic
import algebra.module.ordered

/-!
# Ordered algebras

An ordered algebra is an ordered semiring, which is an algebra over an ordered commutative semiring,
for which scalar multiplication is "compatible" with the two orders.

The prototypical example is 2x2 matrices over the reals or complexes (or indeed any C^* algebra)
where the ordering the one determined by the positive cone of positive operators,
i.e. `A ≤ B` iff `B - A = star R * R` for some `R`.

## Tags

ordered algebra
-/


/--
An ordered algebra over an ordered commutative semiring is an algebra
for which the scalar multiplication is compatible with the orders.
-/
@[protect_proj, ancestor semimodule]
class ordered_algebra (R A : Type*)
  [ordered_comm_semiring R] [ordered_semiring A] extends algebra R A :=
(smul_lt_smul_of_pos : ∀ {a b : A}, ∀ {r : R}, a < b → 0 < r → r • a < r • b)
(lt_of_smul_lt_smul_of_nonneg : ∀ {a b : A}, ∀ {r : R}, r • a < r • b → 0 ≤ r → a < b)

namespace ordered_algebra

variables {R A : Type*} {a b : A} {r : R}

section
variables [ordered_comm_semiring R] [ordered_semiring A] [ordered_algebra R A]

/--
The underlying ordered module of an ordered algebra.
-/
@[priority 100]
instance to_ordered_semimodule : ordered_semimodule R A :=
{ ..‹ordered_algebra R A› }

end

section
variables [ordered_comm_ring R] [ordered_ring A] [ordered_algebra R A]

lemma algebra_map_monotone : monotone (algebra_map R A) :=
λ a b h,
begin
  rw [algebra.algebra_map_eq_smul_one, algebra.algebra_map_eq_smul_one, ←sub_nonneg, ←sub_smul],
  transitivity (b - a) • (0 : A),
  { simp, },
  { exact smul_le_smul_of_nonneg zero_le_one (sub_nonneg.mpr h) }
end

end

end ordered_algebra

section instances

variables {R : Type*} [linear_ordered_comm_ring R]

instance linear_ordered_comm_ring.to_ordered_algebra : ordered_algebra R R :=
{ smul_lt_smul_of_pos      := ordered_semiring.mul_lt_mul_of_pos_left,
  lt_of_smul_lt_smul_of_nonneg  := λ _ _ _, lt_of_mul_lt_mul_left }

end instances

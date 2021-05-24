/-
Copyright (c) 2021 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
import algebra.char_p.basic
import ring_theory.localization


/-!
# Characteristics of field of fractions

In this file we describe the characteristics of the field of fractions of an integral domain.


## Main results

If `R` is an `integral_domain` then the `fraction_ring R` has the same characteristic as `R`.


## TODO

* Could generalise this to any `R`-algebra over a `comm_semiring R`
  with injective algebra map.

-/

namespace fraction_ring

variables (R : Type*) [integral_domain R] (p : ℕ)

/-- If `R` has characteristic `p`, then so does `fraction_ring R`. -/
instance char_p [char_p R p] : char_p (fraction_ring R) p :=
{ cast_eq_zero_iff :=
  begin
    intro x,
    have hR := char_p.cast_eq_zero_iff R p x,
    split,
    {
      -- Want: (x:K) = 0 → p ∣ (x:ℕ)
      intro hp,
      apply hR.elim_left,
      -- From here on we have `(x:fraction_ring R) = 0` and want to show that `(x:R) = 0`.
      -- That should be shorter,
      -- the only real ingredient is `(fraction_map.injective (fraction_ring.of R))`.
      change (coe : ℕ → R) x = 0,
      have q := (fraction_map.injective (fraction_ring.of R)),
      unfold function.injective at q,
      apply q,
      simp,
      exact hp,
    },
    {
      -- Want: p ∣ (x:ℕ) → (x:K) = 0
      intro hp,
      have hR' := hR.elim_right hp,
      -- From here on we have `(x:R) = 0` and want to show that `(x:fraction_ring R) = 0`.
      -- That should be shorter, the only ingredient
      -- is using `is_scalar_tower`.
      change (algebra_map ℕ (fraction_ring R)) x = (algebra_map ℕ (fraction_ring R)) 0,
      rw is_scalar_tower.algebra_map_apply ℕ R (fraction_ring R) x,
      change (algebra_map ℕ R) x = (algebra_map ℕ R) 0 at hR',
      rw hR',
      simp,
    }
  end}

/-- If `R` has characteristic `0`, then so does `fraction_ring R`. -/
instance [char_zero R] : char_zero (fraction_ring R) :=
char_p.char_p_to_char_zero (fraction_ring R)

end fraction_ring

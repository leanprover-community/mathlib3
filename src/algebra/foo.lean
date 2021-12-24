/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import algebra.algebra.basic

/-!
# Name Of Class (tba)

We create a typeclass `foo R n` which carries around the fact that `(n : R) ≠ 0`.
This fact can be really annoying to carry and deduce automatically.

## Main declarations

* `foo R n`: `(n : R) ≠ 0` as a typeclass.

## Implementation details

Does the argument order matter? I would prefer `foo n R`, but not sure what TC prefers.

-/

class foo (R) [has_zero R] [has_one R] [has_add R] (n : ℕ) : Prop := (out : (n : R) ≠ 0)

lemma foo.ne (R) [has_zero R] [has_one R] [has_add R] (n : ℕ) [h : foo R n] : (n : R) ≠ 0 := h.out

namespace foo

universe variables u v w
variables {R : Type u} {S : Type v} {M : Type w} {n m : ℕ} {a b : ℕ+}

section add_monoid_with_one

variables [add_monoid R] [has_one R]

instance pnat [char_zero R] : foo R a := ⟨by exact_mod_cast a.ne_zero⟩

instance succ [char_zero R] : foo R (n.succ) := ⟨by exact_mod_cast n.succ_ne_zero⟩

end add_monoid_with_one

section semiring

variables [non_assoc_semiring R] [non_assoc_semiring S]

instance one [nontrivial R] : foo R 1 := ⟨ne_of_eq_of_ne nat.cast_one one_ne_zero⟩

-- will this instance cause loops/issues with `foo.pnat` and `foo.succ`?
instance char_zero [char_zero R] [foo S n] : foo R n :=
⟨by exact_mod_cast (show n ≠ 0, from λ h, let t := ne S n in by { rw h at t, exact t rfl })⟩

end semiring

section comm_ring

variables [comm_ring R] [ring S] [algebra R S]

instance no_zero_smul_divisors [foo R n] [nontrivial S] [no_zero_smul_divisors R S] : foo S n :=
⟨by { refine mt (λ h, no_zero_smul_divisors.algebra_map_injective R S _) (ne R n),
      rwa [ring_hom.map_nat_cast, ring_hom.map_zero] }⟩

end comm_ring

end foo

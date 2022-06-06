/-
Copyright (c) 2022 Jon Eugster.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jon Eugster.
-/
import algebra.char_p.basic
import ring_theory.ideal.quotient

/-!
# Equal and mixed characteristics

A commutative ring of characteristic zero can either be of 'equal characteristic zero'
or of 'mixed characteristic'. 'Equal characteristic zero' means that the quotient
ring `R⧸I` has characteristic zero for all proper ideals `I ⊆ R`.
Equivalently, `R` has equal characteristics zero if there is an injective
ring homomorphism `ℚ → R`, i.e. `R` contains a copy of `ℚ`.

Mixed characteristics `(0,p)` means `R` has characteristics `0` but there
exists an ideal such that `R⧸I` has characteristics `p`. Note that a ring
can be of different mixed characteristics simultaneously, e.g. `ℤ` has mixed
characteristics `(0,p)` for any `p ≠ 0`.

In this document we define equal characteristics zero and provide a theorem to split
into cases by characteristics.

## Main definitions

- `equal_char_zero` : class for a ring to be of 'equal characteristic zero'.
- `mixed_char_zero` : class for a ring to be of 'mixed characteristic zero'.

## Main results

## Implementation notes

## References

-/

/-!
### Equal characteristics zero
-/

/-- A ring has equal characteristic zero if `char(R⧸I) = 0` for all proper ideals `I ⊂ R`. -/
class equal_char_zero (R : Type*) [comm_ring R] : Prop :=
  (residue_char_zero : ∀(I : ideal R), I ≠ ⊤ → char_zero (R ⧸ I))

/-- This definition is trivial if `R` is a field. -/
lemma field.equal_char_zero (K : Type*) [field K] [h_char : char_zero K] :
  equal_char_zero K :=
⟨begin
  intros I hI',
  have hI := or_iff_not_imp_right.1 (ideal.eq_bot_or_top I) hI',
  exact ⟨begin
    intros x y h,
    apply h_char.cast_injective,
    calc ↑x = I.quot_equiv_of_eq_bot hI (submodule.quotient.mk x) : rfl
        ... = I.quot_equiv_of_eq_bot hI (submodule.quotient.mk y) : by {simp only [
                                                                    ideal.quotient.mk_eq_mk,
                                                                    map_nat_cast], rw h}
        ... = ↑y                                                  : rfl,
  end⟩
end⟩

namespace equal_char_zero

/-- Equal characteristics zero implies `char(R) = 0`. -/
instance char_zero (R : Type*) [comm_ring R] [nontrivial R] [equal_char_zero R] : char_zero R :=
⟨begin
  intros x y h,
  apply (equal_char_zero.residue_char_zero (⊥:ideal R) bot_ne_top).cast_injective,
  replace h := congr_arg (ideal.quotient.mk ⊥) h,
  simp at h,
  exact h,
end⟩

end equal_char_zero

/-!
### Mixed characteristics
-/

/--
A ring `R` of `char_zero` is of mixed characteristics if it is not of `equal_char_zero`.
i.e. if there exists an ideal `I` such that `R/I` has positive characteristic.
-/
class mixed_char_zero (R : Type*) [comm_ring R] (p : ℕ) : Prop :=
  (char_zero : char_zero R)
  (hp : p ≠ 0)
  (residue_char_p : ∃(I : ideal R), (I ≠ ⊤) ∧ char_p (R⧸I) p)

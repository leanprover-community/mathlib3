/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import algebra.module.basic
import ring_theory.ring_invo
import data.complex.is_R_or_C

/-!
# Conjugate semimodules

## Implementation notes

## References

* https://en.wikipedia.org/wiki/Complex_conjugate_vector_space

## Tags
-/

variables {R : Type*} [comm_semiring R]

/-- The conjugate of a semimodule `E` with respect to a ring involution `I`. -/
@[derive [add_comm_monoid], nolint unused_arguments]
def conjugate_semimodule (I : R ≃+* Rᵒᵖ) (E : Type*) [add_comm_monoid E] := E

instance {I : R ≃+* Rᵒᵖ} {E : Type*} [add_comm_monoid E] : inhabited (conjugate_semimodule I E) := ⟨0⟩

/-- The `is_R_or_C` complex conjugate semimodule of `E` -/
abbreviation conj_semimodule (𝕜 : Type*) [is_R_or_C 𝕜] (E : Type*) [add_comm_monoid E] :=
  conjugate_semimodule (is_R_or_C.conj_to_ring_equiv 𝕜) E

namespace conjugate_semimodule

variables {E : Type*}  [add_comm_monoid E]

/-- The identity map to the conjugate space -/
@[nolint unused_arguments] def to_conj (I : R ≃+* Rᵒᵖ) : E → conjugate_semimodule I E := id

/-- The identity map from the conjugate space -/
@[nolint unused_arguments] def from_conj (I : R ≃+* Rᵒᵖ) : conjugate_semimodule I E → E := id

@[simp] lemma from_to_conj {I : R ≃+* Rᵒᵖ} {x : conjugate_semimodule I E}: to_conj I (from_conj I x) = x := rfl
@[simp] lemma to_from_conj {I : R ≃+* Rᵒᵖ} {x : E}: from_conj I (to_conj I x) = x := rfl

variables {I : R ≃+* Rᵒᵖ}

instance [has_scalar R E] : has_scalar R (conjugate_semimodule I E) :=
{ smul := λ r x, to_conj I ((I r).unop • (from_conj I x)) }

instance [mul_action R E] : mul_action R (conjugate_semimodule I E) :=
{ one_smul := λ x, by { change to_conj I ((I 1).unop • (from_conj I x)) = x, simp },
  mul_smul := λ x y z,
  begin
    change to_conj I( (I (x * y)).unop • (from_conj I z)) = to_conj I ((I x).unop • (from_conj I ( to_conj I ((I y).unop • (from_conj I z)) ))),
    simp [mul_comm, mul_smul],
  end }

instance [distrib_mul_action R E] : distrib_mul_action R (conjugate_semimodule I E) :=
{ smul_add := λ r x y,
  begin
    change to_conj I ((I r).unop • (from_conj I (x + y)))
          = to_conj I ((I r).unop • (from_conj I x)) + to_conj I ((I r).unop • (from_conj I y)),
    simp [from_conj, to_conj, smul_add],
  end,
  smul_zero := λ r, by { change to_conj I ((I r).unop • (from_conj I 0)) = 0, simp [to_conj, from_conj] } }

instance [semimodule R E] : semimodule R (conjugate_semimodule I E) :=
{ add_smul := λ r s x,
  begin
    change to_conj I ((I (r + s)).unop • (from_conj I x))
      = to_conj I ((I r).unop • (from_conj I x)) + to_conj I ((I s).unop • (from_conj I x)),
    simp [to_conj, from_conj, add_smul],
  end,
  zero_smul := λ x, by { change to_conj I ((I 0).unop • (from_conj I x)) = 0,
                          simp [to_conj, from_conj, zero_smul] } }

end conjugate_semimodule

namespace conj_semimodule
open is_R_or_C

variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {E : Type*} [add_comm_monoid E] [semimodule 𝕜 E]
local postfix `†`:100 := @conj 𝕜 _
local notation `I` := conj_to_ring_equiv 𝕜

variables (𝕜)
/-- The identity map to the conjugate space -/
@[nolint unused_arguments] def to_conj : E → conj_semimodule 𝕜 E := conjugate_semimodule.to_conj I

/-- The identity map from the conjugate space -/
@[nolint unused_arguments] def from_conj : conj_semimodule 𝕜 E → E := conjugate_semimodule.from_conj I

variables {𝕜}

lemma smul_def {r : 𝕜} {x : E} : to_conj 𝕜 (r • x) = r† • (to_conj 𝕜 x) :=
by simp [to_conj, from_conj, has_scalar.smul, ring_equiv_apply, conjugate_semimodule.to_from_conj]

lemma smul_def' {r : 𝕜} {x : conj_semimodule 𝕜 E} : from_conj 𝕜 (r • x) = r† • (from_conj 𝕜 x) :=
begin
  simp [from_conj, to_conj, has_scalar.smul],
end

lemma from_conj_add {x y : conj_semimodule 𝕜 E} : from_conj 𝕜 (x + y) = from_conj 𝕜 x + from_conj 𝕜 y := rfl
lemma to_conj_add {x y : E} : to_conj 𝕜 (x + y) = to_conj 𝕜 x + to_conj 𝕜 y := rfl

end conj_semimodule

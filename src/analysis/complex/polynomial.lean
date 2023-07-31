/-
Copyright (c) 2019 Chris Hughes All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
-/
import analysis.complex.liouville
import field_theory.is_alg_closed.basic

/-!
# The fundamental theorem of algebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves that every nonconstant complex polynomial has a root using Liouville's theorem.

As a consequence, the complex numbers are algebraically closed.
-/

open polynomial
open_locale polynomial

namespace complex

/-- **Fundamental theorem of algebra**: every non constant complex polynomial
  has a root -/
lemma exists_root {f : ℂ[X]} (hf : 0 < degree f) : ∃ z : ℂ, is_root f z :=
begin
  contrapose! hf,
  obtain ⟨c, hc⟩ := (f.differentiable.inv hf).exists_const_forall_eq_of_bounded _,
  { obtain rfl : f = C c⁻¹ := polynomial.funext (λ z, by rw [eval_C, ← hc z, inv_inv]),
    exact degree_C_le },
  { obtain ⟨z₀, h₀⟩ := f.exists_forall_norm_le,
    simp only [bounded_iff_forall_norm_le, set.forall_range_iff, norm_inv],
    exact ⟨‖eval z₀ f‖⁻¹, λ z, inv_le_inv_of_le (norm_pos_iff.2 $ hf z₀) (h₀ z)⟩ },
end

instance is_alg_closed : is_alg_closed ℂ :=
is_alg_closed.of_exists_root _ $ λ p _ hp, complex.exists_root $ degree_pos_of_irreducible hp

end complex

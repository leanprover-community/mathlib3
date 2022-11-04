/-
Copyright (c) 2019 Chris Hughes All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
-/
import analysis.complex.liouville
import field_theory.is_alg_closed.basic

/-!
# The fundamental theorem of algebra

This file proves that every nonconstant complex polynomial has a root.

As a consequence, the complex numbers are algebraically closed.
-/

/-open complex polynomial metric filter set
open_locale classical
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
  { convert degree_C_le,
    refine polynomial.funext (λ z, _),
    exacts [c⁻¹, by rw [eval_C, ← hc z, inv_inv]] },
  { obtain ⟨z₀, h₀⟩ := f.exists_forall_norm_le,
    simp_rw [metric.bounded_iff_subset_ball (0 : ℂ), set.range_subset_iff,
             metric.mem_closed_ball, dist_eq, sub_zero, ← norm_eq_abs, norm_inv],
    have := _, refine ⟨_, λ y, (inv_le_inv _ this).2 $ h₀ y⟩,
    exacts [this.trans_le (h₀ y), norm_pos_iff.2 (hf z₀)] },
end

instance is_alg_closed : is_alg_closed ℂ :=
is_alg_closed.of_exists_root _ $ λ p _ hp, complex.exists_root $ degree_pos_of_irreducible hp

end complex

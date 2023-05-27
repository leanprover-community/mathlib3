/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import analysis.calculus.deriv.basic

/-!
# Support of the derivative of a function

In this file we prove that the (topological) support of a function includes the support of its
derivative. As a corollary, we show that the derivative of a function with compact support has
compact support.

## Keywords

derivative, support
-/

universes u v

variables {𝕜 : Type u} [nontrivially_normed_field 𝕜]
variables {E : Type v} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {f : 𝕜 → E}

/-! ### Support of derivatives -/

section support

open function

lemma support_deriv_subset : support (deriv f) ⊆ tsupport f :=
begin
  intros x,
  rw [← not_imp_not],
  intro h2x,
  rw [not_mem_tsupport_iff_eventually_eq] at h2x,
  exact nmem_support.mpr (h2x.deriv_eq.trans (deriv_const x 0))
end

lemma has_compact_support.deriv (hf : has_compact_support f) : has_compact_support (deriv f) :=
hf.mono' support_deriv_subset

end support

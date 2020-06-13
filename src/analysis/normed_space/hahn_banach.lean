/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import analysis.normed_space.operator_norm
import analysis.convex.cone

/-!
# Hahn-Banach theorem

In this file we prove a version of Hahn-Banach theorem for continuous linear
functions on normed spaces.

We also prove a standard corollary, needed for the isometric inclusion in the double dual.

## TODO

Prove more corollaries

-/

section basic
variables {E : Type*} [normed_group E] [normed_space ℝ E]

/-- Hahn-Banach theorem for continuous linear functions. -/
theorem exists_extension_norm_eq (p : subspace ℝ E) (f : p →L[ℝ] ℝ) :
  ∃ g : E →L[ℝ] ℝ, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ :=
begin
  rcases exists_extension_of_le_sublinear ⟨p, f⟩ (λ x, ∥f∥ * ∥x∥)
    (λ c hc x, by simp only [norm_smul c x, real.norm_eq_abs, abs_of_pos hc, mul_left_comm])
    (λ x y, _) (λ x, le_trans (le_abs_self _) (f.le_op_norm _))
    with ⟨g, g_eq, g_le⟩,
  set g' := g.mk_continuous (∥f∥)
    (λ x, abs_le.2 ⟨neg_le.1 $ g.map_neg x ▸ norm_neg x ▸ g_le (-x), g_le x⟩),
  { refine ⟨g', g_eq, _⟩,
    { apply le_antisymm (g.mk_continuous_norm_le (norm_nonneg f) _),
      refine f.op_norm_le_bound (norm_nonneg _) (λ x, _),
      dsimp at g_eq,
      rw ← g_eq,
      apply g'.le_op_norm } },
  { simp only [← mul_add],
    exact mul_le_mul_of_nonneg_left (norm_add_le x y) (norm_nonneg f) }
end

end basic

section dual_vector
variables {E : Type*} [normed_group E] [normed_space ℝ E]

open continuous_linear_equiv
open_locale classical

lemma coord_self' (x : E) (h : x ≠ 0) : (∥x∥ • (coord ℝ x h))
  ⟨x, submodule.mem_span_singleton_self x⟩ = ∥x∥ :=
calc (∥x∥ • (coord ℝ x h)) ⟨x, submodule.mem_span_singleton_self x⟩
    = ∥x∥ • (linear_equiv.coord ℝ E x h) ⟨x, submodule.mem_span_singleton_self x⟩ : rfl
... = ∥x∥ • 1 : by rw linear_equiv.coord_self ℝ E x h
... = ∥x∥ : mul_one _

lemma coord_norm' (x : E) (h : x ≠ 0) : ∥∥x∥ • coord ℝ x h∥ = 1 :=
by rw [norm_smul, norm_norm, coord_norm, mul_inv_cancel (mt norm_eq_zero.mp h)]

/-- Corollary of Hahn-Banach.  Given a nonzero element `x` of a normed space, there exists an
    element of the dual space, of norm 1, whose value on `x` is `∥x∥`. -/
theorem exists_dual_vector (x : E) (h : x ≠ 0) : ∃ g : E →L[ℝ] ℝ, ∥g∥ = 1 ∧ g x = ∥x∥ :=
begin
  cases exists_extension_norm_eq (submodule.span ℝ {x}) (∥x∥ • coord ℝ x h) with g hg,
  use g, split,
  { rw [hg.2, coord_norm'] },
  { calc g x = g (⟨x, submodule.mem_span_singleton_self x⟩ : submodule.span ℝ {x}) : by simp
  ... = (∥x∥ • coord ℝ x h) (⟨x, submodule.mem_span_singleton_self x⟩ : submodule.span ℝ {x}) : by rw ← hg.1
  ... = ∥x∥ : by rw coord_self' }
end

/-- Variant of the above theorem, eliminating the hypothesis that `x` be nonzero, and choosing
    the dual element arbitrarily when `x = 0`. -/
theorem exists_dual_vector' (h : 0 < vector_space.dim ℝ E) (x : E) : ∃ g : E →L[ℝ] ℝ,
  ∥g∥ = 1 ∧ g x = ∥x∥ :=
begin
  by_cases hx : x = 0,
  { cases dim_pos_iff_exists_ne_zero.mp h with y hy,
    cases exists_dual_vector y hy with g hg,
    use g, refine ⟨hg.left, _⟩, simp [hx] },
  { exact exists_dual_vector x hx }
end

-- TODO: These corollaries are also true over ℂ.

end dual_vector

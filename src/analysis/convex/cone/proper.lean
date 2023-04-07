/-
Copyright (c) 2022 Apurva Nakade All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import analysis.inner_product_space.adjoint

/-!

We define the closure of the convex cone over a real inner product space as a convex cone.

-/

-- TODO: add proper cones and farkas' lemma


open continuous_linear_map filter

namespace convex_cone

variables {E : Type*} [normed_add_comm_group E] [inner_product_space ℝ E]

example : continuous (function.uncurry (λ (x y : ℝ), x + y)) :=
begin
  exact continuous_add,
end

/-- The closure of a convex cone inside a real inner product space is a convex cone. This
construction is mainly used for defining maps between proper cones. -/
def closure (K : convex_cone ℝ E) : convex_cone ℝ E :=
{ carrier := closure ↑K,
  smul_mem' := λ c hc _ h₁,
    map_mem_closure (continuous_id'.const_smul c) h₁ (λ _ h₂, K.smul_mem hc h₂),
  add_mem' := λ _ h₁ _ h₂, map_mem_closure₂ continuous_add h₁ h₂ K.add_mem }

@[simp] lemma coe_closure {K : convex_cone ℝ E} : (K.closure : set E) = _root_.closure K := rfl

lemma mem_closure_iff_seq_limit {K : convex_cone ℝ E} {a : E} :
  a ∈ K.closure ↔ ∃ x : ℕ → E, (∀ n : ℕ, x n ∈ K) ∧ tendsto x at_top (nhds a) :=
by simp_rw [← set_like.mem_coe, coe_closure, mem_closure_iff_seq_limit]

end convex_cone

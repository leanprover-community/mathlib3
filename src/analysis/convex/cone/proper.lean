/-
Copyright (c) 2022 Apurva Nakade All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import analysis.inner_product_space.adjoint

/-!

We define a proper cone as a nonempty, closed, convex cone. Proper cones are used in defining conic
programs which generalize linear programs. A linear program is a conic program for the positive
cone. We then prove Farkas' lemma for conic programs following the proof in the reference below.
Farkas' lemma is equivalent to strong duality. So, once have the definitions of conic programs and
linear programs, the results from this file can be used to prove duality theorems.

## References

- [B. Gartner and J. Matousek, Cone Programming][gartnerMatousek]

-/

open continuous_linear_map filter

namespace convex_cone

variables {E : Type*} [add_comm_monoid E] [has_smul ℝ E] [topological_space E]
  [has_continuous_const_smul ℝ E] [has_continuous_add E]

/-- The closure of a convex cone inside a real inner product space is a convex cone. This
construction is mainly used for defining maps between proper cones. -/
protected def closure (K : convex_cone ℝ E) : convex_cone ℝ E :=
{ carrier := closure ↑K,
  smul_mem' :=
    λ c hc _ h₁, map_mem_closure (continuous_id'.const_smul c) h₁ (λ _ h₂, K.smul_mem hc h₂),
  add_mem' := λ _ h₁ _ h₂, map_mem_closure₂ continuous_add h₁ h₂ K.add_mem }

@[simp, norm_cast] lemma coe_closure (K : convex_cone ℝ E) : (K.closure : set E) = closure K := rfl

protected lemma mem_closure {K : convex_cone ℝ E} {a : E} :
  a ∈ K.closure ↔ a ∈ closure (K : set E) :=
iff.rfl

end convex_cone

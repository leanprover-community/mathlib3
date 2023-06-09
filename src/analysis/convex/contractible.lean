/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.convex.star
import topology.homotopy.contractible

/-!
# A convex set is contractible

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that a (star) convex set in a real topological vector space is a contractible
topological space.
-/

variables {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E]
  [has_continuous_add E] [has_continuous_smul ℝ E] {s : set E} {x : E}

/-- A non-empty star convex set is a contractible space. -/
protected lemma star_convex.contractible_space (h : star_convex ℝ x s) (hne : s.nonempty) :
  contractible_space s :=
begin
  refine (contractible_iff_id_nullhomotopic _).2 ⟨⟨x, h.mem hne⟩,
    ⟨⟨⟨λ p, ⟨p.1.1 • x + (1 - p.1.1) • p.2, _⟩, _⟩, λ x, _, λ x, _⟩⟩⟩,
  { exact h p.2.2 p.1.2.1 (sub_nonneg.2 p.1.2.2) (add_sub_cancel'_right _ _) },
  { exact ((continuous_subtype_val.fst'.smul continuous_const).add
      ((continuous_const.sub continuous_subtype_val.fst').smul
        continuous_subtype_val.snd')).subtype_mk _ },
  { ext1, simp },
  { ext1, simp }
end

/-- A non-empty convex set is a contractible space. -/
protected lemma convex.contractible_space (hs : convex ℝ s) (hne : s.nonempty) :
  contractible_space s :=
let ⟨x, hx⟩ := hne in (hs.star_convex hx).contractible_space hne

@[priority 100] instance real_topological_vector_space.contractible_space : contractible_space E :=
(homeomorph.set.univ E).contractible_space_iff.mp $ convex_univ.contractible_space set.univ_nonempty

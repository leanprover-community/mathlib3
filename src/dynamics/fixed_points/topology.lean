/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl
-/
import dynamics.fixed_points.basic
import topology.separation

/-!
# Topological properties of fixed points

Currently this file contains two lemmas:

- `is_fixed_pt_of_tendsto_iterate`: if `f^n(x) → y` and `f` is continuous at `y`, then `f y = y`;
- `is_closed_fixed_points`: the set of fixed points of a continuous map is a closed set.

## TODO

fixed points, iterates
-/

variables {α : Type*} [topological_space α] [t2_space α] {f : α → α}

open function filter
open_locale topological_space

/-- If the iterates `f^[n] x₀` converge to `x` and `f` is continuous at `x`,
then `x` is a fixed point for `f`. -/
lemma is_fixed_pt_of_tendsto_iterate {x : α} (hf : continuous_at f x)
  (hx : ∃ x₀ : α, tendsto (λ n, f^[n] x₀) at_top (𝓝 x)) :
  is_fixed_pt f x :=
begin
  rcases hx with ⟨x₀, hx⟩,
  refine tendsto_nhds_unique at_top_ne_bot ((tendsto_add_at_top_iff_nat 1).1 _) hx,
  simp only [iterate_succ' f],
  exact tendsto.comp hf hx
end

/-- The set of fixed points of a continuous map is a closed set. -/
lemma is_closed_fixed_points (hf : continuous f) : is_closed (fixed_points f) :=
is_closed_eq hf continuous_id

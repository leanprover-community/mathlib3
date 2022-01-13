/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.function.lp_space

/-!
# Convergence in measure

-/

open topological_space filter
open_locale nnreal ennreal measure_theory topological_space

namespace measure_theory

variables {α ι E : Type*} {m : measurable_space α} {μ : measure α}

/-- TODO -/
def tendsto_in_measure [preorder ι] [has_dist E] (f : ι → α → E) (g : α → E) : Prop :=
∀ ε (hε : 0 < ε), tendsto (λ i, μ {x | ε ≤ dist (f i x) (g x)}) at_top (𝓝 0)


end measure_theory

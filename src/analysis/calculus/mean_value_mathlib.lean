/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import analysis.calculus.mean_value

/-!
# Stuff for analysis.calculus.mean_value
-/

theorem convex.strict_mono_on_of_has_deriv_at_pos {D : set ℝ} (hD : convex ℝ D) {f f' : ℝ → ℝ}
  (hf : ∀ x ∈ D, has_deriv_at f (f' x) x) (hf' : ∀ x ∈ interior D, 0 < f' x) :
  strict_mono_on f D :=
begin
  refine convex.strict_mono_on_of_deriv_pos hD _ _,
  { exact has_deriv_at.continuous_on hf },
  intros x hx,
  rw has_deriv_at.deriv (hf x (interior_subset hx)),
  exact hf' x hx
end

theorem convex.strict_anti_on_of_has_deriv_at_neg {D : set ℝ} (hD : convex ℝ D) {f f' : ℝ → ℝ}
  (hf : ∀ x ∈ D, has_deriv_at f (f' x) x) (hf' : ∀ x ∈ interior D, f' x < 0) :
  strict_anti_on f D :=
begin
  refine convex.strict_anti_on_of_deriv_neg hD _ _,
  { exact has_deriv_at.continuous_on hf },
  intros x hx,
  rw has_deriv_at.deriv (hf x (interior_subset hx)),
  exact hf' x hx
end

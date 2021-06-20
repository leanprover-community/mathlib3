/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.deriv

open asymptotics set
open_locale topological_space

section
variables {E F : Type*} [normed_group E] [normed_space ℝ E]
[normed_group F] [normed_space ℝ F]
{s : set E}
(s_conv : convex s) (s_open : is_open s)
{f : E → F} {f' : E → (E →L[ℝ] F)} {f'' : E →L[ℝ] (E →L[ℝ] F)}
(hf : ∀ x ∈ s, has_fderiv_at f (f' x) x)
{x : E} (xs : x ∈ closure s) (hx : has_fderiv_within_at f' f'' s x)

include s_conv s_open hx

lemma glou (v w : E) (hv : x + v ∈ s) (hw : x + v + w ∈ s) :
  is_o (λ (h : ℝ), f (x + h • v + h • w) - f (x + h • v) - h • f' x w
    - h • f'' v w - (h^2/2) • f'' w w) (λ h, h^2) (𝓝[Ioi (0 : ℝ)] 0) :=
begin
  apply is_o_iff.2 (λ ε εpos, _),
  apply filter.eventually_of_forall (λ h, _),
  let g := λ t, f (x + h • v + (t * h) • w) - (t * h) • f' x w  - (t * h) • f'' v w
    - ((t * h)^2/2) • f'' w w,
  let g' := λ t, f' (x + h • v + (t * h) • w) (h • w) - h • f' x w
    - h • f'' v w - (t * h^2) • f'' w w,
  have : ∀ t ∈ Icc (0 : ℝ) 1, has_deriv_within_at g (g' t) (Icc 0 1) t,

end


end

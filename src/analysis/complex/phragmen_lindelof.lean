/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.complex.abs_max

/-!
-/

open topological_space set filter asymptotics
open_locale topological_space filter

namespace phragmen_lindelof

variables {E : Type*} [normed_group E] [normed_space ℂ E] [second_countable_topology E]

lemma horizontal_strip {a b c C : ℝ} {f : ℂ → E}
  (hd : diff_on_int_cont ℂ f (complex.im ⁻¹' (Icc a b)))
  (hO : is_O (λ z, real.log ∥f z∥) (λ z, real.exp (c * z.re))
    (comap (abs ∘ complex.re) at_top ⊓ 𝓟 (complex.im ⁻¹' (Icc a b))))
  (hle : ∀ z : ℂ, (z.im = a ∨ z.im = b) → ∥f z∥ ≤ C) {z : ℂ} (hz : z.im ∈ Icc a b) :
  ∥f z∥ ≤ C :=
begin
  -- If `z.im = a` or `z.im = b`, then apply `hle`, otherwise `z.im ∈ Ioo a b`
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hz with (hz|hz|hz'),
  { exact hle z (or.inl hz) }, { exact hle z (or.inr hz) }, clear hz, rename hz' hz,
  
end

end phragmen_lindelof

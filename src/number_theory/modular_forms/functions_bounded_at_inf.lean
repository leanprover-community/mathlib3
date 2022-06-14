/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

import algebra.module.submodule.basic
import analysis.complex.upper_half_plane

/-!
# Bounded at infinity

For complex valued functions on the upper half plane, this file defines the notion of bounded at
infinity and zero at infinity. Both of which are relevant for defining modular forms.
-/

open complex

open_locale topological_space manifold upper_half_plane

namespace upper_half_plane

/--Filter for approaching `i∞`-/
def at_I_inf := filter.at_top.comap upper_half_plane.im

lemma at_I_inf_mem (S : set ℍ) : S ∈ at_I_inf ↔ (∃ A : ℝ, ∀ z : ℍ, A ≤ im z → z ∈ S) :=
begin
  simp only [at_I_inf, filter.mem_comap', filter.mem_at_top_sets, ge_iff_le, set.mem_set_of_eq,
    upper_half_plane.coe_im],
  split,
  { intro h, cases h with a h, refine ⟨a, (λ z hz, by {apply h (im z) hz , refl})⟩ },
  { refine (λ h, by {cases h with A h,
    refine ⟨A, (λ b hb x hx, by {apply (h x), rw hx, exact hb})⟩}) }
end

/--A function ` f : ℍ → ℂ` is bounded at infinity if there exist real numbers `M,A` such that
for all `z ∈ ℍ` with `im z ≥ A` we have `abs(f (z)) ≤ M`,
 i.e. the function is bounded as you approach `i∞`. -/
def is_bound_at_inf (f : ℍ → ℂ) : Prop := asymptotics.is_O at_I_inf f (1 : ℍ → ℂ)

/--A function ` f : ℍ → ℂ` is zero at infinity if for any `ε > 0` there exist a real
number `A` such that for all `z ∈ ℍ` with `im z ≥ A` we have `abs(f (z)) ≤ ε`,
 i.e. the function tends to zero as you approach `i∞`. -/
def is_zero_at_inf (f : ℍ → ℂ) : Prop := filter.tendsto f at_I_inf (𝓝 0)

lemma zero_form_is_zero_at_inf : is_zero_at_inf 0 := tendsto_const_nhds

lemma is_zero_at_inf_is_bound (f : ℍ → ℂ) (hf : is_zero_at_inf f) : is_bound_at_inf f :=
begin
  apply asymptotics.is_O_of_div_tendsto_nhds, { simp, }, { convert hf, ext1, simp, }
end

lemma zero_form_is_bound : is_bound_at_inf 0 :=
  is_zero_at_inf_is_bound _ zero_form_is_zero_at_inf

/--Module of funcitons that are zero at infinity.-/
def zero_at_infty_submodule : submodule ℂ (ℍ → ℂ) :=
{ carrier := is_zero_at_inf,
  zero_mem' := zero_form_is_zero_at_inf,
  add_mem' := by { intros a b ha hb, simpa using ha.add hb },
  smul_mem' := by { intros c f hf, simpa using hf.const_mul c }, }

/--Module of funcitons that are bounded at infinity.-/
def bounded_at_infty_submodule : submodule ℂ (ℍ → ℂ) :=
{ carrier := is_bound_at_inf,
  zero_mem' := zero_form_is_bound,
  add_mem' := by { intros f g hf hg, simpa using hf.add hg, },
  smul_mem' := by { intros c f hf, simpa using hf.const_mul_left c }, }

lemma prod_of_bound_is_bound {f g : ℍ → ℂ} (hf : is_bound_at_inf f) (hg : is_bound_at_inf g) :
  is_bound_at_inf (f * g) := by simpa using hf.mul hg

@[simp]lemma bound_mem (f : ℍ → ℂ) :
  is_bound_at_inf f ↔ ∃ (M A : ℝ), ∀ z : ℍ, A ≤ im z → abs (f z) ≤ M :=
begin
  simp [is_bound_at_inf, asymptotics.is_O_iff, filter.eventually, at_I_inf_mem],
end

end upper_half_plane

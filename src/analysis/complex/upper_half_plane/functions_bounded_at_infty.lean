/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

import algebra.module.submodule.basic
import analysis.complex.upper_half_plane.basic
import order.filter.zero_and_bounded_at_filter

/-!
# Bounded at infinity

For complex valued functions on the upper half plane, this file defines the filter `at_im_infty`
required for defining when functions are bounded at infinity and zero at infinity.
Both of which are relevant for defining modular forms.

-/

open complex filter

open_locale topological_space upper_half_plane

noncomputable theory

namespace upper_half_plane

/--Filter for approaching `i∞`-/
def at_im_infty := filter.at_top.comap upper_half_plane.im

lemma at_im_infty_basis : (at_im_infty).has_basis (λ _, true) (λ (i : ℝ), im ⁻¹' set.Ici i) :=
filter.has_basis.comap upper_half_plane.im filter.at_top_basis

lemma at_im_infty_mem (S : set ℍ) : S ∈ at_im_infty ↔ (∃ A : ℝ, ∀ z : ℍ, A ≤ im z → z ∈ S) :=
begin
  simp only [at_im_infty, filter.mem_comap', filter.mem_at_top_sets, ge_iff_le, set.mem_set_of_eq,
    upper_half_plane.coe_im],
   refine ⟨λ ⟨a, h⟩, ⟨a, (λ z hz, h (im z) hz rfl)⟩, _⟩,
  { rintro ⟨A, h⟩,
    refine ⟨A, λ b hb x hx, h x _⟩,
    rwa hx, }
end

/--A function ` f : ℍ → ℂ` is bounded at infinity if there exist real numbers `M, A` such that
for all `z ∈ ℍ` with `im z ≥ A` we have `abs(f (z)) ≤ M`,
 i.e. the function is bounded as you approach `i∞`. -/
def is_bounded_at_im_infty (f : ℍ → ℂ) : Prop := asymptotics.is_O at_im_infty f (1 : ℍ → ℂ)

/--A function ` f : ℍ → ℂ` is zero at infinity if for any `ε > 0` there exist a real
number `A` such that for all `z ∈ ℍ` with `im z ≥ A` we have `abs(f (z)) ≤ ε`,
 i.e. the function tends to zero as you approach `i∞`. -/
def is_zero_at_im_infty (f : ℍ → ℂ) : Prop := filter.tendsto f at_im_infty (𝓝 0)

lemma zero_form_is_bounded_at_im_infty : is_bounded_at_im_infty 0 :=
zero_is_bounded_at_filter _

/--Module of functions that are zero at infinity.-/
def zero_at_im_infty_submodule : submodule ℂ (ℍ → ℂ) := zero_at_filter_submodule at_im_infty

/--Subalgebra of functions that are bounded at infinity.-/
def bounded_at_im_infty_subalgebra : subalgebra ℂ (ℍ → ℂ) := bounded_filter_subalgebra at_im_infty

lemma prod_of_bounded_is_bounded {f g : ℍ → ℂ} (hf : is_bounded_at_im_infty f) (hg : is_bounded_at_im_infty g) :
  is_bounded_at_im_infty (f * g) :=
by simpa only [pi.one_apply, mul_one, norm_eq_abs, complex.abs_mul] using hf.mul hg

@[simp] lemma bounded_mem (f : ℍ → ℂ) :
  is_bounded_at_im_infty f ↔ ∃ (M A : ℝ), ∀ z : ℍ, A ≤ im z → abs (f z) ≤ M :=
begin
  simp [is_bounded_at_im_infty, asymptotics.is_O_iff, filter.eventually, at_im_infty_mem],
end

end upper_half_plane

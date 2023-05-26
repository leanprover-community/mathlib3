theorem has_strict_deriv_at.has_strict_fderiv_at_equiv {f : 𝕜 → 𝕜} {f' x : 𝕜}
  (hf : has_strict_deriv_at f f' x) (hf' : f' ≠ 0) :
  has_strict_fderiv_at f
    (continuous_linear_equiv.units_equiv_aut 𝕜 (units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) x :=
hf

theorem has_deriv_at.has_fderiv_at_equiv {f : 𝕜 → 𝕜} {f' x : 𝕜} (hf : has_deriv_at f f' x)
  (hf' : f' ≠ 0) :
  has_fderiv_at f (continuous_linear_equiv.units_equiv_aut 𝕜 (units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) x :=
hf

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem has_strict_deriv_at.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜}
  (hg : continuous_at g a) (hf : has_strict_deriv_at f f' (g a)) (hf' : f' ≠ 0)
  (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
  has_strict_deriv_at g f'⁻¹ a :=
(hf.has_strict_fderiv_at_equiv hf').of_local_left_inverse hg hfg

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has a
nonzero derivative `f'` at `f.symm a` in the strict sense, then `f.symm` has the derivative `f'⁻¹`
at `a` in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
lemma local_homeomorph.has_strict_deriv_at_symm (f : local_homeomorph 𝕜 𝕜) {a f' : 𝕜}
  (ha : a ∈ f.target) (hf' : f' ≠ 0) (htff' : has_strict_deriv_at f f' (f.symm a)) :
  has_strict_deriv_at f.symm f'⁻¹ a :=
htff'.of_local_left_inverse (f.symm.continuous_at ha) hf' (f.eventually_right_inverse ha)

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem has_deriv_at.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜}
  (hg : continuous_at g a) (hf : has_deriv_at f f' (g a)) (hf' : f' ≠ 0)
  (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
  has_deriv_at g f'⁻¹ a :=
(hf.has_fderiv_at_equiv hf').of_local_left_inverse hg hfg

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
nonzero derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
lemma local_homeomorph.has_deriv_at_symm (f : local_homeomorph 𝕜 𝕜) {a f' : 𝕜}
  (ha : a ∈ f.target) (hf' : f' ≠ 0) (htff' : has_deriv_at f f' (f.symm a)) :
  has_deriv_at f.symm f'⁻¹ a :=
htff'.of_local_left_inverse (f.symm.continuous_at ha) hf' (f.eventually_right_inverse ha)

lemma has_deriv_at.eventually_ne (h : has_deriv_at f f' x) (hf' : f' ≠ 0) :
  ∀ᶠ z in 𝓝[≠] x, f z ≠ f x :=
(has_deriv_at_iff_has_fderiv_at.1 h).eventually_ne
  ⟨‖f'‖⁻¹, λ z, by field_simp [norm_smul, mt norm_eq_zero.1 hf']⟩

lemma has_deriv_at.tendsto_punctured_nhds (h : has_deriv_at f f' x) (hf' : f' ≠ 0) :
  tendsto f (𝓝[≠] x) (𝓝[≠] (f x)) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
  h.continuous_at.continuous_within_at (h.eventually_ne hf')

theorem not_differentiable_within_at_of_local_left_inverse_has_deriv_within_at_zero
  {f g : 𝕜 → 𝕜} {a : 𝕜} {s t : set 𝕜} (ha : a ∈ s) (hsu : unique_diff_within_at 𝕜 s a)
  (hf : has_deriv_within_at f 0 t (g a)) (hst : maps_to g s t) (hfg : f ∘ g =ᶠ[𝓝[s] a] id) :
  ¬differentiable_within_at 𝕜 g s a :=
begin
  intro hg,
  have := (hf.comp a hg.has_deriv_within_at hst).congr_of_eventually_eq_of_mem hfg.symm ha,
  simpa using hsu.eq_deriv _ this (has_deriv_within_at_id _ _)
end

theorem not_differentiable_at_of_local_left_inverse_has_deriv_at_zero
  {f g : 𝕜 → 𝕜} {a : 𝕜} (hf : has_deriv_at f 0 (g a)) (hfg : f ∘ g =ᶠ[𝓝 a] id) :
  ¬differentiable_at 𝕜 g a :=
begin
  intro hg,
  have := (hf.comp a hg.has_deriv_at).congr_of_eventually_eq hfg.symm,
  simpa using this.unique (has_deriv_at_id a)
end

import geometry.manifold.times_cont_mdiff
import analysis.complex.cauchy_integral
import topology.locally_constant.basic

open_locale manifold topological_space
open complex

variables {M : Type*} [topological_space M] [charted_space ℂ M]
  [smooth_manifold_with_corners 𝓘(ℂ) M]

lemma non_zero_deriv (f : ℂ → ℂ) (s : set ℂ) (hs : is_open s) (c : ℝ) (hf : ∀ x ∈ s, ∥f x∥ = c) (f' : ℂ → ℂ)
  (hf' : ∀ x ∈ s, has_strict_deriv_at f (f' x) x) (x : ℂ) (hx : x ∈ s) :
  f' x = 0 :=
begin
  by_contradiction,
  have H₁ := has_strict_deriv_at.map_nhds_eq (hf' x hx) h,
  have H₂ : s ∈ 𝓝 x := hs.mem_nhds hx,
  have H₃ : f '' s ∈ filter.map f (𝓝 x) := filter.image_mem_map H₂,
  rw H₁ at H₃,
  rw metric.mem_nhds_iff at H₃,
  obtain ⟨ε, hε, H₄⟩ := H₃,
  by_cases hfx : f x = 0, -- ALEX HOMEWORK
  { sorry },
  let η : ℝ := sorry, -- ε / (2 * ∥f x∥)
  have hη : 0 < η := sorry,
  have hη' : η * abs (f x) < ε := sorry,
  have H₅ : (1 + η) • f x ∈ metric.ball (f x) ε,
  { simp [dist_eq_norm, norm_eq_abs],
    calc abs ((1 + ↑η) * f x - f x)
        = abs ((η : ℂ) * f x) : by congr; ring
    ... < ε : _,
    simp,
    rw _root_.abs_of_nonneg hη.le,
    exact hη' },
  obtain ⟨y, hys, hy⟩ := H₄ H₅,
  have H₆ := congr_arg norm hy,
  simp only [of_real_add, normed_field.norm_mul, real_smul, of_real_one] at H₆,
  rw (hf y hys).trans (hf x hx).symm at H₆,
  simp only [norm_eq_abs] at H₆,
  norm_cast at H₆,
  have H₇ : (1 - |1 + η|) * abs (f x) = 0,
  { linarith, },
  rw _root_.abs_of_nonneg (by linarith : 0 ≤ 1 + η) at H₇,
  have H₈ : abs (f x) ≠ 0 := by simpa using hfx,
  have H₉ : 1 - (1 + η) ≠ 0 := by linarith,
  have := mul_ne_zero H₉ H₈,
  contradiction,
end

theorem is_const_of_deriv_within_eq_zero {𝕜 : Type*} {G : Type*} [is_R_or_C 𝕜]
  [normed_group G] [normed_space 𝕜 G] {f : 𝕜 → G} (hf : differentiable 𝕜 f)
  (s : set 𝕜) (hf' : ∀ x ∈ s, deriv f x = 0) :
∀ x ∈ s, ∀ y ∈ s, f x = f y := sorry

lemma non_zero_deriv_to_loc_const (f : ℂ → ℂ) (s : set ℂ) (hs : is_open s) (c : ℝ)
  (hf : ∀ x ∈ s, ∥f x∥ = c) (f' : ℂ → ℂ)
  (hf' : ∀ x ∈ s, has_strict_deriv_at f (f' x) x) :
   ∀ x ∈ s, ∀ y ∈ s, f x = f y :=
begin
  have := non_zero_deriv f s hs c hf f' hf',
  refine is_const_of_deriv_within_eq_zero _ s _ ,
  sorry,
end

example {f : M → ℂ} (hf : times_cont_mdiff 𝓘(ℂ) 𝓘(ℂ) 1 f) :
  is_locally_constant f :=
begin
  rw (is_locally_constant.tfae f).out 0 4,
  intros p,
  refine ⟨(chart_at ℂ p).source, (chart_at ℂ p).open_source, mem_chart_source ℂ p, _⟩,
  intros x hx,
  rw times_cont_mdiff_iff at hf,
  have H₁ := hf.2 p,
  simp at H₁,
  have H₂ := H₁.differentiable_on rfl.le,
  have H₃ := is_open_set_of_mem_nhds_and_is_max_on_norm H₂,
  simp at H₃,
  -- set at H₃ determines
  convert non_zero_deriv_to_loc_const (f ∘ ((chart_at ℂ p).symm))
    ((chart_at ℂ p).to_local_equiv.target) _ _ _ _ _ ((chart_at ℂ p) x) _  ((chart_at ℂ p) p) _,



end

-- example {f : M → ℂ} (hf : times_cont_mdiff 𝓘(ℂ) 𝓘(ℂ) 1 f) :
--   is_open {p | is_max_on (norm ∘ f) set.univ p}  :=
-- begin
--   refine is_open_iff_mem_nhds.2 (λ p hp, _),
--   rw ← (chart_at ℂ p).symm_map_nhds_eq (mem_chart_source ℂ p),
--   rw filter.mem_map,
--   let s := (chart_at ℂ p).symm ⁻¹' {z | is_max_on (norm ∘ f) set.univ z},
--   have hs : s ⊆ (chart_at ℂ p).target := sorry,
--   rw times_cont_mdiff_iff at hf,
--   have := hf.2 p,
--   simp at this,
--   have := (this.differentiable_on rfl.le).mono hs,
--   convert (is_open_set_of_mem_nhds_and_is_max_on_norm this).mem_nhds _,
--   { ext x,
--     simp,
--   },
-- end

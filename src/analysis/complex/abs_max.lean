import analysis.complex.cauchy_integral
import analysis.convex.integral

/-!
-/

open topological_space metric set filter asymptotics function measure_theory
open_locale topological_space filter nnreal real

universe u
variables {E : Type u} [normed_group E] [normed_space ℂ E] [measurable_space E] [borel_space E]
  [second_countable_topology E] [complete_space E]

namespace complex


/-- If `f` is complex differentiable on a closed disc with center `c` and radius `R > 0`, then
`f' c` can be represented as an integral over the corresponding circle.

TODO: add a version for `w ∈ metric.ball c R`.

TODO: add a version for higher derivatives. -/
lemma deriv_eq_smul_circle_integral {R : ℝ} {c : ℂ} {f : ℂ → E} (hR : 0 < R)
  (hc : continuous_on f (closed_ball c R)) (hd : differentiable_on ℂ f (ball c R)) :
  deriv f c = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-2 : ℤ) • f z :=
begin
  lift R to ℝ≥0 using hR.le,
  refine (has_fpower_series_on_ball_of_continuous_on_of_differentiable_on
    hc hd hR).has_fpower_series_at.deriv.trans _,
  simp only [cauchy_power_series_apply, one_div, zpow_neg₀, pow_one, smul_smul,
    zpow_two, mul_inv₀]
end

/-- If `f` is continuous on a closed disc of radius `R`, is complex differentiable on its interior,
and its values on the boundary circle of this disc are bounded from above by `C`, then the norm of
its derivative at the center is at most `C / R`. -/
lemma norm_deriv_le_of_forall_mem_sphere_norm_le {c : ℂ} {R C : ℝ} {f : ℂ → E} (hR : 0 < R)
  (hc : continuous_on f (closed_ball c R)) (hd : differentiable_on ℂ f (ball c R))
  (hC : ∀ z ∈ sphere c R, ∥f z∥ ≤ C) :
  ∥deriv f c∥ ≤ C / R :=
have ∀ z ∈ sphere c R, ∥(z - c) ^ (-2 : ℤ) • f z∥ ≤ C / (R * R),
  from λ z (hz : abs (z - c) = R), by simpa [norm_smul, hz, zpow_two, ← div_eq_inv_mul]
    using (div_le_div_right (mul_pos hR hR)).2 (hC z hz),
calc ∥deriv f c∥ = ∥(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-2 : ℤ) • f z∥ :
  congr_arg norm (deriv_eq_smul_circle_integral hR hc hd)
... ≤ R * (C / (R * R)) :
  circle_integral.norm_two_pi_I_inv_smul_integral_le_of_norm_le_const hR.le this
... = C / R : by rw [mul_div_comm, div_self_mul_self', div_eq_mul_inv]

/-- A complex differentiable bounded function is a constant. -/
lemma apply_eq_apply_of_differentiable_of_bounded {f : ℂ → E} (hf : differentiable ℂ f)
  (hb : bounded (range f)) (z w : ℂ) : f z = f w :=
begin
  suffices : ∀ c, deriv f c = 0, from is_const_of_deriv_eq_zero hf this z w,
  clear z w, intro c,
  obtain ⟨C, C₀, hC⟩ : ∃ C > (0 : ℝ), ∀ z, ∥f z∥ ≤ C,
  { rcases bounded_iff_forall_norm_le.1 hb with ⟨C, hC⟩,
    exact ⟨max C 1, lt_max_iff.2 (or.inr zero_lt_one),
      λ z, (hC (f z) (mem_range_self _)).trans (le_max_left _ _)⟩ },
  refine norm_le_zero_iff.1 (le_of_forall_le_of_dense $ λ ε ε₀, _),
  calc ∥deriv f c∥ ≤ C / (C / ε) :
    norm_deriv_le_of_forall_mem_sphere_norm_le (div_pos C₀ ε₀) hf.continuous.continuous_on
      hf.differentiable_on (λ z _, hC z)
  ... = ε : div_div_cancel' C₀.lt.ne'
end

/-- A complex differentiable bounded function is a constant. -/
lemma exists_const_forall_eq_of_differentiable_of_bounded {f : ℂ → E} (hf : differentiable ℂ f)
  (hb : bounded (range f)) : ∃ c, ∀ z, f z = c :=
⟨f 0, λ z, apply_eq_apply_of_differentiable_of_bounded hf hb _ _⟩

/-- A complex differentiable bounded function is a constant. -/
lemma exists_eq_const_of_differentiable_of_bounded {f : ℂ → E} (hf : differentiable ℂ f)
  (hb : bounded (range f)) : ∃ c, f = const ℂ c :=
(exists_const_forall_eq_of_differentiable_of_bounded hf hb).imp $ λ c, funext

lemma norm_eq_norm_of_differentiable_on_of_is_max_on_of_closed_ball_subset {f : ℂ → E} {s : set ℂ}
  {z w : ℂ} (hd : differentiable_on ℂ f s) (hz : is_max_on (norm ∘ f) s z)
  (hsub : closed_ball z (dist w z) ⊆ s) :
  ∥f w∥ = ∥f z∥ :=
begin
  set r := dist w z,
  have hw_mem : w ∈ closed_ball z r, from mem_closed_ball.2 le_rfl,
  refine (is_max_on_iff.1 hz _ (hsub hw_mem)).antisymm (not_lt.1 _),
  rintro hw_lt : ∥f w∥ < ∥f z∥,
  have hr : 0 < r, from dist_pos.2 (λ h, hw_lt.ne $ h ▸ rfl),
  have hsub' : sphere z r ⊆ s, from sphere_subset_closed_ball.trans hsub,
  have hne : ∀ ζ ∈ sphere z r, ζ ≠ z,
    from λ ζ hζ, ne_of_mem_of_not_mem hζ (ne_of_lt $ (dist_self z).symm ▸ hr),
  have hcont : continuous_on (λ ζ, (ζ - z)⁻¹ • f ζ) (sphere z r),
    from ((continuous_on_id.sub continuous_on_const).inv₀ $
      λ ζ hζ, sub_ne_zero.2 (hne ζ hζ)).smul (hd.continuous_on.mono hsub'),
  have hle : ∀ ζ ∈ sphere z r, ∥(ζ - z)⁻¹ • f ζ∥ ≤ ∥f z∥ / r,
  { rintros ζ (hζ : abs (ζ - z) = r),
    simpa [norm_smul, hζ, ← div_eq_inv_mul] using (div_le_div_right hr).2 (hz (hsub' hζ)) },
  have hlt : ∥(w - z)⁻¹ • f w∥ < ∥f z∥ / r,
    by simpa [norm_smul, ← div_eq_inv_mul] using (div_lt_div_right hr).2 hw_lt,
  have : ∥∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ∥ < 2 * π * r * (∥f z∥ / r),
    from circle_integral.norm_integral_lt_of_norm_le_const_of_lt hr hcont hle ⟨w, rfl, hlt⟩,
  refine this.ne _,
  rw circle_integral_sub_inv_smul_of_differentiable_on (mem_ball_self hr) (hd.mono hsub),
  field_simp [norm_smul, hr.ne', abs_of_pos real.pi_pos],
  ac_refl
end

lemma norm_eventually_eq_of_eventually_differentiable_at_of_is_local_max {f : ℂ → E} {c : ℂ}
  (hd : ∀ᶠ z in 𝓝 c, differentiable_at ℂ f z) (hc : is_local_max (norm ∘ f) c) :
  ∀ᶠ y in 𝓝 c, ∥f y∥ = ∥f c∥ :=
begin
  rcases nhds_basis_closed_ball.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩,
  exact nhds_basis_closed_ball.eventually_iff.2 ⟨r, hr₀, λ w hw,
    norm_eq_norm_of_differentiable_on_of_is_max_on_of_closed_ball_subset
      (λ z hz, (hr hz).1.differentiable_within_at) (λ z hz, (hr hz).2)
      (closed_ball_subset_closed_ball hw)⟩
end

lemma is_open_set_of_mem_nhds_and_is_max_on_norm {f : ℂ → E} {s : set ℂ}
  (hd : differentiable_on ℂ f s) :
  is_open {z | s ∈ 𝓝 z ∧ is_max_on (norm ∘ f) s z} :=
begin
  refine is_open_iff_mem_nhds.2 (λ z hz, (eventually_eventually_nhds.2 hz.1).and _),
  replace hd : ∀ᶠ w in 𝓝 z, differentiable_at ℂ f w, from hd.eventually_differentiable_at hz.1,
  exact (norm_eventually_eq_of_eventually_differentiable_at_of_is_local_max hd $
    (hz.2.is_local_max hz.1)).mono (λ x hx y hy, le_trans (hz.2 hy) hx.ge)
end

/-- **Maximum modulus principle**: if `f : ℂ → E` is complex differentiable on a nonempty compact
set `s`, then there exists a point `z ∈ frontier s` such that `λ z, ∥f z∥` takes it maximum value on
`s` at `z`. -/
lemma exists_mem_frontier_is_max_on_norm {f : ℂ → E} {s : set ℂ} (hs : is_compact s)
  (hne : s.nonempty) (hd : differentiable_on ℂ f s) :
  ∃ z ∈ frontier s, is_max_on (norm ∘ f) s z :=
begin
  rcases hs.exists_forall_ge hne hd.continuous_on.norm with ⟨w, hws, hle⟩,
  rcases exists_mem_frontier_inf_dist_compl_eq_dist hws hs.ne_univ with ⟨z, hzs, hzw⟩,
  refine ⟨z, hzs, λ x hx, (hle x hx).trans_eq _⟩,
  refine (norm_eq_norm_of_differentiable_on_of_is_max_on_of_closed_ball_subset hd hle _).symm,
  calc closed_ball w (dist z w) ⊆ closed_ball w (inf_dist w sᶜ) :
    closed_ball_subset_closed_ball (by rw [hzw, dist_comm])
  ... ⊆ closure s : closed_ball_inf_dist_compl_subset_closure hws hs.ne_univ
  ... = s : hs.is_closed.closure_eq
end

/-- **Maximum modulus principle**: if `f : ℂ → E` is complex differentiable on a compact set `s` and
`∥f z∥ ≤ C` for any `z ∈ frontier s`, then the same is true for any `z ∈ s`. -/
lemma norm_le_of_forall_mem_frontier_norm_le {f : ℂ → E} {s : set ℂ} (hs : is_compact s)
  (hd : differentiable_on ℂ f s) {C : ℝ} (hC : ∀ z ∈ frontier s, ∥f z∥ ≤ C) {z : ℂ} (hz : z ∈ s) :
  ∥f z∥ ≤ C :=
let ⟨w, hws, hw⟩ := exists_mem_frontier_is_max_on_norm hs ⟨z, hz⟩ hd in le_trans (hw hz) (hC w hws)

lemma eq_of_differentiable_on_of_is_max_on_of_closed_ball_subset {f : ℂ → E} {s : set ℂ}
  {z w : ℂ} (hd : differentiable_on ℂ f s) (hz : is_max_on (norm ∘ f) s z)
  (hsub : closed_ball z (dist w z) ⊆ s) (h_conv : ∀ R, strict_convex ℝ (closed_ball (0 : E) R)) :
  f w = f z :=
begin
  by_contra' H : f w ≠ f z,
  set r := dist w z,
  have hw_mem : w ∈ closed_ball z r, from mem_closed_ball.2 le_rfl,
  have hr : 0 < r, from dist_pos.2 (ne_of_apply_ne _ H),
  have hsub' : sphere z r ⊆ s, from sphere_subset_closed_ball.trans hsub,
  have hle : ∀ᵐ θ : ℝ ∂(measure.restrict volume (Ioc (0 : ℝ) (2 * π))),
    ∥deriv (circle_map z r) θ • f (circle_map z r θ)∥ ≤ r * ∥f z∥,
  { refine eventually_of_forall (λ θ, _),
    simp only [norm_smul, norm_deriv_circle_map, abs_of_pos hr, mul_le_mul_left hr],
    exact hz (hsub' $ circle_map_mem_sphere _ hr.le _) },
  cases (h_conv _).ae_eq_const_or_norm_integral_lt_of_norm_le_const hle with H H,
  {  },
  
  have hne : ∀ ζ ∈ sphere z r, ζ ≠ z,
    from λ ζ hζ, ne_of_mem_of_not_mem hζ (ne_of_lt $ (dist_self z).symm ▸ hr),
  have hcont : continuous_on (λ ζ, (ζ - z)⁻¹ • f ζ) (sphere z r),
    from ((continuous_on_id.sub continuous_on_const).inv₀ $
      λ ζ hζ, sub_ne_zero.2 (hne ζ hζ)).smul (hd.continuous_on.mono hsub'),
  have hle : ∀ ζ ∈ sphere z r, ∥(ζ - z)⁻¹ • f ζ∥ ≤ ∥f z∥ / r,
  { rintros ζ (hζ : abs (ζ - z) = r),
    simpa [norm_smul, hζ, ← div_eq_inv_mul] using (div_le_div_right hr).2 (hz (hsub' hζ)) },
  have hlt : ∥(w - z)⁻¹ • f w∥ < ∥f z∥ / r,
    by simpa [norm_smul, ← div_eq_inv_mul] using (div_lt_div_right hr).2 hw_lt,
  have : ∥∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ∥ < 2 * π * r * (∥f z∥ / r),
    from circle_integral.norm_integral_lt_of_norm_le_const_of_lt hr hcont hle ⟨w, rfl, hlt⟩,
  refine this.ne _,
  rw circle_integral_sub_inv_smul_of_differentiable_on (mem_ball_self hr) (hd.mono hsub),
  field_simp [norm_smul, hr.ne', abs_of_pos real.pi_pos],
  ac_refl
end

end complex

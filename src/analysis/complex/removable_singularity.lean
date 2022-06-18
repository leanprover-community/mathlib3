/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.calculus.fderiv_analytic
import analysis.asymptotics.specific_asymptotics
import analysis.complex.cauchy_integral

/-!
# Removable singularity theorem

In this file we prove Riemann's removable singularity theorem: if `f : ℂ → E` is complex
differentiable in a punctured neighborhood of a point `c` and is bounded in a punctured neighborhood
of `c` (or, more generally, $f(z) - f(c)=o((z-c)^{-1})$), then it has a limit at `c` and the
function `function.update f c (lim (𝓝[≠] c) f)` is complex differentiable in a neighborhood of `c`.
-/

open topological_space metric set filter asymptotics function
open_locale topological_space filter nnreal

universe u
variables {E : Type u} [normed_group E] [normed_space ℂ E] [complete_space E]

namespace complex

/-- **Removable singularity** theorem, weak version. If `f : ℂ → E` is differentiable in a punctured
neighborhood of a point and is continuous at this point, then it is analytic at this point. -/
lemma analytic_at_of_differentiable_on_punctured_nhds_of_continuous_at {f : ℂ → E} {c : ℂ}
  (hd : ∀ᶠ z in 𝓝[≠] c, differentiable_at ℂ f z) (hc : continuous_at f c) :
  analytic_at ℂ f c :=
begin
  rcases (nhds_within_has_basis nhds_basis_closed_ball _).mem_iff.1 hd with ⟨R, hR0, hRs⟩,
  lift R to ℝ≥0 using hR0.le,
  replace hc : continuous_on f (closed_ball c R),
  { refine λ z hz, continuous_at.continuous_within_at _,
    rcases eq_or_ne z c with rfl | hne,
    exacts [hc, (hRs ⟨hz, hne⟩).continuous_at] },
  exact (has_fpower_series_on_ball_of_differentiable_off_countable (countable_singleton c) hc
    (λ z hz, hRs (diff_subset_diff_left ball_subset_closed_ball hz)) hR0).analytic_at
end

lemma differentiable_on_compl_singleton_and_continuous_at_iff {f : ℂ → E} {s : set ℂ} {c : ℂ}
  (hs : s ∈ 𝓝 c) : differentiable_on ℂ f (s \ {c}) ∧ continuous_at f c ↔ differentiable_on ℂ f s :=
begin
  refine ⟨_, λ hd, ⟨hd.mono (diff_subset _ _), (hd.differentiable_at hs).continuous_at⟩⟩,
  rintro ⟨hd, hc⟩ x hx,
  rcases eq_or_ne x c with rfl | hne,
  { refine (analytic_at_of_differentiable_on_punctured_nhds_of_continuous_at _ hc)
      .differentiable_at.differentiable_within_at,
    refine eventually_nhds_within_iff.2 ((eventually_mem_nhds.2 hs).mono $ λ z hz hzx, _),
    exact hd.differentiable_at (inter_mem hz (is_open_ne.mem_nhds hzx)) },
  { simpa only [differentiable_within_at, has_fderiv_within_at, hne.nhds_within_diff_singleton]
      using hd x ⟨hx, hne⟩ }
end

lemma differentiable_on_dslope {f : ℂ → E} {s : set ℂ} {c : ℂ} (hc : s ∈ 𝓝 c) :
  differentiable_on ℂ (dslope f c) s ↔ differentiable_on ℂ f s :=
⟨λ h, h.of_dslope, λ h, (differentiable_on_compl_singleton_and_continuous_at_iff hc).mp $
  ⟨iff.mpr (differentiable_on_dslope_of_nmem $ λ h, h.2 rfl) (h.mono $ diff_subset _ _),
    continuous_at_dslope_same.2 $ h.differentiable_at hc⟩⟩

/-- **Removable singularity** theorem: if `s` is a neighborhood of `c : ℂ`, a function `f : ℂ → E`
is complex differentiable on `s \ {c}`, and $f(z) - f(c)=o((z-c)^{-1})$, then `f` redefined to be
equal to `lim (𝓝[≠] c) f` at `c` is complex differentiable on `s`. -/
lemma differentiable_on_update_lim_of_is_o {f : ℂ → E} {s : set ℂ} {c : ℂ}
  (hc : s ∈ 𝓝 c) (hd : differentiable_on ℂ f (s \ {c}))
  (ho : (λ z, f z - f c) =o[𝓝[≠] c] (λ z, (z - c)⁻¹)) :
  differentiable_on ℂ (update f c (lim (𝓝[≠] c) f)) s :=
begin
  set F : ℂ → E := λ z, (z - c) • f z with hF,
  suffices : differentiable_on ℂ F (s \ {c}) ∧ continuous_at F c,
  { rw [differentiable_on_compl_singleton_and_continuous_at_iff hc, ← differentiable_on_dslope hc,
      dslope_sub_smul] at this; try { apply_instance },
    have hc : tendsto f (𝓝[≠] c) (𝓝 (deriv F c)),
      from continuous_at_update_same.mp (this.continuous_on.continuous_at hc),
    rwa hc.lim_eq },
  refine ⟨(differentiable_on_id.sub_const _).smul hd, _⟩,
  rw ← continuous_within_at_compl_self,
  have H := ho.tendsto_inv_smul_nhds_zero,
  have H' : tendsto (λ z, (z - c) • f c) (𝓝[≠] c) (𝓝 (F c)),
    from (continuous_within_at_id.tendsto.sub tendsto_const_nhds).smul tendsto_const_nhds,
  simpa [← smul_add, continuous_within_at] using H.add H'
end

/-- **Removable singularity** theorem: if `s` is a punctured neighborhood of `c : ℂ`, a function
`f : ℂ → E` is complex differentiable on `s`, and $f(z) - f(c)=o((z-c)^{-1})$, then `f` redefined to
be equal to `lim (𝓝[≠] c) f` at `c` is complex differentiable on `{c} ∪ s`. -/
lemma differentiable_on_update_lim_insert_of_is_o {f : ℂ → E} {s : set ℂ} {c : ℂ}
  (hc : s ∈ 𝓝[≠] c) (hd : differentiable_on ℂ f s)
  (ho : (λ z, f z - f c) =o[𝓝[≠] c] (λ z, (z - c)⁻¹)) :
  differentiable_on ℂ (update f c (lim (𝓝[≠] c) f)) (insert c s) :=
differentiable_on_update_lim_of_is_o (insert_mem_nhds_iff.2 hc)
  (hd.mono $ λ z hz, hz.1.resolve_left hz.2) ho

/-- **Removable singularity** theorem: if `s` is a neighborhood of `c : ℂ`, a function `f : ℂ → E`
is complex differentiable and is bounded on `s \ {c}`, then `f` redefined to be equal to
`lim (𝓝[≠] c) f` at `c` is complex differentiable on `s`. -/
lemma differentiable_on_update_lim_of_bdd_above {f : ℂ → E} {s : set ℂ} {c : ℂ}
  (hc : s ∈ 𝓝 c) (hd : differentiable_on ℂ f (s \ {c}))
  (hb : bdd_above (norm ∘ f '' (s \ {c}))) :
  differentiable_on ℂ (update f c (lim (𝓝[≠] c) f)) s :=
differentiable_on_update_lim_of_is_o hc hd $ is_bounded_under.is_o_sub_self_inv $
  let ⟨C, hC⟩ := hb in ⟨C + ∥f c∥, eventually_map.2 $ mem_nhds_within_iff_exists_mem_nhds_inter.2
    ⟨s, hc, λ z hz, norm_sub_le_of_le (hC $ mem_image_of_mem _ hz) le_rfl⟩⟩

/-- **Removable singularity** theorem: if a function `f : ℂ → E` is complex differentiable on a
punctured neighborhood of `c` and $f(z) - f(c)=o((z-c)^{-1})$, then `f` has a limit at `c`. -/
lemma tendsto_lim_of_differentiable_on_punctured_nhds_of_is_o {f : ℂ → E} {c : ℂ}
  (hd : ∀ᶠ z in 𝓝[≠] c, differentiable_at ℂ f z)
  (ho : (λ z, f z - f c) =o[𝓝[≠] c] (λ z, (z - c)⁻¹)) :
  tendsto f (𝓝[≠] c) (𝓝 $ lim (𝓝[≠] c) f) :=
begin
  rw eventually_nhds_within_iff at hd,
  have : differentiable_on ℂ f ({z | z ≠ c → differentiable_at ℂ f z} \ {c}),
    from λ z hz, (hz.1 hz.2).differentiable_within_at,
  have H := differentiable_on_update_lim_of_is_o hd this ho,
  exact continuous_at_update_same.1 (H.differentiable_at hd).continuous_at
end

/-- **Removable singularity** theorem: if a function `f : ℂ → E` is complex differentiable and
bounded on a punctured neighborhood of `c`, then `f` has a limit at `c`. -/
lemma tendsto_lim_of_differentiable_on_punctured_nhds_of_bounded_under {f : ℂ → E}
  {c : ℂ} (hd : ∀ᶠ z in 𝓝[≠] c, differentiable_at ℂ f z)
  (hb : is_bounded_under (≤) (𝓝[≠] c) (λ z, ∥f z - f c∥)) :
  tendsto f (𝓝[≠] c) (𝓝 $ lim (𝓝[≠] c) f) :=
tendsto_lim_of_differentiable_on_punctured_nhds_of_is_o hd hb.is_o_sub_self_inv

end complex

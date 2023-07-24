/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.convex.function
import analysis.convex.strict_convex_space
import measure_theory.function.ae_eq_of_integral
import measure_theory.integral.average

/-!
# Jensen's inequality for integrals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove several forms of Jensen's inequality for integrals.

- for convex sets: `convex.average_mem`, `convex.set_average_mem`, `convex.integral_mem`;

- for convex functions: `convex.on.average_mem_epigraph`, `convex_on.map_average_le`,
  `convex_on.set_average_mem_epigraph`, `convex_on.map_set_average_le`, `convex_on.map_integral_le`;

- for strictly convex sets: `strict_convex.ae_eq_const_or_average_mem_interior`;

- for a closed ball in a strictly convex normed space:
  `ae_eq_const_or_norm_integral_lt_of_norm_le_const`;

- for strictly convex functions: `strict_convex_on.ae_eq_const_or_map_average_lt`.

## TODO

- Use a typeclass for strict convexity of a closed ball.

## Tags

convex, integral, center mass, average value, Jensen's inequality
-/

open measure_theory measure_theory.measure metric set filter topological_space function
open_locale topology big_operators ennreal convex

variables {α E F : Type*} {m0 : measurable_space α}
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]
  {μ : measure α} {s : set E} {t : set α} {f : α → E} {g : E → ℝ} {C : ℝ}

/-!
### Non-strict Jensen's inequality
-/

/-- If `μ` is a probability measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the expected value of `f` belongs to `s`:
`∫ x, f x ∂μ ∈ s`. See also `convex.sum_mem` for a finite sum version of this lemma. -/
lemma convex.integral_mem [is_probability_measure μ] (hs : convex ℝ s) (hsc : is_closed s)
  (hf : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ) :
  ∫ x, f x ∂μ ∈ s :=
begin
  borelize E,
  rcases hfi.ae_strongly_measurable with ⟨g, hgm, hfg⟩,
  haveI : separable_space (range g ∩ s : set E) :=
    (hgm.is_separable_range.mono (inter_subset_left _ _)).separable_space,
  obtain ⟨y₀, h₀⟩ : (range g ∩ s).nonempty,
  { rcases (hf.and hfg).exists with ⟨x₀, h₀⟩,
    exact ⟨f x₀, by simp only [h₀.2, mem_range_self], h₀.1⟩ },
  rw [integral_congr_ae hfg], rw [integrable_congr hfg] at hfi,
  have hg : ∀ᵐ x ∂μ, g x ∈ closure (range g ∩ s),
  { filter_upwards [hfg.rw (λ x y, y ∈ s) hf] with x hx,
    apply subset_closure,
    exact ⟨mem_range_self _, hx⟩ },
  set G : ℕ → simple_func α E := simple_func.approx_on _ hgm.measurable (range g ∩ s) y₀ h₀,
  have : tendsto (λ n, (G n).integral μ) at_top (𝓝 $ ∫ x, g x ∂μ),
    from tendsto_integral_approx_on_of_measurable hfi _ hg _ (integrable_const _),
  refine hsc.mem_of_tendsto this (eventually_of_forall $ λ n, hs.sum_mem _ _ _),
  { exact λ _ _, ennreal.to_real_nonneg },
  { rw [← ennreal.to_real_sum, (G n).sum_range_measure_preimage_singleton, measure_univ,
      ennreal.one_to_real],
    exact λ _ _, measure_ne_top _ _ },
  { simp only [simple_func.mem_range, forall_range_iff],
    assume x,
    apply inter_subset_right (range g),
    exact simple_func.approx_on_mem hgm.measurable _ _ _ },
end

/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `s`:
`⨍ x, f x ∂μ ∈ s`. See also `convex.center_mass_mem` for a finite sum version of this lemma. -/
lemma convex.average_mem [is_finite_measure μ] (hs : convex ℝ s) (hsc : is_closed s) (hμ : μ ≠ 0)
  (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ) :
  ⨍ x, f x ∂μ ∈ s :=
begin
  haveI : is_probability_measure ((μ univ)⁻¹ • μ),
    from is_probability_measure_smul hμ,
  refine hs.integral_mem hsc (ae_mono' _ hfs) hfi.to_average,
  exact absolutely_continuous.smul (refl _) _
end

/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `s`:
`⨍ x, f x ∂μ ∈ s`. See also `convex.center_mass_mem` for a finite sum version of this lemma. -/
lemma convex.set_average_mem (hs : convex ℝ s) (hsc : is_closed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞)
  (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) (hfi : integrable_on f t μ) :
  ⨍ x in t, f x ∂μ ∈ s :=
begin
  haveI : fact (μ t < ∞) := ⟨ht.lt_top⟩,
  refine hs.average_mem hsc _ hfs hfi,
  rwa [ne.def, restrict_eq_zero]
end

/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex set in `E`, and `f` is an integrable
function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `closure s`:
`⨍ x, f x ∂μ ∈ s`. See also `convex.center_mass_mem` for a finite sum version of this lemma. -/
lemma convex.set_average_mem_closure (hs : convex ℝ s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞)
  (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) (hfi : integrable_on f t μ) :
  ⨍ x in t, f x ∂μ ∈ closure s :=
hs.closure.set_average_mem is_closed_closure h0 ht (hfs.mono $ λ x hx, subset_closure hx) hfi

lemma convex_on.average_mem_epigraph [is_finite_measure μ] (hg : convex_on ℝ s g)
  (hgc : continuous_on g s) (hsc : is_closed s) (hμ : μ ≠ 0) (hfs : ∀ᵐ x ∂μ, f x ∈ s)
  (hfi : integrable f μ) (hgi : integrable (g ∘ f) μ) :
  (⨍ x, f x ∂μ, ⨍ x, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} :=
have ht_mem : ∀ᵐ x ∂μ, (f x, g (f x)) ∈ {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2},
  from hfs.mono (λ x hx, ⟨hx, le_rfl⟩),
by simpa only [average_pair hfi hgi]
  using hg.convex_epigraph.average_mem (hsc.epigraph hgc) hμ ht_mem (hfi.prod_mk hgi)

lemma concave_on.average_mem_hypograph [is_finite_measure μ] (hg : concave_on ℝ s g)
  (hgc : continuous_on g s) (hsc : is_closed s) (hμ : μ ≠ 0) (hfs : ∀ᵐ x ∂μ, f x ∈ s)
  (hfi : integrable f μ) (hgi : integrable (g ∘ f) μ) :
  (⨍ x, f x ∂μ, ⨍ x, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ p.2 ≤ g p.1} :=
by simpa only [mem_set_of_eq, pi.neg_apply, average_neg, neg_le_neg_iff]
  using hg.neg.average_mem_epigraph hgc.neg hsc hμ hfs hfi hgi.neg

/-- **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points to `s`, then the value of `g` at the average value of `f` is less than or equal to
the average value of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also
`convex_on.map_center_mass_le` for a finite sum version of this lemma. -/
lemma convex_on.map_average_le [is_finite_measure μ] (hg : convex_on ℝ s g)
  (hgc : continuous_on g s) (hsc : is_closed s) (hμ : μ ≠ 0) (hfs : ∀ᵐ x ∂μ, f x ∈ s)
  (hfi : integrable f μ) (hgi : integrable (g ∘ f) μ) :
  g (⨍ x, f x ∂μ) ≤ ⨍ x, g (f x) ∂μ :=
(hg.average_mem_epigraph hgc hsc hμ hfs hfi hgi).2

/-- **Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points to `s`, then the average value of `g ∘ f` is less than or equal to the value of `g`
at the average value of `f` provided that both `f` and `g ∘ f` are integrable. See also
`concave_on.le_map_center_mass` for a finite sum version of this lemma. -/
lemma concave_on.le_map_average [is_finite_measure μ] (hg : concave_on ℝ s g)
  (hgc : continuous_on g s) (hsc : is_closed s) (hμ : μ ≠ 0) (hfs : ∀ᵐ x ∂μ, f x ∈ s)
  (hfi : integrable f μ) (hgi : integrable (g ∘ f) μ) :
  ⨍ x, g (f x) ∂μ ≤ g (⨍ x, f x ∂μ) :=
(hg.average_mem_hypograph hgc hsc hμ hfs hfi hgi).2

/-- **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points of a set `t` to `s`, then the value of `g` at the average value of `f` over `t` is
less than or equal to the average value of `g ∘ f` over `t` provided that both `f` and `g ∘ f` are
integrable. -/
lemma convex_on.set_average_mem_epigraph (hg : convex_on ℝ s g) (hgc : continuous_on g s)
  (hsc : is_closed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
  (hfi : integrable_on f t μ) (hgi : integrable_on (g ∘ f) t μ) :
  (⨍ x in t, f x ∂μ, ⨍ x in t, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} :=
begin
  haveI : fact (μ t < ∞) := ⟨ht.lt_top⟩,
  refine hg.average_mem_epigraph hgc hsc _ hfs hfi hgi,
  rwa [ne.def, restrict_eq_zero]
end

/-- **Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points of a set `t` to `s`, then the average value of `g ∘ f` over `t` is less than or
equal to the value of `g` at the average value of `f` over `t` provided that both `f` and `g ∘ f`
are integrable. -/
lemma concave_on.set_average_mem_hypograph (hg : concave_on ℝ s g) (hgc : continuous_on g s)
  (hsc : is_closed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
  (hfi : integrable_on f t μ) (hgi : integrable_on (g ∘ f) t μ) :
  (⨍ x in t, f x ∂μ, ⨍ x in t, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ p.2 ≤ g p.1} :=
by simpa only [mem_set_of_eq, pi.neg_apply, average_neg, neg_le_neg_iff]
  using hg.neg.set_average_mem_epigraph hgc.neg hsc h0 ht hfs hfi hgi.neg

/-- **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points of a set `t` to `s`, then the value of `g` at the average value of `f` over `t` is
less than or equal to the average value of `g ∘ f` over `t` provided that both `f` and `g ∘ f` are
integrable. -/
lemma convex_on.map_set_average_le (hg : convex_on ℝ s g) (hgc : continuous_on g s)
  (hsc : is_closed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
  (hfi : integrable_on f t μ) (hgi : integrable_on (g ∘ f) t μ) :
  g (⨍ x in t, f x ∂μ) ≤ ⨍ x in t, g (f x) ∂μ :=
(hg.set_average_mem_epigraph hgc hsc h0 ht hfs hfi hgi).2

/-- **Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points of a set `t` to `s`, then the average value of `g ∘ f` over `t` is less than or
equal to the value of `g` at the average value of `f` over `t` provided that both `f` and `g ∘ f`
are integrable. -/
lemma concave_on.le_map_set_average (hg : concave_on ℝ s g) (hgc : continuous_on g s)
  (hsc : is_closed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
  (hfi : integrable_on f t μ) (hgi : integrable_on (g ∘ f) t μ) :
  ⨍ x in t, g (f x) ∂μ ≤ g (⨍ x in t, f x ∂μ) :=
(hg.set_average_mem_hypograph hgc hsc h0 ht hfs hfi hgi).2

/-- **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex closed
set `s`, `μ` is a probability measure on `α`, and `f : α → E` is a function sending `μ`-a.e.  points
to `s`, then the value of `g` at the expected value of `f` is less than or equal to the expected
value of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also
`convex_on.map_center_mass_le` for a finite sum version of this lemma. -/
lemma convex_on.map_integral_le [is_probability_measure μ] (hg : convex_on ℝ s g)
  (hgc : continuous_on g s) (hsc : is_closed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ)
  (hgi : integrable (g ∘ f) μ) :
  g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ :=
by simpa only [average_eq_integral]
  using hg.map_average_le hgc hsc (is_probability_measure.ne_zero μ) hfs hfi hgi

/-- **Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on a convex closed
set `s`, `μ` is a probability measure on `α`, and `f : α → E` is a function sending `μ`-a.e.  points
to `s`, then the expected value of `g ∘ f` is less than or equal to the value of `g` at the expected
value of `f` provided that both `f` and `g ∘ f` are integrable. -/
lemma concave_on.le_map_integral [is_probability_measure μ] (hg : concave_on ℝ s g)
  (hgc : continuous_on g s) (hsc : is_closed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ)
  (hgi : integrable (g ∘ f) μ) :
  ∫ x, g (f x) ∂μ ≤ g (∫ x, f x ∂μ) :=
by simpa only [average_eq_integral]
  using hg.le_map_average hgc hsc (is_probability_measure.ne_zero μ) hfs hfi hgi

/-!
### Strict Jensen's inequality
-/

/-- If `f : α → E` is an integrable function, then either it is a.e. equal to the constant
`⨍ x, f x ∂μ` or there exists a measurable set such that `μ t ≠ 0`, `μ tᶜ ≠ 0`, and the average
values of `f` over `t` and `tᶜ` are different. -/
lemma ae_eq_const_or_exists_average_ne_compl [is_finite_measure μ] (hfi : integrable f μ) :
  (f =ᵐ[μ] const α (⨍ x, f x ∂μ)) ∨ ∃ t, measurable_set t ∧ μ t ≠ 0 ∧ μ tᶜ ≠ 0 ∧
    ⨍ x in t, f x ∂μ ≠ ⨍ x in tᶜ, f x ∂μ :=
begin
  refine or_iff_not_imp_right.mpr (λ H, _), push_neg at H,
  refine hfi.ae_eq_of_forall_set_integral_eq _ _ (integrable_const _) (λ t ht ht', _), clear ht',
  simp only [const_apply, set_integral_const],
  by_cases h₀ : μ t = 0,
  { rw [restrict_eq_zero.2 h₀, integral_zero_measure, h₀, ennreal.zero_to_real, zero_smul] },
  by_cases h₀' : μ tᶜ = 0,
  { rw ← ae_eq_univ at h₀',
    rw [restrict_congr_set h₀', restrict_univ, measure_congr h₀', measure_smul_average] },
  have := average_mem_open_segment_compl_self ht.null_measurable_set h₀ h₀' hfi,
  rw [← H t ht h₀ h₀', open_segment_same, mem_singleton_iff] at this,
  rw [this, measure_smul_set_average _ (measure_ne_top μ _)]
end

/-- If an integrable function `f : α → E` takes values in a convex set `s` and for some set `t` of
positive measure, the average value of `f` over `t` belongs to the interior of `s`, then the average
of `f` over the whole space belongs to the interior of `s`. -/
lemma convex.average_mem_interior_of_set [is_finite_measure μ] (hs : convex ℝ s) (h0 : μ t ≠ 0)
  (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ) (ht : ⨍ x in t, f x ∂μ ∈ interior s) :
  ⨍ x, f x ∂μ ∈ interior s :=
begin
  rw ← measure_to_measurable at h0, rw ← restrict_to_measurable (measure_ne_top μ t) at ht,
  by_cases h0' : μ (to_measurable μ t)ᶜ = 0,
  { rw ← ae_eq_univ at h0',
    rwa [restrict_congr_set h0', restrict_univ] at ht },
  exact hs.open_segment_interior_closure_subset_interior ht
    (hs.set_average_mem_closure h0' (measure_ne_top _ _) (ae_restrict_of_ae hfs) hfi.integrable_on)
    (average_mem_open_segment_compl_self (measurable_set_to_measurable μ t).null_measurable_set
      h0 h0' hfi)
end

/-- If an integrable function `f : α → E` takes values in a strictly convex closed set `s`, then
either it is a.e. equal to its average value, or its average value belongs to the interior of
`s`. -/
lemma strict_convex.ae_eq_const_or_average_mem_interior [is_finite_measure μ]
  (hs : strict_convex ℝ s) (hsc : is_closed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ) :
  f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ ⨍ x, f x ∂μ ∈ interior s :=
begin
  have : ∀ {t}, μ t ≠ 0 → ⨍ x in t, f x ∂μ ∈ s,
    from λ t ht, hs.convex.set_average_mem hsc ht (measure_ne_top _ _) (ae_restrict_of_ae hfs)
      hfi.integrable_on,
  refine (ae_eq_const_or_exists_average_ne_compl hfi).imp_right _,
  rintro ⟨t, hm, h₀, h₀', hne⟩,
  exact hs.open_segment_subset (this h₀) (this h₀') hne
    (average_mem_open_segment_compl_self hm.null_measurable_set h₀ h₀' hfi)
end

/-- **Jensen's inequality**, strict version: if an integrable function `f : α → E` takes values in a
convex closed set `s`, and `g : E → ℝ` is continuous and strictly convex on `s`, then
either `f` is a.e. equal to its average value, or `g (⨍ x, f x ∂μ) < ⨍ x, g (f x) ∂μ`. -/
lemma strict_convex_on.ae_eq_const_or_map_average_lt [is_finite_measure μ]
  (hg : strict_convex_on ℝ s g) (hgc : continuous_on g s) (hsc : is_closed s)
  (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ) (hgi : integrable (g ∘ f) μ) :
  f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ g (⨍ x, f x ∂μ) < ⨍ x, g (f x) ∂μ :=
begin
  have : ∀ {t}, μ t ≠ 0 → ⨍ x in t, f x ∂μ ∈ s ∧ g (⨍ x in t, f x ∂μ) ≤ ⨍ x in t, g (f x) ∂μ,
    from λ t ht, hg.convex_on.set_average_mem_epigraph hgc hsc ht (measure_ne_top _ _)
      (ae_restrict_of_ae hfs) hfi.integrable_on hgi.integrable_on,
  refine (ae_eq_const_or_exists_average_ne_compl hfi).imp_right _,
  rintro ⟨t, hm, h₀, h₀', hne⟩,
  rcases average_mem_open_segment_compl_self hm.null_measurable_set h₀ h₀' (hfi.prod_mk hgi)
    with ⟨a, b, ha, hb, hab, h_avg⟩,
  simp only [average_pair hfi hgi, average_pair hfi.integrable_on hgi.integrable_on, prod.smul_mk,
    prod.mk_add_mk, prod.mk.inj_iff, (∘)] at h_avg,
  rw [← h_avg.1, ← h_avg.2],
  calc g (a • ⨍ x in t, f x ∂μ + b • ⨍ x in tᶜ, f x ∂μ)
      < a * g (⨍ x in t, f x ∂μ) + b * g (⨍ x in tᶜ, f x ∂μ) :
    hg.2 (this h₀).1 (this h₀').1 hne ha hb hab
  ... ≤ a * ⨍ x in t, g (f x) ∂μ + b * ⨍ x in tᶜ, g (f x) ∂μ :
    add_le_add (mul_le_mul_of_nonneg_left (this h₀).2 ha.le)
      (mul_le_mul_of_nonneg_left (this h₀').2 hb.le)
end

/-- **Jensen's inequality**, strict version: if an integrable function `f : α → E` takes values in a
convex closed set `s`, and `g : E → ℝ` is continuous and strictly concave on `s`, then
either `f` is a.e. equal to its average value, or `⨍ x, g (f x) ∂μ < g (⨍ x, f x ∂μ)`. -/
lemma strict_concave_on.ae_eq_const_or_lt_map_average [is_finite_measure μ]
  (hg : strict_concave_on ℝ s g) (hgc : continuous_on g s) (hsc : is_closed s)
  (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ) (hgi : integrable (g ∘ f) μ) :
  f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ ⨍ x, g (f x) ∂μ < g (⨍ x, f x ∂μ) :=
by simpa only [pi.neg_apply, average_neg, neg_lt_neg_iff]
  using hg.neg.ae_eq_const_or_map_average_lt hgc.neg hsc hfs hfi hgi.neg

/-- If `E` is a strictly convex normed space and `f : α → E` is a function such that `‖f x‖ ≤ C`
a.e., then either this function is a.e. equal to its average value, or the norm of its average value
is strictly less than `C`. -/
lemma ae_eq_const_or_norm_average_lt_of_norm_le_const [strict_convex_space ℝ E]
  (h_le : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
  (f =ᵐ[μ] const α ⨍ x, f x ∂μ) ∨ ‖⨍ x, f x ∂μ‖ < C :=
begin
  cases le_or_lt C 0 with hC0 hC0,
  { have : f =ᵐ[μ] 0, from h_le.mono (λ x hx, norm_le_zero_iff.1 (hx.trans hC0)),
    simp only [average_congr this, pi.zero_apply, average_zero],
    exact or.inl this },
  by_cases hfi : integrable f μ, swap,
    by simp [average_eq, integral_undef hfi, hC0, ennreal.to_real_pos_iff],
  cases (le_top : μ univ ≤ ∞).eq_or_lt with hμt hμt, { simp [average_eq, hμt, hC0] },
  haveI : is_finite_measure μ := ⟨hμt⟩,
  replace h_le : ∀ᵐ x ∂μ, f x ∈ closed_ball (0 : E) C, by simpa only [mem_closed_ball_zero_iff],
  simpa only [interior_closed_ball _ hC0.ne', mem_ball_zero_iff]
    using (strict_convex_closed_ball ℝ (0 : E) C).ae_eq_const_or_average_mem_interior
      is_closed_ball h_le hfi
end

/-- If `E` is a strictly convex normed space and `f : α → E` is a function such that `‖f x‖ ≤ C`
a.e., then either this function is a.e. equal to its average value, or the norm of its integral is
strictly less than `(μ univ).to_real * C`. -/
lemma ae_eq_const_or_norm_integral_lt_of_norm_le_const [strict_convex_space ℝ E]
  [is_finite_measure μ] (h_le : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
  (f =ᵐ[μ] const α ⨍ x, f x ∂μ) ∨ ‖∫ x, f x ∂μ‖ < (μ univ).to_real * C :=
begin
  cases eq_or_ne μ 0 with h₀ h₀, { left, simp [h₀] },
  have hμ : 0 < (μ univ).to_real,
    by simp [ennreal.to_real_pos_iff, pos_iff_ne_zero, h₀, measure_lt_top],
  refine (ae_eq_const_or_norm_average_lt_of_norm_le_const h_le).imp_right (λ H, _),
  rwa [average_eq, norm_smul, norm_inv, real.norm_eq_abs, abs_of_pos hμ,
    ← div_eq_inv_mul, div_lt_iff' hμ] at H
end

/-- If `E` is a strictly convex normed space and `f : α → E` is a function such that `‖f x‖ ≤ C`
a.e. on a set `t` of finite measure, then either this function is a.e. equal to its average value on
`t`, or the norm of its integral over `t` is strictly less than `(μ t).to_real * C`. -/
lemma ae_eq_const_or_norm_set_integral_lt_of_norm_le_const [strict_convex_space ℝ E]
  (ht : μ t ≠ ∞) (h_le : ∀ᵐ x ∂μ.restrict t, ‖f x‖ ≤ C) :
  (f =ᵐ[μ.restrict t] const α ⨍ x in t, f x ∂μ) ∨ ‖∫ x in t, f x ∂μ‖ < (μ t).to_real * C :=
begin
  haveI := fact.mk ht.lt_top,
  rw [← restrict_apply_univ],
  exact ae_eq_const_or_norm_integral_lt_of_norm_le_const h_le
end

/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.basic
import measure_theory.measure.regular

/-!
# McShane integrability vs Bochner integrability

In this file we prove that any Bochner integrable function is McShane integrable (hence, it is
Henstock and `⊥` integrable) with the same integral. The proof is based on
[Russel A. Gordon, *The integrals of Lebesgue, Denjoy, Perron, and Henstock*][Gordon55].

## Tags

integral, McShane integral, Bochner integral
-/

open_locale classical nnreal ennreal topological_space big_operators

universes u

variables {E : Type u} {n : ℕ} [normed_group E] [normed_space ℝ E]

local notation `ℝⁿ` := fin n → ℝ
local notation `ℝ>0` := {x : ℝ // 0 < x}

open measure_theory metric set finset filter box_integral

namespace box_integral

/-- The indicator function of a measurable set is McShane integrable with respect to any
locally-finite measure. -/
lemma has_integral_indicator_const (l : integration_params) (hl : l.bRiemann = ff)
  {s : set ℝⁿ} (hs : measurable_set s) (I : box n) (y : E)
  (μ : measure ℝⁿ) [is_locally_finite_measure μ] :
  has_integral.{u u} I l (s.indicator (λ _, y)) μ.to_box_additive.to_smul
    ((μ (s ∩ I)).to_real • y) :=
begin
  refine has_integral_of_mul (∥y∥) (λ ε ε0, _),
  lift ε to ℝ≥0 using ε0.le, rw nnreal.coe_pos at ε0,
  /- First we choose a closed set `F ⊆ s ∩ I.Icc` and an open set `U ⊇ s` such that
  both `(s ∩ I.Icc) \ F` and `U \ s` have measure less than `ε`. -/
  have A : μ (s ∩ I.Icc) ≠ ∞,
    from ((measure_mono $ set.inter_subset_right _ _).trans_lt (I.measure_Icc_lt_top μ)).ne,
  have B : μ (s ∩ I) ≠ ∞,
    from ((measure_mono $ set.inter_subset_right _ _).trans_lt (I.measure_coe_lt_top μ)).ne,
  obtain ⟨F, hFs, hFc, hμF⟩ : ∃ F ⊆ s ∩ I.Icc, is_closed F ∧ μ ((s ∩ I.Icc) \ F) < ε,
    from (hs.inter I.measurable_set_Icc).exists_is_closed_diff_lt A (ennreal.coe_pos.2 ε0).ne',
  obtain ⟨U, hsU, hUo, hUt, hμU⟩ : ∃ U ⊇ s ∩ I.Icc, is_open U ∧ μ U < ∞ ∧ μ (U \ (s ∩ I.Icc)) < ε,
    from (hs.inter I.measurable_set_Icc).exists_is_open_diff_lt A (ennreal.coe_pos.2 ε0).ne',
  /- Then we choose `r` so that `closed_ball x (r x) ⊆ U` whenever `x ∈ s ∩ I.Icc` and
  `closed_ball x (r x)` is disjoint with `F` otherwise. -/
  have : ∀ x ∈ s ∩ I.Icc, ∃ r : ℝ>0, closed_ball x r ⊆ U,
    from λ x hx, subtype.exists'.1 (nhds_basis_closed_ball.mem_iff.1 (hUo.mem_nhds $ hsU hx)),
  choose! rs hrsU,
  have : ∀ x ∈ I.Icc \ s, ∃ r : ℝ>0, closed_ball x r ⊆ Fᶜ,
    from λ x hx, subtype.exists'.1 (nhds_basis_closed_ball.mem_iff.1 (hFc.is_open_compl.mem_nhds $
      λ hx', hx.2 (hFs hx').1)),
  choose! rs' hrs'F,
  set r : ℝⁿ → ℝ>0 := s.piecewise rs rs',
  refine ⟨λ c, r, λ c, l.r_cond_of_bRiemann_eq_ff hl, λ c π hπ hπp, _⟩, rw mul_comm,
  /- Then the union of boxes `J ∈ π` such that `π.tag ∈ s` includes `F` and is included by `U`,
  hence its measure is `ε`-close to the measure of `s`. -/
  dsimp [integral_sum],
  simp only [mem_closed_ball, dist_eq_norm, ← indicator_const_smul_apply,
    sum_indicator_eq_sum_filter, ← sum_smul, ← sub_smul, norm_smul, real.norm_eq_abs,
    ← prepartition.filter_boxes, ← prepartition.measure_Union_to_real],
  refine mul_le_mul_of_nonneg_right _ (norm_nonneg y),
  set t := (π.to_prepartition.filter (λ J, π.tag J ∈ s)).Union,
  change abs ((μ t).to_real - (μ (s ∩ I)).to_real) ≤ ε,
  have htU : t ⊆ U ∩ I,
  { simp only [t, prepartition.Union_def, Union_subset_iff, prepartition.mem_filter, and_imp],
    refine λ J hJ hJs x hx, ⟨hrsU _ ⟨hJs, π.tag_mem_Icc J⟩  _, π.le_of_mem' J hJ hx⟩,
    simpa only [r, s.piecewise_eq_of_mem _ _ hJs] using hπ.1 J hJ (box.coe_subset_Icc hx) },
  refine abs_sub_le_iff.2 ⟨_, _⟩,
  { refine (ennreal.le_to_real_sub B).trans (ennreal.to_real_le_coe_of_le_coe _),
    refine (tsub_le_tsub (measure_mono htU) le_rfl).trans (le_measure_diff.trans _),
    refine (measure_mono $ λ x hx, _).trans hμU.le,
    exact ⟨hx.1.1, λ hx', hx.2 ⟨hx'.1, hx.1.2⟩⟩ },
  { have hμt : μ t ≠ ∞ :=
      ((measure_mono (htU.trans (inter_subset_left _ _))).trans_lt hUt).ne,
    refine (ennreal.le_to_real_sub hμt).trans (ennreal.to_real_le_coe_of_le_coe _),
    refine le_measure_diff.trans ((measure_mono _).trans hμF.le),
    rintro x ⟨⟨hxs, hxI⟩, hxt⟩,
    refine ⟨⟨hxs, box.coe_subset_Icc hxI⟩, λ hxF, hxt _⟩,
    simp only [t, prepartition.Union_def, prepartition.mem_filter, set.mem_Union, exists_prop],
    rcases hπp x hxI with ⟨J, hJπ, hxJ⟩,
    refine ⟨J, ⟨hJπ, _⟩, hxJ⟩,
    contrapose hxF,
    refine hrs'F _ ⟨π.tag_mem_Icc J, hxF⟩ _,
    simpa only [r, s.piecewise_eq_of_not_mem _ _ hxF] using hπ.1 J hJπ (box.coe_subset_Icc hxJ) }
end

/-- If `f` is a.e. equal to zero on a rectangular box, then it has McShane integral zero on this
box. -/
lemma has_integral_zero_of_ae_eq_zero {l : integration_params} {I : box n} {f : ℝⁿ → E}
  {μ : measure ℝⁿ} [is_locally_finite_measure μ] (hf : f =ᵐ[μ.restrict I] 0)
  (hl : l.bRiemann = ff) :
  has_integral.{u u} I l f μ.to_box_additive.to_smul 0 :=
begin
  /- Each set `{x | n < ∥f x∥ ≤ n + 1}`, `n : ℕ`, has measure zero. We cover it by an open set of
  measure less than `ε / 2 ^ n / (n + 1)`. Then the norm of the integral sum is less than `ε`. -/
  refine has_integral_iff.2 (λ ε ε0, _),
  lift ε to ℝ≥0 using ε0.lt.le, rw [gt_iff_lt, nnreal.coe_pos] at ε0,
  rcases nnreal.exists_pos_sum_of_encodable ε0.ne' ℕ with ⟨δ, δ0, c, hδc, hcε⟩,
  haveI := fact.mk (I.measure_coe_lt_top μ),
  change μ.restrict I {x | f x ≠ 0} = 0 at hf,
  set N : ℝⁿ → ℕ := λ x, ⌈∥f x∥⌉₊,
  have N0 : ∀ {x}, N x = 0 ↔ f x = 0, by { intro x, simp [N] },
  have : ∀ k, ∃ U ⊇ N ⁻¹' {k}, is_open U ∧ μ.restrict I U < δ k / k,
  { refine λ k, (N ⁻¹' {k}).exists_is_open_lt_of_lt _ _,
    cases k,
    { simpa [ennreal.div_zero (ennreal.coe_pos.2 (δ0 _)).ne']
        using measure_lt_top (μ.restrict I) _ },
    { refine (measure_mono_null _ hf).le.trans_lt _,
      { exact λ x hxN hxf, k.succ_ne_zero ((eq.symm hxN).trans $ N0.2 hxf) },
      { simp [(δ0 _).ne'] } } },
  choose U hNU hUo hμU,
  have : ∀ x, ∃ r : ℝ>0, closed_ball x r ⊆ U (N x),
    from λ x, subtype.exists'.1 (nhds_basis_closed_ball.mem_iff.1 ((hUo _).mem_nhds (hNU _ rfl))),
  choose r hrU,
  refine ⟨λ _, r, λ c, l.r_cond_of_bRiemann_eq_ff hl, λ c π hπ hπp, _⟩,
  rw [dist_eq_norm, sub_zero, ← integral_sum_fiberwise (λ J, N (π.tag J))],
  refine le_trans _ (nnreal.coe_lt_coe.2 hcε).le,
  refine (norm_sum_le_of_le _ _).trans
    (sum_le_has_sum _ (λ n _, (δ n).2) (nnreal.has_sum_coe.2 hδc)),
  rintro n -,
  dsimp [integral_sum],
  have : ∀ J ∈ π.filter (λ J, N (π.tag J) = n),
    ∥(μ ↑J).to_real • f (π.tag J)∥ ≤ (μ J).to_real * n,
  { intros J hJ, rw tagged_prepartition.mem_filter at hJ,
    rw [norm_smul, real.norm_eq_abs, abs_of_nonneg ennreal.to_real_nonneg],
    exact mul_le_mul_of_nonneg_left (hJ.2 ▸ nat.le_ceil _) ennreal.to_real_nonneg },
  refine (norm_sum_le_of_le _ this).trans _, clear this,
  rw [← sum_mul, ← prepartition.measure_Union_to_real],
  generalize hm : μ (π.filter (λ J, N (π.tag J) = n)).Union = m,
  have : m < δ n / n,
  { simp only [measure.restrict_apply (hUo _).measurable_set] at hμU,
    refine hm ▸ (measure_mono _).trans_lt (hμU _),
    simp only [set.subset_def, tagged_prepartition.mem_Union, exists_prop,
      tagged_prepartition.mem_filter],
    rintro x ⟨J, ⟨hJ, rfl⟩, hx⟩,
    exact ⟨hrU _ (hπ.1 _ hJ (box.coe_subset_Icc hx)), π.le_of_mem' J hJ hx⟩ },
  lift m to ℝ≥0 using ne_top_of_lt this,
  rw [ennreal.coe_to_real, ← nnreal.coe_nat_cast, ← nnreal.coe_mul, nnreal.coe_le_coe,
    ← ennreal.coe_le_coe, ennreal.coe_mul, ennreal.coe_nat, mul_comm],
  exact (mul_le_mul_left' this.le _).trans ennreal.mul_div_le
end

/-- If `f` has integral `y` on a box `I` with respect to a locally finite measure `μ` and `g` is
a.e. equal to `f` on `I`, then `g` has the same integral on `I`.  -/
lemma has_integral.congr_ae {l : integration_params} {I : box n} {y : E} {f g : ℝⁿ → E}
  {μ : measure ℝⁿ} [is_locally_finite_measure μ]
  (hf : has_integral.{u u} I l f μ.to_box_additive.to_smul y)
  (hfg : f =ᵐ[μ.restrict I] g) (hl : l.bRiemann = ff) :
  has_integral.{u u} I l g μ.to_box_additive.to_smul y :=
begin
  have : (g - f) =ᵐ[μ.restrict I] 0, from hfg.mono (λ x hx, sub_eq_zero.2 hx.symm),
  simpa using hf.add (has_integral_zero_of_ae_eq_zero this hl)
end

end box_integral

namespace measure_theory

namespace simple_func

/-- A simple function is McShane integrable w.r.t. any locally finite measure. -/
lemma has_box_integral (f : simple_func ℝⁿ E) (μ : measure ℝⁿ)
  [is_locally_finite_measure μ] (I : box n) (l : integration_params) (hl : l.bRiemann = ff) :
  has_integral.{u u} I l f μ.to_box_additive.to_smul (f.integral (μ.restrict I)) :=
begin
  induction f using measure_theory.simple_func.induction with y s hs f g hd hfi hgi,
  { simpa [function.const, measure.restrict_apply hs]
      using box_integral.has_integral_indicator_const l hl hs I y μ },
  { borelize E, haveI := fact.mk (I.measure_coe_lt_top μ),
    rw integral_add,
    exacts [hfi.add hgi, integrable_iff.2 $ λ _ _, measure_lt_top _ _,
      integrable_iff.2 $ λ _ _, measure_lt_top _ _] }
end

/-- For a simple function, its McShane (or Henstock, or `⊥`) box integral is equal to its
integral in the sense of `measure_theory.simple_func.integral`. -/
lemma box_integral_eq_integral (f : simple_func ℝⁿ E) (μ : measure ℝⁿ)
  [is_locally_finite_measure μ] (I : box n) (l : integration_params) (hl : l.bRiemann = ff) :
  box_integral.integral.{u u} I l f μ.to_box_additive.to_smul = f.integral (μ.restrict I) :=
(f.has_box_integral μ I l hl).integral_eq

end simple_func

open topological_space

/-- If `f : ℝⁿ → E` is Bochner integrable w.r.t. a locally finite measure `μ` on a rectangular box
`I`, then it is McShane integrable on `I` with the same integral.  -/
lemma integrable_on.has_box_integral [complete_space E] {f : ℝⁿ → E} {μ : measure ℝⁿ}
  [is_locally_finite_measure μ] {I : box n} (hf : integrable_on f I μ) (l : integration_params)
  (hl : l.bRiemann = ff) :
  has_integral.{u u} I l f μ.to_box_additive.to_smul (∫ x in I, f x ∂ μ) :=
begin
  borelize E,
  /- First we replace an `ae_strongly_measurable` function by a measurable one. -/
  rcases hf.ae_strongly_measurable with ⟨g, hg, hfg⟩,
  haveI : separable_space (range g ∪ {0} : set E) := hg.separable_space_range_union_singleton,
  rw integral_congr_ae hfg, have hgi : integrable_on g I μ := (integrable_congr hfg).1 hf,
  refine box_integral.has_integral.congr_ae _ hfg.symm hl,
  clear_dependent f,
  /- Now consider the sequence of simple functions
  `simple_func.approx_on g hg.measurable (range g ∪ {0}) 0 (by simp)`
  approximating `g`. Recall some properties of this sequence. -/
  set f : ℕ → simple_func ℝⁿ E :=
    simple_func.approx_on g hg.measurable (range g ∪ {0}) 0 (by simp),
  have hfi : ∀ n, integrable_on (f n) I μ,
    from simple_func.integrable_approx_on_range hg.measurable hgi,
  have hfi' := λ n, ((f n).has_box_integral μ I l hl).integrable,
  have hfgi : tendsto (λ n, (f n).integral (μ.restrict I)) at_top (𝓝 $ ∫ x in I, g x ∂μ),
    from tendsto_integral_approx_on_of_measurable_of_range_subset hg.measurable hgi _ subset.rfl,
  have hfg_mono : ∀ x {m n}, m ≤ n → ∥f n x - g x∥ ≤ ∥f m x - g x∥,
  { intros x m n hmn,
    rw [← dist_eq_norm, ← dist_eq_norm, dist_nndist, dist_nndist, nnreal.coe_le_coe,
      ← ennreal.coe_le_coe, ← edist_nndist, ← edist_nndist],
    exact simple_func.edist_approx_on_mono hg.measurable _ x hmn },
  /- Now consider `ε > 0`. We need to find `r` such that for any tagged partition subordinate
  to `r`, the integral sum is `(μ I + 1 + 1) * ε`-close to the Bochner integral. -/
  refine has_integral_of_mul ((μ I).to_real + 1 + 1) (λ ε ε0, _),
  lift ε to ℝ≥0 using ε0.le, rw nnreal.coe_pos at ε0, have ε0' := ennreal.coe_pos.2 ε0,
  /- Choose `N` such that the integral of `∥f N x - g x∥` is less than or equal to `ε`. -/
  obtain ⟨N₀, hN₀⟩ : ∃ N : ℕ, ∫ x in I, ∥f N x - g x∥ ∂μ ≤ ε,
  { have : tendsto (λ n, ∫⁻ x in I, ∥f n x - g x∥₊ ∂μ) at_top (𝓝 0),
      from simple_func.tendsto_approx_on_range_L1_nnnorm hg.measurable hgi,
    refine (this.eventually (ge_mem_nhds ε0')).exists.imp (λ N hN, _),
    exact integral_coe_le_of_lintegral_coe_le hN },
  /- For each `x`, we choose `Nx x ≥ N₀` such that `dist (f Nx x) (g x) ≤ ε`. -/
  have : ∀ x, ∃ N₁, N₀ ≤ N₁ ∧ dist (f N₁ x) (g x) ≤ ε,
  { intro x,
    have : tendsto (λ n, f n x) at_top (𝓝 $ g x),
      from simple_func.tendsto_approx_on hg.measurable _ (subset_closure (by simp)),
    exact ((eventually_ge_at_top N₀).and $ this $ closed_ball_mem_nhds _ ε0).exists },
  choose Nx hNx hNxε,
  /- We also choose a convergent series with `∑' i : ℕ, δ i < ε`. -/
  rcases nnreal.exists_pos_sum_of_encodable ε0.ne' ℕ with ⟨δ, δ0, c, hδc, hcε⟩,
  /- Since each simple function `fᵢ` is integrable, there exists `rᵢ : ℝⁿ → (0, ∞)` such that
  the integral sum of `f` over any tagged prepartition is `δᵢ`-close to the sum of integrals
  of `fᵢ` over the boxes of this prepartition. For each `x`, we choose `r (Nx x)` as the radius
  at `x`. -/
  set r : ℝ≥0 → ℝⁿ → ℝ>0 := λ c x, (hfi' $ Nx x).convergence_r (δ $ Nx x) c x,
  refine ⟨r, λ c, l.r_cond_of_bRiemann_eq_ff hl, λ c π hπ hπp, _⟩,
  /- Now we prove the estimate in 3 "jumps": first we replace `g x` in the formula for the
  integral sum by `f (Nx x)`; then we replace each `μ J • f (Nx (π.tag J)) (π.tag J)`
  by the Bochner integral of `f (Nx (π.tag J)) x` over `J`, then we jump to the Bochner
  integral of `g`. -/
  refine (dist_triangle4 _ (∑ J in π.boxes, (μ J).to_real • f (Nx $ π.tag J) (π.tag J))
    (∑ J in π.boxes, ∫ x in J, f (Nx $ π.tag J) x ∂μ) _).trans _,
  rw [add_mul, add_mul, one_mul],
  refine add_le_add_three _ _ _,
  { /- Since each `f (Nx $ π.tag J)` is `ε`-close to `g (π.tag J)`, replacing the latter with
    the former in the formula for the integral sum changes the sum at most by `μ I * ε`. -/
    rw [← hπp.Union_eq, π.to_prepartition.measure_Union_to_real, sum_mul, integral_sum],
    refine dist_sum_sum_le_of_le _ (λ J hJ, _), dsimp,
    rw [dist_eq_norm, ← smul_sub, norm_smul, real.norm_eq_abs,
      abs_of_nonneg ennreal.to_real_nonneg],
    refine mul_le_mul_of_nonneg_left _ ennreal.to_real_nonneg,
    rw [← dist_eq_norm'], exact hNxε _ },
  { /- We group the terms of both sums by the values of `Nx (π.tag J)`.
    For each `N`, the sum of Bochner integrals over the boxes is equal
    to the sum of box integrals, and the sum of box integrals is `δᵢ`-close
    to the corresponding integral sum due to the Henstock-Sacks inequality. -/
    rw [← π.to_prepartition.sum_fiberwise (λ J, Nx (π.tag J)),
      ← π.to_prepartition.sum_fiberwise (λ J, Nx (π.tag J))],
    refine le_trans _ (nnreal.coe_lt_coe.2 hcε).le,
    refine (dist_sum_sum_le_of_le _ (λ n hn, _)).trans
      (sum_le_has_sum _ (λ n _, (δ n).2) (nnreal.has_sum_coe.2 hδc)),
    have hNxn : ∀ J ∈ π.filter (λ J, Nx (π.tag J) = n), Nx (π.tag J) = n,
      from λ J hJ, (π.mem_filter.1 hJ).2,
    have hrn : ∀ J ∈ π.filter (λ J, Nx (π.tag J) = n),
      r c (π.tag J) = (hfi' n).convergence_r (δ n) c (π.tag J),
    { intros J hJ,
      obtain rfl := hNxn J hJ,
      refl },
    have : l.mem_base_set I c ((hfi' n).convergence_r (δ n) c) (π.filter (λ J, Nx (π.tag J) = n)),
      from (hπ.filter _).mono' _ le_rfl le_rfl (λ J hJ, (hrn J hJ).le),
    convert (hfi' n).dist_integral_sum_sum_integral_le_of_mem_base_set (δ0 _) this using 2,
    { refine sum_congr rfl (λ J hJ, _),
      simp [hNxn J hJ] },
    { refine sum_congr rfl (λ J hJ, _),
      rw [← simple_func.integral_eq_integral, simple_func.box_integral_eq_integral _ _ _ _ hl,
        hNxn J hJ],
      exact (hfi _).mono_set (prepartition.le_of_mem _ hJ) } },
  { /-  For the last jump, we use the fact that the distance between `f (Nx x) x` and `g x` is less
    than or equal to the distance between `f N₀ x` and `g x` and the integral of `∥f N₀ x - g x∥`
    is less than or equal to `ε`. -/
    refine le_trans _ hN₀,
    have hfi : ∀ n (J ∈ π), integrable_on (f n) ↑J  μ,
      from λ n J hJ, (hfi n).mono_set (π.le_of_mem' J hJ),
    have hgi : ∀ J ∈ π, integrable_on g ↑J μ, from λ J hJ, hgi.mono_set (π.le_of_mem' J hJ),
    have hfgi : ∀ n (J ∈ π), integrable_on (λ x, ∥f n x - g x∥) J μ,
      from λ n J hJ, ((hfi n J hJ).sub (hgi J hJ)).norm,
    rw [← hπp.Union_eq, prepartition.Union_def',
      integral_finset_bUnion π.boxes (λ J hJ, J.measurable_set_coe) π.pairwise_disjoint hgi,
      integral_finset_bUnion π.boxes (λ J hJ, J.measurable_set_coe) π.pairwise_disjoint (hfgi _)],
    refine dist_sum_sum_le_of_le _ (λ J hJ, _),
    rw [dist_eq_norm, ← integral_sub (hfi _ J hJ) (hgi J hJ)],
    refine norm_integral_le_of_norm_le (hfgi _ J hJ) (eventually_of_forall $ λ x, _),
    exact hfg_mono x (hNx (π.tag J)) }
end

end measure_theory

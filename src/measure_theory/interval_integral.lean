/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import measure_theory.set_integral
import measure_theory.lebesgue_measure
import analysis.calculus.deriv

/-!
# Integral over an interval

In this file we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ` if `a ≤ b`
and `-∫ x in Ioc b a, f x ∂μ` if `b ≤ a`. We prove a few simple properties and the first part of the
[fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus),
see `integral_has_deriv_at_of_tendsto_ae`.

## Implementation notes

### Avoiding `if`, `min`, and `max`

In order to avoid `if`s in the definition, we define `interval_integrable f μ a b` as
`integrable_on f (Ioc a b) μ ∧ integrable_on f (Ioc b a) μ`. For any `a`, `b` one of these
intervals is empty and the other coincides with `Ioc (min a b) (max a b)`.

Similarly, we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`.
Again, for any `a`, `b` one of these integrals is zero, and the other gives the expected result.

This way some properties can be translated from integrals over sets without dealing with
the cases `a ≤ b` and `b ≤ a` separately.

### Choice of the interval

We use integral over `Ioc (min a b) (max a b)` instead of one of the other three possible
intervals with the same endpoints for two reasons:

* this way `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ` holds whenever
  `f` is integrable on each interval; in particular, it works even if the measure `μ` has an atom
  at `b`; this rules out `Ioo` and `Icc` intervals;
* with this definition for a probability measure `μ`, the integral `∫ x in a..b, 1 ∂μ` equals
  the difference $F_μ(b)-F_μ(a)$, where $F_μ(a)=μ(-∞, a]$ is the
  [cumulative distribution function](https://en.wikipedia.org/wiki/Cumulative_distribution_function)
  of `μ`.
-/

noncomputable theory
open topological_space (second_countable_topology)
open measure_theory set classical filter

open_locale classical topological_space filter

variables {α β 𝕜 E F : Type*} [decidable_linear_order α] [measurable_space α] [normed_group E]

/-!
### Integrability at an interval
-/

/-- A function `f` is called *interval integrable* with respect to a measure `μ` on an unordered
interval `a..b` if it is integrable on both intervals `(a, b]` and `(b, a]`. One of these
intervals is always empty, so this property is equivalent to `f` being integrable on
`(min a b, max a b]`. -/
def interval_integrable (f : α → E) (μ : measure α) (a b : α) :=
integrable_on f (Ioc a b) μ ∧ integrable_on f (Ioc b a) μ

namespace interval_integrable

section

variables {f : α → E} {a b c : α} {μ : measure α}

@[symm] lemma symm (h : interval_integrable f μ a b) : interval_integrable f μ b a :=
h.symm

@[refl] lemma refl : interval_integrable f μ a a :=
by split; simp

@[trans] lemma trans  (hab : interval_integrable f μ a b)
  (hbc : interval_integrable f μ b c) :
  interval_integrable f μ a c :=
⟨(hab.1.union hbc.1).mono_set Ioc_subset_Ioc_union_Ioc,
  (hbc.2.union hab.2).mono_set Ioc_subset_Ioc_union_Ioc⟩

lemma neg (h : interval_integrable f μ a b) : interval_integrable (-f) μ a b :=
⟨h.1.neg, h.2.neg⟩

end

lemma smul [normed_field 𝕜] [normed_space 𝕜 E] {f : α → E} {a b : α} {μ : measure α}
  (h : interval_integrable f μ a b) (r : 𝕜) :
  interval_integrable (r • f) μ a b :=
⟨h.1.smul r, h.2.smul r⟩

variables [measurable_space E] [opens_measurable_space E] {f g : α → E} {a b : α} {μ : measure α}

lemma add (hfm : measurable f) (hfi : interval_integrable f μ a b)
  (hgm : measurable g) (hgi : interval_integrable g μ a b) :
  interval_integrable (f + g) μ a b :=
⟨hfi.1.add hfm hgm hgi.1, hfi.2.add hfm hgm hgi.2⟩

lemma sub (hfm : measurable f) (hfi : interval_integrable f μ a b)
  (hgm : measurable g) (hgi : interval_integrable g μ a b) :
  interval_integrable (f - g) μ a b :=
⟨hfi.1.sub hfm hgm hgi.1, hfi.2.sub hfm hgm hgi.2⟩

end interval_integrable

/-- If `f : α → E` has a finite limit at `l ⊓ μ.ae`, where `l` is a measurably generated interval
generated filter and `μ` is a measure finite at this filter, then `f` is interval integrable
with respect to `μ` on `a..b` as both `a` and `b` tend to `l`. -/
lemma filter.tendsto.eventually_interval_integrable_ae {f : α → E} {μ : measure α} {l : filter α}
  [is_interval_generated l] [is_measurably_generated l]
  (hμ : μ.finite_at_filter l) {c : E} (hf : tendsto f (l ⊓ μ.ae) (𝓝 c))
  {a b : β → α} {lb : filter β} (ha : tendsto a lb l) (hb : tendsto b lb l) :
  ∀ᶠ t in lb, interval_integrable f μ (a t) (b t) :=
have _ := (hf.integrable_at_filter_ae hμ).eventually,
((ha.Ioc hb).eventually this).and $ (hb.Ioc ha).eventually this

/-- If `f : α → E` has a finite limit at a measurably generated interval generated filter `l`
and `μ` is a measure finite at this filter, then `f` is interval integrable with respect
to `μ` on `a..b` as both `a` and `b` tend to `l`. -/
lemma filter.tendsto.eventually_interval_integrable {f : α → E} {μ : measure α} {l : filter α}
  [is_interval_generated l] [is_measurably_generated l]
  (hμ : μ.finite_at_filter l) {c : E} (hf : tendsto f l (𝓝 c))
  {a b : β → α} {lb : filter β} (ha : tendsto a lb l) (hb : tendsto b lb l) :
  ∀ᶠ t in lb, interval_integrable f μ (a t) (b t) :=
(tendsto_le_left (inf_le_left : l ⊓ μ.ae ≤ l) hf).eventually_interval_integrable_ae hμ ha hb

/-!
### Interval integral: definition and basic properties
-/

variables [second_countable_topology E] [complete_space E] [normed_space ℝ E]
  [measurable_space E] [borel_space E]

/-- The interval integral `∫ x in a..b, f x ∂μ` is defined
as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals
`∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`. -/
def interval_integral (f : α → E) (a b : α) (μ : measure α) :=
∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ

notation `∫` binders ` in ` a `..` b `, ` r:(scoped:60 f, f) ` ∂` μ:70 := interval_integral r a b μ
notation `∫` binders ` in ` a `..` b `, ` r:(scoped:60 f, interval_integral f a b volume) := r

namespace interval_integral

section

variables {a b c : α} {f g : α → E} {μ : measure α}

lemma integral_of_le (h : a ≤ b) : ∫ x in a..b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ :=
by simp [interval_integral, h]

@[simp] lemma integral_same : ∫ x in a..a, f x ∂μ = 0 :=
sub_self _

lemma integral_symm (a b) : ∫ x in b..a, f x ∂μ = -∫ x in a..b, f x ∂μ :=
by simp only [interval_integral, neg_sub]

lemma integral_of_ge (h : b ≤ a) : ∫ x in a..b, f x ∂μ = -∫ x in Ioc b a, f x ∂μ :=
by simp only [integral_symm b, integral_of_le h]

lemma integral_cases (f : α → E) (a b) :
  ∫ x in a..b, f x ∂μ ∈ ({∫ x in Ioc (min a b) (max a b), f x ∂μ,
    -∫ x in Ioc (min a b) (max a b), f x ∂μ} : set E) :=
(le_total a b).imp (λ h, by simp [h, integral_of_le]) (λ h, by simp [h, integral_of_ge])

lemma norm_integral_eq_norm_integral_Ioc :
  ∥∫ x in a..b, f x ∂μ∥ = ∥∫ x in Ioc (min a b) (max a b), f x ∂μ∥ :=
(integral_cases f a b).elim (congr_arg _) (λ h, (congr_arg _ h).trans (norm_neg _))

lemma norm_integral_le_integral_norm_Ioc :
  ∥∫ x in a..b, f x ∂μ∥ ≤ ∫ x in Ioc (min a b) (max a b), ∥f x∥ ∂μ :=
calc ∥∫ x in a..b, f x ∂μ∥ = ∥∫ x in Ioc (min a b) (max a b), f x ∂μ∥ :
  norm_integral_eq_norm_integral_Ioc
... ≤ ∫ x in Ioc (min a b) (max a b), ∥f x∥ ∂μ :
  norm_integral_le_integral_norm f

lemma norm_integral_le_abs_integral_norm : ∥∫ x in a..b, f x ∂μ∥ ≤ abs (∫ x in a..b, ∥f x∥ ∂μ) :=
begin
  simp only [← real.norm_eq_abs, norm_integral_eq_norm_integral_Ioc],
  exact le_trans (norm_integral_le_integral_norm _) (le_abs_self _)
end

lemma norm_integral_le_of_norm_le_const_ae {a b C : ℝ} {f : ℝ → E}
  (h : ∀ᵐ x, x ∈ Ioc (min a b) (max a b) → ∥f x∥ ≤ C) :
  ∥∫ x in a..b, f x∥ ≤ C * abs (b - a) :=
begin
  rw [norm_integral_eq_norm_integral_Ioc],
  convert norm_set_integral_le_of_norm_le_const_ae'' _ is_measurable_Ioc h,
  { rw [real.volume_Ioc, max_sub_min_eq_abs, ennreal.to_real_of_real (abs_nonneg _)] },
  { simp only [real.volume_Ioc, ennreal.of_real_lt_top] },
end

lemma norm_integral_le_of_norm_le_const {a b C : ℝ} {f : ℝ → E}
  (h : ∀ x ∈ Ioc (min a b) (max a b), ∥f x∥ ≤ C) :
  ∥∫ x in a..b, f x∥ ≤ C * abs (b - a) :=
norm_integral_le_of_norm_le_const_ae $ eventually_of_forall h

lemma integral_add (hfm : measurable f) (hfi : interval_integrable f μ a b)
  (hgm : measurable g) (hgi : interval_integrable g μ a b) :
  ∫ x in a..b, f x + g x ∂μ = ∫ x in a..b, f x ∂μ + ∫ x in a..b, g x ∂μ :=
begin
  simp only [interval_integral, integral_add hfm hfi.1 hgm hgi.1,
    integral_add hfm hfi.2 hgm hgi.2],
  abel
end

@[simp] lemma integral_neg : ∫ x in a..b, -f x ∂μ = -∫ x in a..b, f x ∂μ :=
begin
  simp only [interval_integral, integral_neg],
  abel
end

lemma integral_sub (hfm : measurable f) (hfi : interval_integrable f μ a b)
  (hgm : measurable g) (hgi : interval_integrable g μ a b) :
  ∫ x in a..b, f x - g x ∂μ = ∫ x in a..b, f x ∂μ - ∫ x in a..b, g x ∂μ :=
(integral_add hfm hfi hgm.neg hgi.neg).trans $ congr_arg _ integral_neg

lemma integral_smul (r : ℝ) : ∫ x in a..b, r • f x ∂μ = r • ∫ x in a..b, f x ∂μ :=
by simp only [interval_integral, integral_smul, smul_sub]

lemma integral_const' (c : E) :
  ∫ x in a..b, c ∂μ = ((μ $ Ioc a b).to_real - (μ $ Ioc b a).to_real) • c :=
by simp only [interval_integral, set_integral_const, sub_smul]

lemma integral_const {a b : ℝ} (c : E) : (∫ (x : ℝ) in a..b, c) = (b - a) • c :=
by simp only [integral_const', real.volume_Ioc, ennreal.to_real_of_real', ← neg_sub b,
  max_zero_sub_eq_self]

variables [topological_space α] [opens_measurable_space α]

section order_closed_topology

variables [order_closed_topology α]

lemma integral_add_adjacent_intervals_cancel (hfm : measurable f)
  (hab : interval_integrable f μ a b) (hbc : interval_integrable f μ b c) :
  ∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ + ∫ x in c..a, f x ∂μ = 0 :=
begin
  have hac := hab.trans hbc,
  simp only [interval_integral, ← add_sub_comm, sub_eq_zero],
  iterate 4 { rw ← integral_union },
  { suffices : Ioc a b ∪ Ioc b c ∪ Ioc c a = Ioc b a ∪ Ioc c b ∪ Ioc a c, by rw this,
    rw [Ioc_union_Ioc_union_Ioc_cycle, union_right_comm, Ioc_union_Ioc_union_Ioc_cycle,
      min_left_comm, max_left_comm] },
  all_goals { simp [*, is_measurable.union, is_measurable_Ioc, Ioc_disjoint_Ioc_same,
    Ioc_disjoint_Ioc_same.symm, hab.1, hab.2, hbc.1, hbc.2, hac.1, hac.2] }
end

lemma integral_add_adjacent_intervals (hfm : measurable f) (hab : interval_integrable f μ a b)
  (hbc : interval_integrable f μ b c) :
  ∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ :=
by rw [← add_neg_eq_zero, ← integral_symm, integral_add_adjacent_intervals_cancel hfm hab hbc]

lemma integral_interval_sub_left (hfm : measurable f) (hab : interval_integrable f μ a b)
  (hac : interval_integrable f μ a c) :
  ∫ x in a..b, f x ∂μ - ∫ x in a..c, f x ∂μ = ∫ x in c..b, f x ∂μ :=
sub_eq_of_eq_add' $ eq.symm $ integral_add_adjacent_intervals hfm hac (hac.symm.trans hab)

lemma integral_Ici_sub_Ici (hfm : measurable f) (ha : integrable_on f (Iic a) μ)
  (hb : integrable_on f (Iic b) μ) :
  ∫ x in Iic b, f x ∂μ - ∫ x in Iic a, f x ∂μ = ∫ x in a..b, f x ∂μ :=
begin
  wlog hab : a ≤ b using [a b] tactic.skip,
  { rw [sub_eq_iff_eq_add', integral_of_le hab, ← integral_union (Iic_disjoint_Ioc (le_refl _)),
      Iic_union_Ioc_eq_Iic hab],
    exacts [is_measurable_Iic, is_measurable_Ioc, hfm, ha, hb.mono_set (λ _, and.right)] },
  { intros ha hb,
    rw [integral_symm, ← this hb ha, neg_sub] }
end

/-- If `μ` is a finite measure then `∫ x in a..b, c ∂μ = (μ (Iic b) - μ (Iic a)) • c`. -/
lemma integral_const_of_cdf [finite_measure μ] (c : E) :
  ∫ x in a..b, c ∂μ = ((μ (Iic b)).to_real - (μ (Iic a)).to_real) • c :=
begin
  simp only [sub_smul, ← set_integral_const],
  refine (integral_Ici_sub_Ici measurable_const _ _).symm;
    simp only [integrable_on_const, measure_lt_top, or_true]
end

end order_closed_topology

end

/-!
### Fundamental theorem of calculus, part 1

In this section we prove many versions of FTC-1. First we prove supporting lemmas that work for any
measure on an ordered type, then specialize them for the Lebesgue measure on `ℝ`.
-/

open asymptotics

section

variables {f : α → E} {c : E} {l : filter α} {lb : filter β}
  [is_measurably_generated l] [is_interval_generated l] {μ : measure α}

/-- If `f` has a finite limit `c` at `l ⊓ μ.ae`, where `l` is a measurably generated interval
generated filter (e.g., `𝓝 a`, `𝓝[Ici a] a`, `𝓝[Iic a] a`, or `at_top`) and `μ` is a measure
finite at `l`, then `∫ x in a..b, f x ∂μ = ((μ (I-/
lemma integral_sub_linear_is_o_of_tendsto_ae₂ (hfm : measurable f)
  (hf : tendsto f (l ⊓ μ.ae) (𝓝 c)) (hl : μ.finite_at_filter l)
  {a b : β → α} (ha : tendsto a lb l) (hb : tendsto b lb l) :
  is_o (λ t, ∫ x in a t..b t, f x ∂μ - ∫ x in a t..b t, c ∂μ)
    (λ t, (μ (Ioc (min (a t) (b t)) (max (a t) (b t)))).to_real) lb :=
begin
  have A := (hf.integral_sub_linear_is_o_ae hfm hl).comp_tendsto (ha.Ioc hb),
  have B := (hf.integral_sub_linear_is_o_ae hfm hl).comp_tendsto (hb.Ioc ha),
  convert (A.trans_le _).sub (B.trans_le _),
  { ext t,
    simp_rw [(∘), integral_const', interval_integral, sub_smul],
    abel },
  all_goals { intro t, cases le_total (a t) (b t) with hab hab; simp [hab] }
end

lemma integral_sub_linear_is_o_of_tendsto_ae_of_le (hfm : measurable f)
  (hf : tendsto f (l ⊓ μ.ae) (𝓝 c)) (hl : μ.finite_at_filter l)
  {a b : β → α} (ha : tendsto a lb l) (hb : tendsto b lb l) (hab : a ≤ᶠ[lb] b) :
  is_o (λ t, ∫ x in a t..b t, f x ∂μ - (μ (Ioc (a t) (b t))).to_real • c)
    (λ t, (μ $ Ioc (a t) (b t)).to_real) lb :=
(integral_sub_linear_is_o_of_tendsto_ae₂ hfm hf hl ha hb).congr'
  (hab.mono $ λ x hx, by simp [integral_const', hx]) (hab.mono $ λ x hx, by simp [hx])

lemma integral_sub_linear_is_o_of_tendsto_ae_of_ge (hfm : measurable f)
  (hf : tendsto f (l ⊓ μ.ae) (𝓝 c)) (hl : μ.finite_at_filter l)
  {a b : β → α} (ha : tendsto a lb l) (hb : tendsto b lb l) (hab : b ≤ᶠ[lb] a) :
  is_o (λ t, ∫ x in a t..b t, f x ∂μ + (μ (Ioc (b t) (a t))).to_real • c)
    (λ t, (μ $ Ioc (b t) (a t)).to_real) lb :=
(integral_sub_linear_is_o_of_tendsto_ae_of_le hfm hf hl hb ha hab).neg_left.congr_left $ λ t,
  by simp [integral_symm (a t), add_comm]

variables [topological_space α] [order_topology α] [borel_space α]

lemma integral_sub_linear_is_o_of_tendsto_ae [locally_finite_measure μ] {f : α → E} {a : α}
  {c : E} (hfm : measurable f) (hf : tendsto f ((𝓝 a) ⊓ μ.ae) (𝓝 c)) :
  is_o (λ b, ∫ x in a..b, f x ∂μ - ∫ x in a..b, c ∂μ)
    (λ b, (μ (Ioc (min a b) (max a b))).to_real) (𝓝 a) :=
integral_sub_linear_is_o_of_tendsto_ae₂ hfm hf (μ.finite_at_nhds a) tendsto_const_nhds tendsto_id

lemma integral_sub_linear_is_o_of_tendsto_ae_left [locally_finite_measure μ] {f : α → E} {a : α}
  {c : E} (hfm : measurable f) (hf : tendsto f ((nhds_within a (Iic a)) ⊓ μ.ae) (𝓝 c)) :
  is_o (λ b, ∫ x in a..b, f x ∂μ + (μ $ Ioc b a).to_real • c)
    (λ b, (μ $ Ioc b a).to_real) (nhds_within a $ Iic a) :=
integral_sub_linear_is_o_of_tendsto_ae_of_ge hfm hf (μ.finite_at_nhds_within _ _)
  (tendsto_le_right (pure_le_nhds_within right_mem_Iic) tendsto_const_pure) tendsto_id $
  eventually_nhds_within_iff.2 $ eventually_of_forall $ λ _, id

lemma integral_sub_linear_is_o_of_tendsto_ae_right [locally_finite_measure μ] {f : α → E} {a : α}
  {c : E} (hfm : measurable f) (hf : tendsto f ((nhds_within a (Ici a)) ⊓ μ.ae) (𝓝 c)) :
  is_o (λ b, ∫ x in a..b, f x ∂μ - (μ $ Ioc a b).to_real • c)
    (λ b, (μ $ Ioc a b).to_real) (nhds_within a $ Ici a) :=
integral_sub_linear_is_o_of_tendsto_ae_of_le hfm hf (μ.finite_at_nhds_within _ _)
  (tendsto_le_right (pure_le_nhds_within left_mem_Ici) tendsto_const_pure) tendsto_id $
  eventually_nhds_within_iff.2 $ eventually_of_forall $ λ _, id

end

variables {f : ℝ → E} {c : E} {l : filter ℝ} {lb : filter β} [is_measurably_generated l]
  [is_interval_generated l] {a b z : ℝ}

lemma integral_volume_sub_linear_is_o_of_tendsto_ae (hfm : measurable f)
  (hf : tendsto f (l ⊓ volume.ae) (𝓝 c)) (hz : l ≤ 𝓝 z)
  {a b : β → ℝ} (ha : tendsto a lb l) (hb : tendsto b lb l) :
  is_o (λ t, (∫ x in a t..b t, f x) - (b t - a t) • c) (b - a) lb :=
begin
  refine ((integral_sub_linear_is_o_of_tendsto_ae₂ hfm hf
    ((volume.finite_at_nhds _).filter_mono hz) ha hb).congr _ _).of_norm_right,
  { intro t,
    simp only [integral_const] },
  { intro t,
    simp [max_sub_min_eq_abs, abs_nonneg, real.norm_eq_abs] }
end

lemma integral_volume_sub_integral_sub_linear_is_o_of_tendsto_ae
  (hfm : measurable f) (hf : tendsto f (l ⊓ volume.ae) (𝓝 c))
  (hb : l ≤ 𝓝 b) (hb' : pure b ≤ l) (hab : interval_integrable f volume a b)
  {u₁ u₂ : β → ℝ} (h₁ : tendsto u₁ lb l) (h₂ : tendsto u₂ lb l) :
  is_o (λ t, (∫ x in a..u₁ t, f x) - (∫ x in a..u₂ t, f x) - (u₁ t - u₂ t) • c) (u₁ - u₂) lb :=
begin
  refine (integral_volume_sub_linear_is_o_of_tendsto_ae hfm hf hb h₂ h₁).congr' _
    (eventually_eq.refl _ _),
  have hl : volume.finite_at_filter l := (volume.finite_at_nhds _).filter_mono hb,
  have A : ∀ᶠ t in lb, interval_integrable f volume (u₂ t) (u₁ t) :=
    hf.eventually_interval_integrable_ae hl h₂ h₁,
  have B : ∀ᶠ t in lb, interval_integrable f volume a (u₂ t) :=
    (hf.eventually_interval_integrable_ae hl (tendsto_le_right hb' tendsto_const_pure) h₂).mono
      (λ x hx, hab.trans hx),
  refine A.mp (B.mono $ λ x h₂ h₂₁, _),
  simp [← integral_add_adjacent_intervals hfm h₂ h₂₁]
end

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b`, then `u ↦ ∫ x in a..u, f x` has derivative `c` at `b`
in the sense of strict differentiability. -/
lemma integral_has_strict_deriv_at_of_tendsto_ae (hfm : measurable f)
  (hfi : interval_integrable f volume a b) (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 c)) :
  has_strict_deriv_at (λ u, ∫ x in a..u, f x) c b :=
integral_volume_sub_integral_sub_linear_is_o_of_tendsto_ae hfm hb (le_refl _) (pure_le_nhds _)
  hfi continuous_at_fst continuous_at_snd

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b`, then `u ↦ ∫ x in a..u, f x` has derivative `c` at
`b`. -/
lemma integral_has_deriv_at_of_tendsto_ae (hfm : measurable f)
  (hfi : interval_integrable f volume a b) (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 c)) :
  has_deriv_at (λ u, ∫ x in a..u, f x) c b :=
(integral_has_strict_deriv_at_of_tendsto_ae hfm hfi hb).has_deriv_at

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `f b` at `b`. -/
lemma integral_has_deriv_at (hfm : measurable f) (hfi : interval_integrable f volume a b)
  (hb : continuous_at f b) :
  has_deriv_at (λ u, ∫ x in a..u, f x) (f b) b :=
integral_has_deriv_at_of_tendsto_ae hfm hfi (flip tendsto_le_left hb inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b`
equals `c`. -/
lemma deriv_integral_eq_of_tendsto_ae (hfm : measurable f) (hfi : interval_integrable f volume a b)
  (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 c)) :
  deriv (λ u, ∫ x in a..u, f x) b = c :=
(integral_has_deriv_at_of_tendsto_ae hfm hfi hb).deriv

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `f b`. -/
lemma deriv_integral_eq (hfm : measurable f) (hfi : interval_integrable f volume a b)
  (hb : continuous_at f b) :
  deriv (λ u, ∫ x in a..u, f x) b = f b :=
(integral_has_deriv_at hfm hfi hb).deriv

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right, then `u ↦ ∫ x in a..u, f x` has
right derivative `c` at `b`. -/
lemma integral_has_deriv_within_at_Ici_of_tendsto_ae (hfm : measurable f)
  (hfi : interval_integrable f volume a b)
  (hb : tendsto f (nhds_within b (Ici b) ⊓ volume.ae) (𝓝 c)) :
  has_deriv_within_at (λ u, ∫ x in a..u, f x) c (Ici b) b :=
have pure b ≤ nhds_within b (Ici b) := pure_le_nhds_within left_mem_Ici,
integral_volume_sub_integral_sub_linear_is_o_of_tendsto_ae hfm hb inf_le_left this hfi
  tendsto_id (flip tendsto_le_right tendsto_const_pure this)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the right at `b`, then `u ↦ ∫ x in a..u, f x` has right derivative `f b` at `b`. -/
lemma integral_has_deriv_within_at_Ici (hfm : measurable f) (hfi : interval_integrable f volume a b)
  (hb : continuous_within_at f (Ici b) b) :
  has_deriv_within_at (λ u, ∫ x in a..u, f x) (f b) (Ici b) b :=
integral_has_deriv_within_at_Ici_of_tendsto_ae hfm hfi (flip tendsto_le_left hb inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right, then the right derivative
of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
lemma deriv_within_Ici_integral_of_tendsto_ae (hfm : measurable f)
  (hfi : interval_integrable f volume a b)
  (hb : tendsto f (nhds_within b (Ici b) ⊓ volume.ae) (𝓝 c)) :
  deriv_within (λ u, ∫ x in a..u, f x) (Ici b) b = c :=
(integral_has_deriv_within_at_Ici_of_tendsto_ae hfm hfi hb).deriv_within $
  unique_diff_on_Ici _ _ left_mem_Ici

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the right at `b`, then the right derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
lemma deriv_within_Ici_integral (hfm : measurable f) (hfi : interval_integrable f volume a b)
  (hb : continuous_within_at f (Ici b) b) :
  deriv_within (λ u, ∫ x in a..u, f x) (Ici b) b = f b :=
(integral_has_deriv_within_at_Ici hfm hfi hb).deriv_within $
  unique_diff_on_Ici _ _ left_mem_Ici

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the left, then `u ↦ ∫ x in a..u, f x` has left
derivative `c` at `b`. -/
lemma integral_has_deriv_within_at_Iic_of_tendsto_ae (hfm : measurable f)
  (hfi : interval_integrable f volume a b)
  (hb : tendsto f (nhds_within b (Iic b) ⊓ volume.ae) (𝓝 c)) :
  has_deriv_within_at (λ u, ∫ x in a..u, f x) c (Iic b) b :=
have pure b ≤ nhds_within b (Iic b) := pure_le_nhds_within right_mem_Iic,
integral_volume_sub_integral_sub_linear_is_o_of_tendsto_ae hfm hb inf_le_left this hfi
  tendsto_id (flip tendsto_le_right tendsto_const_pure this)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left at `b`, then `u ↦ ∫ x in a..u, f x` has left derivative `f b` at `b`. -/
lemma integral_has_deriv_within_at_Iic (hfm : measurable f) (hfi : interval_integrable f volume a b)
  (hb : continuous_within_at f (Iic b) b) :
  has_deriv_within_at (λ u, ∫ x in a..u, f x) (f b) (Iic b) b :=
integral_has_deriv_within_at_Iic_of_tendsto_ae hfm hfi (flip tendsto_le_left hb inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the left, then the left derivative
of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
lemma deriv_within_Iic_integral_of_tendsto_ae (hfm : measurable f)
  (hfi : interval_integrable f volume a b)
  (hb : tendsto f (nhds_within b (Iic b) ⊓ volume.ae) (𝓝 c)) :
  deriv_within (λ u, ∫ x in a..u, f x) (Iic b) b = c :=
(integral_has_deriv_within_at_Iic_of_tendsto_ae hfm hfi hb).deriv_within $
  unique_diff_on_Iic _ _ right_mem_Iic

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left at `b`, then the left derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
lemma deriv_within_Iic_integral (hfm : measurable f) (hfi : interval_integrable f volume a b)
  (hb : continuous_within_at f (Iic b) b) :
  deriv_within (λ u, ∫ x in a..u, f x) (Iic b) b = f b :=
(integral_has_deriv_within_at_Iic hfm hfi hb).deriv_within $
  unique_diff_on_Iic _ _ right_mem_Iic

end interval_integral

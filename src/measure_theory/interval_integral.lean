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
see `integral_has_strict_deriv_at_of_tendsto_ae`.

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

-- TODO: rewrite docstring
/-- If `f : α → E` has a finite limit at `l ⊓ μ.ae`, where `l` is a measurably generated interval
generated filter and `μ` is a measure finite at this filter, then `f` is interval integrable
with respect to `μ` on `u..v` as both `u` and `v` tend to `l`. -/
lemma filter.tendsto.eventually_interval_integrable_ae {f : α → E} {μ : measure α}
  {l l' : filter α} [tendsto_Ixx_class Ioc l l'] [is_measurably_generated l']
  (hμ : μ.finite_at_filter l') {c : E} (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c))
  {u v : β → α} {lb : filter β} (hu : tendsto u lb l) (hv : tendsto v lb l) :
  ∀ᶠ t in lb, interval_integrable f μ (u t) (v t) :=
have _ := (hf.integrable_at_filter_ae hμ).eventually,
((hu.Ioc hv).eventually this).and $ (hv.Ioc hu).eventually this

-- TODO: rewrite docstring
/-- If `f : α → E` has a finite limit at a measurably generated interval generated filter `l`
and `μ` is a measure finite at this filter, then `f` is interval integrable with respect
to `μ` on `u..v` as both `u` and `v` tend to `l`. -/
lemma filter.tendsto.eventually_interval_integrable {f : α → E} {μ : measure α}
  {l l' : filter α} [tendsto_Ixx_class Ioc l l'] [is_measurably_generated l']
  (hμ : μ.finite_at_filter l') {c : E} (hf : tendsto f l' (𝓝 c))
  {u v : β → α} {lb : filter β} (hu : tendsto u lb l) (hv : tendsto v lb l) :
  ∀ᶠ t in lb, interval_integrable f μ (u t) (v t) :=
(tendsto_le_left (inf_le_left : l' ⊓ μ.ae ≤ l') hf).eventually_interval_integrable_ae hμ hu hv

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

variables {a b c d : α} {f g : α → E} {μ : measure α}

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

/-!
### Additivity in intervals

In this section we prove that `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ`
as well as a few other identities trivially equivalent to this one.
-/

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

lemma integral_interval_add_interval_comm (hfm : measurable f) (hab : interval_integrable f μ a b)
  (hcd : interval_integrable f μ c d) (hac : interval_integrable f μ a c) :
  ∫ x in a..b, f x ∂μ + ∫ x in c..d, f x ∂μ = ∫ x in a..d, f x ∂μ + ∫ x in c..b, f x ∂μ :=
by rw [← integral_add_adjacent_intervals hfm hac hcd, add_assoc, add_left_comm,
  integral_add_adjacent_intervals hfm hac (hac.symm.trans hab), add_comm]

lemma integral_interval_sub_interval_comm (hfm : measurable f) (hab : interval_integrable f μ a b)
  (hcd : interval_integrable f μ c d) (hac : interval_integrable f μ a c) :
  ∫ x in a..b, f x ∂μ - ∫ x in c..d, f x ∂μ = ∫ x in a..c, f x ∂μ - ∫ x in b..d, f x ∂μ :=
by simp only [sub_eq_add_neg, ← integral_symm,
  integral_interval_add_interval_comm hfm hab hcd.symm (hac.trans hcd)]

lemma integral_interval_sub_interval_comm' (hfm : measurable f) (hab : interval_integrable f μ a b)
  (hcd : interval_integrable f μ c d) (hac : interval_integrable f μ a c) :
  ∫ x in a..b, f x ∂μ - ∫ x in c..d, f x ∂μ = ∫ x in d..b, f x ∂μ - ∫ x in c..a, f x ∂μ :=
by rw [integral_interval_sub_interval_comm hfm hab hcd hac, integral_symm b d, integral_symm a c,
  sub_neg_eq_add, sub_eq_neg_add]

lemma integral_Iic_sub_Iic (hfm : measurable f) (ha : integrable_on f (Iic a) μ)
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
  refine (integral_Iic_sub_Iic measurable_const _ _).symm;
    simp only [integrable_on_const, measure_lt_top, or_true]
end

end order_closed_topology

end

/-!
### Fundamental theorem of calculus, part 1, for any measure

In this section we prove a few lemmas that can be seen as versions of FTC-1 for interval integral
w.r.t. any measure. Many theorems are formulated for any measurably generated interval generated
filter `l` such that `pure b ≤ l ≤ 𝓝 b`. In the most interesting case `α = ℝ`, there are only four
filters with these properties: `pure b`, `𝓝[Ici b] b`, `𝓝[Iic b] b`, and `𝓝 b`. For `pure b` most
of these theorems are trivial; we use `filter` versions to avoid repeating the same arguments for
the other three filters.

The most general theorem `measure_integral_sub_linear_is_o_of_tendsto_ae` says
that `∫ x in u t..v t, f x ∂μ = ∫ x in u t..v t, c ∂μ + o(∫ x in u t..v t, 1 ∂μ)` provided that both
`u` and `v` tend to a measurably generated interval generated filter `l` (e.g., `𝓝 a`, `𝓝[Ici a] a`,
`𝓝[Iic a] a`, or `at_top`) such that `μ` is finite at this filter, and `f x` tends to `c` as `x`
tends to `l ⊓ μ.ae`.

This theorem is formulated with integral of constants instead of measures in the right hand sides
for two reasons: first, this way we avoid `min`/`max` in the statements; second, often it is
possible to write better `simp` lemmas for these integrals, see `integral_const` and
`integral_const_of_cdf`.

We apply this theorem to prove lemma `measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae`
which corresponds to the `has_strict_deriv_at` version of FTC-1. If `f` is a measurable function
integrable on `a..b` and `l`, `pure b ≤ l ≤ 𝓝 b`, is a measurably generated interval generated
filter (e.g., `𝓝 b`, `𝓝[Ici b] b`, or `𝓝[Iic b] b`) such that `μ` is finite at `l` and `f x` tends
to `c` as `x` tends to `l ⊓ μ.ae` then
`∫ x in a..v, f x ∂μ - ∫ x in a..u, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)`
as `u` and `v` tend to `l`.

-/

namespace FTC

class FTC_filter {β : Type*} [linear_order β] [measurable_space β] [topological_space β]
  (a : out_param β) (outer : filter β) (inner : out_param $ filter β)
  extends tendsto_Ixx_class Ioc outer inner : Prop :=
(pure_le : pure a ≤ outer)
(le_nhds : inner ≤ 𝓝 a)
[meas_gen : is_measurably_generated inner]

namespace FTC_filter

variables [linear_order β] [measurable_space β] [topological_space β]

instance pure (a : β) : FTC_filter a (pure a) ⊥ :=
{ pure_le := le_refl _,
  le_nhds := bot_le }

variables [opens_measurable_space β] [order_topology β]

instance nhds (a : β) : FTC_filter a (𝓝 a) (𝓝 a) :=
{ pure_le := pure_le_nhds a,
  le_nhds := le_refl _ }

instance nhds_left (a : β) : FTC_filter a (𝓝[Iic a] a) (𝓝[Iic a] a) :=
{ pure_le := pure_le_nhds_within right_mem_Iic,
  le_nhds := inf_le_left }

instance nhds_right (a : β) : FTC_filter a (𝓝[Ici a] a) (𝓝[Ioi a] a) :=
{ pure_le := pure_le_nhds_within left_mem_Ici,
  le_nhds := inf_le_left }

end FTC_filter

open asymptotics

section

variables {f : α → E} {c ca cb : E} {l l' la la' lb lb' : filter α} {lt : filter β}
  {μ : measure α} {u v ua va ub vb : β → α}

/-- Fundamental theorem of calculus-1, local version for any measure.
If `f` has a finite limit `c` at `l ⊓ μ.ae`, where `l` is a measurably generated interval
generated filter (e.g., `𝓝 a`, `𝓝[Ici a] a`, `𝓝[Iic a] a`, or `at_top`) and `μ` is a measure
finite at `l`, then `∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)` as both
`u` and `v` tend to `l`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae
  [is_measurably_generated l'] [tendsto_Ixx_class Ioc l l']
  (hfm : measurable f) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c)) (hl : μ.finite_at_filter l')
  (hu : tendsto u lt l) (hv : tendsto v lt l) :
  is_o (λ t, ∫ x in u t..v t, f x ∂μ - ∫ x in u t..v t, c ∂μ)
    (λ t, ∫ x in u t..v t, (1:ℝ) ∂μ) lt :=
begin
  have A := (hf.integral_sub_linear_is_o_ae hfm hl).comp_tendsto (hu.Ioc hv),
  have B := (hf.integral_sub_linear_is_o_ae hfm hl).comp_tendsto (hv.Ioc hu),
  simp only [integral_const'],
  convert (A.trans_le _).sub (B.trans_le _),
  { ext t,
    simp_rw [(∘), interval_integral, sub_smul],
    abel },
  all_goals { intro t, cases le_total (u t) (v t) with huv huv; simp [huv] }
end

lemma measure_integral_sub_linear_is_o_of_tendsto_ae_of_le
  [is_measurably_generated l'] [tendsto_Ixx_class Ioc l l']
  (hfm : measurable f) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c)) (hl : μ.finite_at_filter l')
  (hu : tendsto u lt l) (hv : tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
  is_o (λ t, ∫ x in u t..v t, f x ∂μ - (μ (Ioc (u t) (v t))).to_real • c)
    (λ t, (μ $ Ioc (u t) (v t)).to_real) lt :=
(measure_integral_sub_linear_is_o_of_tendsto_ae hfm hf hl hu hv).congr'
  (huv.mono $ λ x hx, by simp [integral_const', hx])
  (huv.mono $ λ x hx, by simp [integral_const', hx])

lemma measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge
  [is_measurably_generated l'] [tendsto_Ixx_class Ioc l l']
  (hfm : measurable f) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c)) (hl : μ.finite_at_filter l')
  (hu : tendsto u lt l) (hv : tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
  is_o (λ t, ∫ x in u t..v t, f x ∂μ + (μ (Ioc (v t) (u t))).to_real • c)
    (λ t, (μ $ Ioc (v t) (u t)).to_real) lt :=
(measure_integral_sub_linear_is_o_of_tendsto_ae_of_le hfm hf hl hv hu huv).neg_left.congr_left $
  λ t, by simp [integral_symm (u t), add_comm]

variables [topological_space α] [order_topology α] [borel_space α]

/-- Fundamental theorem of calculus-1, strict derivative in both limits for any measure.
Let `f` be a measurable function integrable on `a..b`.
Let `la`, `pure a ≤ la ≤ 𝓝 a`, be a measurably generated interval generated filter such that
`μ` is finite at `la` and `f x` has a finite limit `ca` almost surely at `la`.
Let `lb`, `pure b ≤ lb ≤ 𝓝 b`, be a measurably generated interval generated filter such that
`μ` is finite at `lb` and `f x` has a finite limit `cb` almost surely at `lb`.
Then
`∫ x in va t..vb t, f x ∂μ - ∫ x in ua t..ub t, f x ∂μ =
  ∫ x in ub t..vb t, cb ∂μ - ∫ x in ua t..va t, ca ∂μ +
    o(∥∫ x in ua t..va t, (1:ℝ) ∂μ∥ + ∥∫ x in ub t..vb t, (1:ℝ) ∂μ∥)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.
 -/
lemma measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_of_tendsto_ae
  [tendsto_Ixx_class Ioc la la'] [is_measurably_generated la']
  [tendsto_Ixx_class Ioc lb lb'] [is_measurably_generated lb']
  {a b} (hfm : measurable f) (hab : interval_integrable f μ a b)
  (ha_lim : tendsto f (la' ⊓ μ.ae) (𝓝 ca)) (ha_fin : μ.finite_at_filter la') (ha_le : pure a ≤ la)
  (hb_lim : tendsto f (lb' ⊓ μ.ae) (𝓝 cb)) (hb_fin : μ.finite_at_filter lb') (hb_le : pure b ≤ lb)
  (hua : tendsto ua lt la) (hva : tendsto va lt la)
  (hub : tendsto ub lt lb) (hvb : tendsto vb lt lb) :
  is_o (λ t, (∫ x in va t..vb t, f x ∂μ) - (∫ x in ua t..ub t, f x ∂μ) -
    (∫ x in ub t..vb t, cb ∂μ - ∫ x in ua t..va t, ca ∂μ))
    (λ t, ∥∫ x in ua t..va t, (1:ℝ) ∂μ∥ + ∥∫ x in ub t..vb t, (1:ℝ) ∂μ∥) lt :=
begin
  refine
    ((measure_integral_sub_linear_is_o_of_tendsto_ae hfm ha_lim ha_fin hua hva).neg_left.add_add
    (measure_integral_sub_linear_is_o_of_tendsto_ae hfm hb_lim hb_fin hub hvb)).congr'
      _ (eventually_eq.refl _ _),
  have A : ∀ᶠ t in lt, interval_integrable f μ (ua t) (va t) :=
    ha_lim.eventually_interval_integrable_ae ha_fin hua hva,
  have A' : ∀ᶠ t in lt, interval_integrable f μ a (ua t) :=
    ha_lim.eventually_interval_integrable_ae ha_fin (tendsto_le_right ha_le tendsto_const_pure) hua,
  have B : ∀ᶠ t in lt, interval_integrable f μ (ub t) (vb t) :=
    hb_lim.eventually_interval_integrable_ae hb_fin hub hvb,
  have B' : ∀ᶠ t in lt, interval_integrable f μ b (ub t) :=
    hb_lim.eventually_interval_integrable_ae hb_fin (tendsto_le_right hb_le tendsto_const_pure) hub,
  filter_upwards [A, A', B, B'], simp only [mem_set_of_eq],
  intros t ua_va a_ua ub_vb b_ub,
  rw [← integral_interval_sub_interval_comm' hfm],
  { dsimp only [], abel },
  exacts [ub_vb, ua_va, b_ub.symm.trans $ hab.symm.trans a_ua]
end

/-- Fundamental theorem of calculus-1 for any measure.
Let f` be a measurable function integrable on `a..b`. Let `l` be one of `pure b`, `𝓝[Iic b] b`,
`𝓝[Ici b] b`, or `𝓝 b`. Suppose that `f x` has a finite limit `c` as `x` tends to `l ⊓ μ.ae`.
Then `∫ x in a..v, f x ∂μ - ∫ x in a..u, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)`
as `u` and `v` tend to `l`.

We use `pure b ≤ l ≤ 𝓝 b` together with two typeclasses as a fancy way to say
"let `l` be one of `pure b`, `𝓝[Iic b] b`, `𝓝[Ici b] b`, or `𝓝 b`". -/
lemma measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right
  [tendsto_Ixx_class Ioc lb lb'] [is_measurably_generated lb']
  {a b} (hfm : measurable f) (hab : interval_integrable f μ a b)
  (hf : tendsto f (lb' ⊓ μ.ae) (𝓝 c)) (hl : μ.finite_at_filter lb') (h_le : pure b ≤ lb)
  (hu : tendsto u lt lb) (hv : tendsto v lt lb) :
  is_o (λ t, ∫ x in a..v t, f x ∂μ - ∫ x in a..u t, f x ∂μ - ∫ x in u t..v t, c ∂μ)
    (λ t, ∫ x in u t..v t, (1:ℝ) ∂μ) lt :=
by simpa using measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_of_tendsto_ae
  hfm hab (flip tendsto_le_left (tendsto_bot : tendsto _ ⊥ (𝓝 0)) inf_le_left)
  μ.finite_at_bot (le_refl _) hf hl h_le tendsto_const_pure tendsto_const_pure hu hv

lemma measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left
  [tendsto_Ixx_class Ioc la la'] [is_measurably_generated la']
  {a b} (hfm : measurable f) (hab : interval_integrable f μ a b)
  (hf : tendsto f (la' ⊓ μ.ae) (𝓝 c)) (hl : μ.finite_at_filter la') (h_le : pure a ≤ la)
  (hu : tendsto u lt la) (hv : tendsto v lt la) :
  is_o (λ t, ∫ x in v t..b, f x ∂μ - ∫ x in u t..b, f x ∂μ + ∫ x in u t..v t, c ∂μ)
    (λ t, ∫ x in u t..v t, (1:ℝ) ∂μ) lt :=
by simpa using measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_of_tendsto_ae
  hfm hab hf hl h_le (flip tendsto_le_left (tendsto_bot : tendsto _ ⊥ (𝓝 0)) inf_le_left)
  μ.finite_at_bot (le_refl _) hu hv tendsto_const_pure tendsto_const_pure

#exit
end

/-!
### Fundamental theorem of calculus-1 for Lebesgue measure

In this section we restate theorems from the previous section for Lebesgue measure.
In particular, we prove that `∫ x in a..u, f x` is strictly differentiable in `u`
at `b` provided that `f` is integrable on `a..b` and is continuous at `b`.
-/

variables {f : ℝ → E} {c : E} {l : filter ℝ} {lb : filter β} [is_measurably_generated l]
  [is_interval_generated l] {a b z : ℝ}

/-- Fundamental theorem of calculus-1, local version. If `f` has a finite limit `c` at
`l ⊓ volume.ae`, where `l ≤ 𝓝 a` is a measurably generated interval generated filter (e.g., `𝓝 a`,
`𝓝[Ici a] a`, `𝓝[Iic a] a`), then `∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)`
as both `u` and `v` tend to `l`. -/
lemma integral_sub_linear_is_o_of_tendsto_ae (hfm : measurable f)
  (hf : tendsto f (l ⊓ volume.ae) (𝓝 c)) (ha : l ≤ 𝓝 a)
  {u v : β → ℝ} (hu : tendsto u lb l) (hv : tendsto v lb l) :
  is_o (λ t, (∫ x in u t..v t, f x) - (v t - u t) • c) (v - u) lb :=
by simpa [integral_const] using measure_integral_sub_linear_is_o_of_tendsto_ae hfm hf
  ((volume.finite_at_nhds _).filter_mono ha) hu hv

/-- Fundamental theorem of calculus-1. If `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `l`, where `l ≤ 𝓝 a` is a measurably generated interval generated filter
(e.g., `𝓝 a`, `𝓝[Ici a] a`, `𝓝[Iic a] a`), then
`∫ x in a..v, f x - ∫ x in a..u, f x = (v - u) • c + o(v - u)` as both `u` and `v` tend to `l`.

This is a generalization of the `has_strict_deriv_at` version of FTC-1 below. -/
lemma integral_sub_integral_sub_linear_is_o_of_tendsto_ae
  (hfm : measurable f) (hf : tendsto f (l ⊓ volume.ae) (𝓝 c))
  (hb : l ≤ 𝓝 b) (hb' : pure b ≤ l) (hab : interval_integrable f volume a b)
  {u v : β → ℝ} (hu : tendsto u lb l) (hv : tendsto v lb l) :
  is_o (λ t, (∫ x in a..v t, f x) - (∫ x in a..u t, f x) - (v t - u t) • c) (v - u) lb :=
by simpa only [integral_const, smul_eq_mul, mul_one] using
  measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae hfm hf
    ((volume.finite_at_nhds _).filter_mono hb) hb hb' hab hu hv

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b`, then `u ↦ ∫ x in a..u, f x` has derivative `c` at `b`
in the sense of strict differentiability. -/
lemma integral_has_strict_deriv_at_of_tendsto_ae (hfm : measurable f)
  (hfi : interval_integrable f volume a b) (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 c)) :
  has_strict_deriv_at (λ u, ∫ x in a..u, f x) c b :=
integral_sub_integral_sub_linear_is_o_of_tendsto_ae hfm hb (le_refl _) (pure_le_nhds _)
  hfi continuous_at_snd continuous_at_fst

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
limit `c` almost surely as `x` tends to `b` from the right, then `u ↦ ∫ x in a..u, f x` has
right derivative `c` at `b`. -/
lemma integral_has_deriv_within_at_Ici_of_tendsto_ae (hfm : measurable f)
  (hfi : interval_integrable f volume a b)
  (hb : tendsto f (𝓝[Ici b] b ⊓ volume.ae) (𝓝 c)) :
  has_deriv_within_at (λ u, ∫ x in a..u, f x) c (Ici b) b :=
have pure b ≤ 𝓝[Ici b] b := pure_le_nhds_within left_mem_Ici,
integral_sub_integral_sub_linear_is_o_of_tendsto_ae hfm hb inf_le_left this hfi
  (flip tendsto_le_right tendsto_const_pure this) tendsto_id

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the right at `b`, then `u ↦ ∫ x in a..u, f x` has right derivative `f b` at `b`. -/
lemma integral_has_deriv_within_at_Ici (hfm : measurable f) (hfi : interval_integrable f volume a b)
  (hb : continuous_within_at f (Ici b) b) :
  has_deriv_within_at (λ u, ∫ x in a..u, f x) (f b) (Ici b) b :=
integral_has_deriv_within_at_Ici_of_tendsto_ae hfm hfi (flip tendsto_le_left hb inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the left, then `u ↦ ∫ x in a..u, f x` has left
derivative `c` at `b`. -/
lemma integral_has_deriv_within_at_Iic_of_tendsto_ae (hfm : measurable f)
  (hfi : interval_integrable f volume a b)
  (hb : tendsto f (𝓝[Iic b] b ⊓ volume.ae) (𝓝 c)) :
  has_deriv_within_at (λ u, ∫ x in a..u, f x) c (Iic b) b :=
have pure b ≤ 𝓝[Iic b] b := pure_le_nhds_within right_mem_Iic,
integral_sub_integral_sub_linear_is_o_of_tendsto_ae hfm hb inf_le_left this hfi
  (flip tendsto_le_right tendsto_const_pure this) tendsto_id

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left at `b`, then `u ↦ ∫ x in a..u, f x` has left derivative `f b` at `b`. -/
lemma integral_has_deriv_within_at_Iic (hfm : measurable f) (hfi : interval_integrable f volume a b)
  (hb : continuous_within_at f (Iic b) b) :
  has_deriv_within_at (λ u, ∫ x in a..u, f x) (f b) (Iic b) b :=
integral_has_deriv_within_at_Iic_of_tendsto_ae hfm hfi (flip tendsto_le_left hb inf_le_left)

/-!
### Fundamental theorem of calculus-1: formulas for `(d/du) ∫ x in a..u, f x`

In this section we reformulate FTC-1 in terms of `deriv ... = ...` or `deriv_within ... = ...`.
-/

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
limit `c` almost surely as `x` tends to `b` from the right, then the right derivative
of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
lemma deriv_within_Ici_integral_of_tendsto_ae (hfm : measurable f)
  (hfi : interval_integrable f volume a b)
  (hb : tendsto f (𝓝[Ici b] b ⊓ volume.ae) (𝓝 c)) :
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
limit `c` almost surely as `x` tends to `b` from the left, then the left derivative
of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
lemma deriv_within_Iic_integral_of_tendsto_ae (hfm : measurable f)
  (hfi : interval_integrable f volume a b)
  (hb : tendsto f (𝓝[Iic b] b ⊓ volume.ae) (𝓝 c)) :
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

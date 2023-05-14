/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import measure_theory.measure.measure_space

/-!
# Measures positive on nonempty opens

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define a typeclass for measures that are positive on nonempty opens, see
`measure_theory.measure.is_open_pos_measure`. Examples include (additive) Haar measures, as well as
measures that have positive density with respect to a Haar measure. We also prove some basic facts
about these measures.

-/

open_locale topology ennreal measure_theory
open set function filter

namespace measure_theory

namespace measure

section basic

variables {X Y : Type*} [topological_space X] {m : measurable_space X}
  [topological_space Y] [t2_space Y] (μ ν : measure X)

/-- A measure is said to be `is_open_pos_measure` if it is positive on nonempty open sets. -/
class is_open_pos_measure : Prop :=
(open_pos : ∀ (U : set X), is_open U → U.nonempty → μ U ≠ 0)

variables [is_open_pos_measure μ] {s U : set X} {x : X}

lemma _root_.is_open.measure_ne_zero (hU : is_open U) (hne : U.nonempty) : μ U ≠ 0 :=
is_open_pos_measure.open_pos U hU hne

lemma _root_.is_open.measure_pos (hU : is_open U) (hne : U.nonempty) : 0 < μ U :=
(hU.measure_ne_zero μ hne).bot_lt

lemma _root_.is_open.measure_pos_iff (hU : is_open U) : 0 < μ U ↔ U.nonempty :=
⟨λ h, nonempty_iff_ne_empty.2 $ λ he, h.ne' $ he.symm ▸ measure_empty, hU.measure_pos μ⟩

lemma _root_.is_open.measure_eq_zero_iff (hU : is_open U) : μ U = 0 ↔ U = ∅ :=
by simpa only [not_lt, nonpos_iff_eq_zero, not_nonempty_iff_eq_empty]
  using not_congr (hU.measure_pos_iff μ)

lemma measure_pos_of_nonempty_interior (h : (interior s).nonempty) : 0 < μ s :=
(is_open_interior.measure_pos μ h).trans_le (measure_mono interior_subset)

lemma measure_pos_of_mem_nhds (h : s ∈ 𝓝 x) : 0 < μ s :=
measure_pos_of_nonempty_interior _ ⟨x, mem_interior_iff_mem_nhds.2 h⟩

lemma is_open_pos_measure_smul {c : ℝ≥0∞} (h : c ≠ 0) : is_open_pos_measure (c • μ) :=
⟨λ U Uo Une, mul_ne_zero h (Uo.measure_ne_zero μ Une)⟩

variables {μ ν}

protected lemma absolutely_continuous.is_open_pos_measure (h : μ ≪ ν) :
  is_open_pos_measure ν :=
⟨λ U ho hne h₀, ho.measure_ne_zero μ hne (h h₀)⟩

lemma _root_.has_le.le.is_open_pos_measure (h : μ ≤ ν) :
  is_open_pos_measure ν :=
h.absolutely_continuous.is_open_pos_measure

lemma _root_.is_open.eq_empty_of_measure_zero (hU : is_open U) (h₀ : μ U = 0) :
  U = ∅ :=
(hU.measure_eq_zero_iff μ).mp h₀

lemma interior_eq_empty_of_null (hs : μ s = 0) : interior s = ∅ :=
is_open_interior.eq_empty_of_measure_zero $ measure_mono_null interior_subset hs

/-- If two functions are a.e. equal on an open set and are continuous on this set, then they are
equal on this set. -/
lemma eq_on_open_of_ae_eq {f g : X → Y} (h : f =ᵐ[μ.restrict U] g) (hU : is_open U)
  (hf : continuous_on f U) (hg : continuous_on g U) :
  eq_on f g U :=
begin
  replace h := ae_imp_of_ae_restrict h,
  simp only [eventually_eq, ae_iff, not_imp] at h,
  have : is_open (U ∩ {a | f a ≠ g a}),
  { refine is_open_iff_mem_nhds.mpr (λ a ha, inter_mem (hU.mem_nhds ha.1) _),
    rcases ha with ⟨ha : a ∈ U, ha' : (f a, g a) ∈ (diagonal Y)ᶜ⟩,
    exact (hf.continuous_at (hU.mem_nhds ha)).prod_mk_nhds (hg.continuous_at (hU.mem_nhds ha))
      (is_closed_diagonal.is_open_compl.mem_nhds ha') },
  replace := (this.eq_empty_of_measure_zero h).le,
  exact λ x hx, not_not.1 (λ h, this ⟨hx, h⟩)
end

/-- If two continuous functions are a.e. equal, then they are equal. -/
lemma eq_of_ae_eq {f g : X → Y} (h : f =ᵐ[μ] g) (hf : continuous f) (hg : continuous g) : f = g :=
suffices eq_on f g univ, from funext (λ x, this trivial),
eq_on_open_of_ae_eq (ae_restrict_of_ae h) is_open_univ hf.continuous_on hg.continuous_on

lemma eq_on_of_ae_eq {f g : X → Y} (h : f =ᵐ[μ.restrict s] g) (hf : continuous_on f s)
  (hg : continuous_on g s) (hU : s ⊆ closure (interior s)) :
  eq_on f g s :=
have interior s ⊆ s, from interior_subset,
(eq_on_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset this h) is_open_interior
  (hf.mono this) (hg.mono this)).of_subset_closure hf hg this hU

variable (μ)

lemma _root_.continuous.ae_eq_iff_eq {f g : X → Y} (hf : continuous f) (hg : continuous g) :
  f =ᵐ[μ] g ↔ f = g :=
⟨λ h, eq_of_ae_eq h hf hg, λ h, h ▸ eventually_eq.rfl⟩

end basic

section linear_order

variables {X Y : Type*} [topological_space X] [linear_order X] [order_topology X]
  {m : measurable_space X} [topological_space Y] [t2_space Y] (μ : measure X)
  [is_open_pos_measure μ]

lemma measure_Ioi_pos [no_max_order X] (a : X) : 0 < μ (Ioi a) :=
is_open_Ioi.measure_pos μ nonempty_Ioi

lemma measure_Iio_pos [no_min_order X] (a : X) : 0 < μ (Iio a) :=
is_open_Iio.measure_pos μ nonempty_Iio

lemma measure_Ioo_pos [densely_ordered X] {a b : X} : 0 < μ (Ioo a b) ↔ a < b :=
(is_open_Ioo.measure_pos_iff μ).trans nonempty_Ioo

lemma measure_Ioo_eq_zero [densely_ordered X] {a b : X} : μ (Ioo a b) = 0 ↔ b ≤ a :=
(is_open_Ioo.measure_eq_zero_iff μ).trans (Ioo_eq_empty_iff.trans not_lt)

lemma eq_on_Ioo_of_ae_eq {a b : X} {f g : X → Y} (hfg : f =ᵐ[μ.restrict (Ioo a b)] g)
  (hf : continuous_on f (Ioo a b)) (hg : continuous_on g (Ioo a b)) : eq_on f g (Ioo a b) :=
eq_on_of_ae_eq hfg hf hg Ioo_subset_closure_interior

lemma eq_on_Ioc_of_ae_eq [densely_ordered X] {a b : X} {f g : X → Y}
  (hfg : f =ᵐ[μ.restrict (Ioc a b)] g) (hf : continuous_on f (Ioc a b))
  (hg : continuous_on g (Ioc a b)) : eq_on f g (Ioc a b) :=
eq_on_of_ae_eq hfg hf hg (Ioc_subset_closure_interior _ _)

lemma eq_on_Ico_of_ae_eq [densely_ordered X] {a b : X} {f g : X → Y}
  (hfg : f =ᵐ[μ.restrict (Ico a b)] g) (hf : continuous_on f (Ico a b))
  (hg : continuous_on g (Ico a b)) : eq_on f g (Ico a b) :=
eq_on_of_ae_eq hfg hf hg (Ico_subset_closure_interior _ _)

lemma eq_on_Icc_of_ae_eq [densely_ordered X] {a b : X} (hne : a ≠ b) {f g : X → Y}
  (hfg : f =ᵐ[μ.restrict (Icc a b)] g) (hf : continuous_on f (Icc a b))
  (hg : continuous_on g (Icc a b)) : eq_on f g (Icc a b) :=
eq_on_of_ae_eq hfg hf hg (closure_interior_Icc hne).symm.subset

end linear_order

end measure

end measure_theory

open measure_theory measure_theory.measure

namespace metric

variables {X : Type*} [pseudo_metric_space X] {m : measurable_space X} (μ : measure X)
  [is_open_pos_measure μ]

lemma measure_ball_pos (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ (ball x r) :=
is_open_ball.measure_pos μ (nonempty_ball.2 hr)

lemma measure_closed_ball_pos (x : X) {r : ℝ} (hr : 0 < r) :
  0 < μ (closed_ball x r) :=
(measure_ball_pos μ x hr).trans_le (measure_mono ball_subset_closed_ball)

end metric

namespace emetric

variables {X : Type*} [pseudo_emetric_space X] {m : measurable_space X} (μ : measure X)
  [is_open_pos_measure μ]

lemma measure_ball_pos (x : X) {r : ℝ≥0∞} (hr : r ≠ 0) : 0 < μ (ball x r) :=
is_open_ball.measure_pos μ ⟨x, mem_ball_self hr.bot_lt⟩

lemma measure_closed_ball_pos (x : X) {r : ℝ≥0∞} (hr : r ≠ 0) :
  0 < μ (closed_ball x r) :=
(measure_ball_pos μ x hr).trans_le (measure_mono ball_subset_closed_ball)

end emetric

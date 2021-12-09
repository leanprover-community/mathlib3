/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.measure.measure_space
import order.filter.ennreal

/-!
# Essential supremum and infimum
We define the essential supremum and infimum of a function `f : α → β` with respect to a measure
`μ` on `α`. The essential supremum is the infimum of the constants `c : β` such that `f x ≤ c`
almost everywhere.

TODO: The essential supremum of functions `α → ℝ≥0∞` is used in particular to define the norm in
the `L∞` space (see measure_theory/lp_space.lean).

There is a different quantity which is sometimes also called essential supremum: the least
upper-bound among measurable functions of a family of measurable functions (in an almost-everywhere
sense). We do not define that quantity here, which is simply the supremum of a map with values in
`α →ₘ[μ] β` (see measure_theory/ae_eq_fun.lean).

## Main definitions

* `ess_sup f μ := μ.ae.limsup f`
* `ess_inf f μ := μ.ae.liminf f`
-/

open measure_theory filter
open_locale ennreal measure_theory

variables {α β : Type*} {m : measurable_space α} {μ ν : measure α}

section conditionally_complete_lattice
variable [conditionally_complete_lattice β]

/-- Essential supremum of `f` with respect to measure `μ`: the smallest `c : β` such that
`f x ≤ c` a.e. -/
def ess_sup {m : measurable_space α} (f : α → β) (μ : measure α) := μ.ae.limsup f

/-- Essential infimum of `f` with respect to measure `μ`: the greatest `c : β` such that
`c ≤ f x` a.e. -/
def ess_inf {m : measurable_space α} (f : α → β) (μ : measure α) := μ.ae.liminf f

lemma ess_sup_congr_ae {f g : α → β} (hfg : f =ᵐ[μ] g) : ess_sup f μ = ess_sup g μ :=
limsup_congr hfg

lemma ess_inf_congr_ae {f g : α → β} (hfg : f =ᵐ[μ] g) :  ess_inf f μ = ess_inf g μ :=
@ess_sup_congr_ae α (order_dual β) _ _ _ _ _ hfg

end conditionally_complete_lattice

section complete_lattice
variable [complete_lattice β]

@[simp] lemma ess_sup_measure_zero {m : measurable_space α} {f : α → β} :
  ess_sup f (0 : measure α) = ⊥ :=
le_bot_iff.mp (Inf_le (by simp [set.mem_set_of_eq, eventually_le, ae_iff]))

@[simp] lemma ess_inf_measure_zero {m : measurable_space α} {f : α → β} :
  ess_inf f (0 : measure α) = ⊤ :=
@ess_sup_measure_zero α (order_dual β) _ _ _

lemma ess_sup_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) : ess_sup f μ ≤ ess_sup g μ :=
limsup_le_limsup hfg

lemma ess_inf_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) : ess_inf f μ ≤ ess_inf g μ :=
liminf_le_liminf hfg

lemma ess_sup_const (c : β) (hμ : μ ≠ 0) : ess_sup (λ x : α, c) μ = c :=
begin
  haveI hμ_ne_bot : μ.ae.ne_bot, { rwa [ne_bot_iff, ne.def, ae_eq_bot] },
  exact limsup_const c,
end

lemma ess_sup_le_of_ae_le {f : α → β} (c : β) (hf : f ≤ᵐ[μ] (λ _, c)) : ess_sup f μ ≤ c :=
begin
  refine (ess_sup_mono_ae hf).trans _,
  by_cases hμ : μ = 0,
  { simp [hμ], },
  { rwa ess_sup_const, },
end

lemma ess_inf_const (c : β) (hμ : μ ≠ 0) : ess_inf (λ x : α, c) μ = c :=
@ess_sup_const α (order_dual β) _ _ _ _ hμ

lemma le_ess_inf_of_ae_le {f : α → β} (c : β) (hf : (λ _, c) ≤ᵐ[μ] f) : c ≤ ess_inf f μ :=
@ess_sup_le_of_ae_le α (order_dual β) _ _ _ _ c hf

lemma ess_sup_const_bot : ess_sup (λ x : α, (⊥ : β)) μ = (⊥ : β) :=
limsup_const_bot

lemma ess_inf_const_top : ess_inf (λ x : α, (⊤ : β)) μ = (⊤ : β) :=
liminf_const_top

lemma order_iso.ess_sup_apply {m : measurable_space α} {γ} [complete_lattice γ]
  (f : α → β) (μ : measure α) (g : β ≃o γ) :
  g (ess_sup f μ) = ess_sup (λ x, g (f x)) μ :=
begin
  refine order_iso.limsup_apply g _ _ _ _,
  all_goals { is_bounded_default, },
end

lemma order_iso.ess_inf_apply {m : measurable_space α} {γ} [complete_lattice γ]
  (f : α → β) (μ : measure α) (g : β ≃o γ) :
  g (ess_inf f μ) = ess_inf (λ x, g (f x)) μ :=
@order_iso.ess_sup_apply α (order_dual β) _ _  (order_dual γ) _ _ _ g.dual

lemma ess_sup_mono_measure {f : α → β} (hμν : ν ≪ μ) : ess_sup f ν ≤ ess_sup f μ :=
begin
  refine limsup_le_limsup_of_le (measure.ae_le_iff_absolutely_continuous.mpr hμν) _ _,
  all_goals { is_bounded_default, },
end

lemma ess_inf_antitone_measure {f : α → β} (hμν : μ ≪ ν) : ess_inf f ν ≤ ess_inf f μ :=
begin
  refine liminf_le_liminf_of_le (measure.ae_le_iff_absolutely_continuous.mpr hμν) _ _,
  all_goals { is_bounded_default, },
end

lemma ess_sup_smul_measure {f : α → β} {c : ℝ≥0∞} (hc : c ≠ 0) :
  ess_sup f (c • μ) = ess_sup f μ :=
begin
  simp_rw ess_sup,
  suffices h_smul : (c • μ).ae = μ.ae, by rw h_smul,
  ext1,
  simp_rw mem_ae_iff,
  simp [hc],
end

end complete_lattice

section complete_linear_order
variable [complete_linear_order β]

lemma ae_lt_of_ess_sup_lt {f : α → β} {x : β} (hf : ess_sup f μ < x) : ∀ᵐ y ∂μ, f y < x :=
filter.eventually_lt_of_limsup_lt hf

lemma ae_lt_of_lt_ess_inf {f : α → β} {x : β} (hf : x < ess_inf f μ) : ∀ᵐ y ∂μ, x < f y :=
@ae_lt_of_ess_sup_lt α (order_dual β) _ _ _ _ _ hf

lemma ess_sup_indicator_eq_ess_sup_restrict [has_zero β] {s : set α}
  {f : α → β} (hf : 0 ≤ᵐ[μ.restrict s] f) (hs : measurable_set s) (hs_not_null : μ s ≠ 0) :
  ess_sup (s.indicator f) μ = ess_sup f (μ.restrict s) :=
begin
  refine le_antisymm _ (Limsup_le_Limsup_of_le (map_restrict_ae_le_map_indicator_ae hs)
    (by is_bounded_default) (by is_bounded_default)),
  refine Limsup_le_Limsup (by is_bounded_default) (by is_bounded_default) (λ c h_restrict_le, _),
  rw eventually_map at h_restrict_le ⊢,
  rw ae_restrict_iff' hs at h_restrict_le,
  have hc : 0 ≤ c,
  { suffices : ∃ x, 0 ≤ f x ∧ f x ≤ c, by { obtain ⟨x, hx⟩ := this, exact hx.1.trans hx.2, },
    refine frequently.exists _,
    { exact μ.ae, },
    rw [eventually_le, ae_restrict_iff' hs] at hf,
    have hs' : ∃ᵐ x ∂μ, x ∈ s,
    { contrapose! hs_not_null,
      rw [not_frequently, ae_iff] at hs_not_null,
      suffices : {a : α | ¬a ∉ s} = s, by rwa ← this,
      simp, },
    refine hs'.mp (hf.mp (h_restrict_le.mono (λ x hxs_imp_c hxf_nonneg hxs, _))),
    rw pi.zero_apply at hxf_nonneg,
    exact ⟨hxf_nonneg hxs, hxs_imp_c hxs⟩, },
  refine h_restrict_le.mono (λ x hxc, _),
  by_cases hxs : x ∈ s,
  { simpa [hxs] using hxc hxs, },
  { simpa [hxs] using hc, },
end

end complete_linear_order

namespace ennreal

variables {f : α → ℝ≥0∞}

lemma ae_le_ess_sup (f : α → ℝ≥0∞) : ∀ᵐ y ∂μ, f y ≤ ess_sup f μ :=
eventually_le_limsup f

@[simp] lemma ess_sup_eq_zero_iff : ess_sup f μ = 0 ↔ f =ᵐ[μ] 0 :=
limsup_eq_zero_iff

lemma ess_sup_const_mul {a : ℝ≥0∞} : ess_sup (λ (x : α), a * (f x)) μ = a * ess_sup f μ :=
limsup_const_mul

lemma ess_sup_add_le (f g : α → ℝ≥0∞) : ess_sup (f + g) μ ≤ ess_sup f μ + ess_sup g μ :=
limsup_add_le f g

lemma ess_sup_liminf_le {ι} [encodable ι] [linear_order ι] (f : ι → α → ℝ≥0∞) :
  ess_sup (λ x, at_top.liminf (λ n, f n x)) μ ≤ at_top.liminf (λ n, ess_sup (λ x, f n x) μ) :=
by { simp_rw ess_sup, exact ennreal.limsup_liminf_le_liminf_limsup (λ a b, f b a), }

end ennreal

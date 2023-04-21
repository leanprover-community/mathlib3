/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.constructions.borel_space
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

open measure_theory filter set topological_space
open_locale ennreal measure_theory nnreal

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
@ess_sup_congr_ae α βᵒᵈ _ _ _ _ _ hfg

@[simp] lemma ess_sup_const' [μ.ae.ne_bot] (c : β) : ess_sup (λ x : α, c) μ = c := limsup_const _
@[simp] lemma ess_inf_const' [μ.ae.ne_bot] (c : β) : ess_inf (λ x : α, c) μ = c := liminf_const _

lemma ess_sup_const (c : β) (hμ : μ ≠ 0) : ess_sup (λ x : α, c) μ = c :=
by { rw ←ae_ne_bot at hμ, exactI ess_sup_const' _ }

lemma ess_inf_const (c : β) (hμ : μ ≠ 0) : ess_inf (λ x : α, c) μ = c :=
by { rw ←ae_ne_bot at hμ, exactI ess_inf_const' _ }

end conditionally_complete_lattice

section conditionally_complete_linear_order
variables [conditionally_complete_linear_order β] {x : β} {f : α → β}

lemma ess_sup_eq_Inf {m : measurable_space α} (μ : measure α) (f : α → β) :
  ess_sup f μ = Inf {a | μ {x | a < f x} = 0} :=
by { dsimp [ess_sup, limsup, Limsup], simp only [ae_iff, not_le] }

lemma ess_inf_eq_Sup {m : measurable_space α} (μ : measure α) (f : α → β) :
  ess_inf f μ = Sup {a | μ {x | f x < a} = 0} :=
by { dsimp [ess_inf, liminf, Liminf], simp only [ae_iff, not_le] }

lemma ae_lt_of_ess_sup_lt (hx : ess_sup f μ < x)
  (hf : is_bounded_under (≤) μ.ae f . is_bounded_default) : ∀ᵐ y ∂μ, f y < x :=
eventually_lt_of_limsup_lt hx hf

lemma ae_lt_of_lt_ess_inf (hx : x < ess_inf f μ)
  (hf : is_bounded_under (≥) μ.ae f . is_bounded_default) : ∀ᵐ y ∂μ, x < f y :=
eventually_lt_of_lt_liminf hx hf

variables [topological_space β] [first_countable_topology β] [order_topology β]

lemma ae_le_ess_sup (hf : is_bounded_under (≤) μ.ae f . is_bounded_default) :
  ∀ᵐ y ∂μ, f y ≤ ess_sup f μ :=
eventually_le_limsup hf

lemma ae_ess_inf_le (hf : is_bounded_under (≥) μ.ae f . is_bounded_default) :
  ∀ᵐ y ∂μ, ess_inf f μ ≤ f y :=
eventually_liminf_le hf

lemma meas_ess_sup_lt (hf : is_bounded_under (≤) μ.ae f . is_bounded_default) :
  μ {y | ess_sup f μ < f y} = 0 :=
by { simp_rw ←not_le, exact ae_le_ess_sup hf }

lemma meas_lt_ess_inf (hf : is_bounded_under (≥) μ.ae f . is_bounded_default) :
  μ {y | f y < ess_inf f μ} = 0 :=
by { simp_rw ←not_le, exact ae_ess_inf_le hf }

lemma ae_le_of_le_ess_inf [no_min_order β] (hx : x ≤ ess_inf f μ)
  (hf : is_bounded_under (≥) μ.ae f . is_bounded_default) : ∀ᵐ y ∂μ, x ≤ f y :=
@ae_le_of_ess_sup_le α βᵒᵈ _ _ _ _ _ _ _ _ _ _ hx hf

lemma meas_lt_of_ess_sup_le [no_max_order β] (hx : ess_sup f μ ≤ x)
  (hf : is_bounded_under (≤) μ.ae f . is_bounded_default) : μ {y | x < f y} = 0 :=
by { simp_rw ←not_le, exact ae_le_of_ess_sup_le hx hf }

lemma meas_lt_of_le_ess_inf [no_min_order β] (hx : x ≤ ess_inf f μ)
  (hf : is_bounded_under (≥) μ.ae f . is_bounded_default) : μ {y | f y < x} = 0 :=
by { simp_rw ←not_le, exact ae_le_of_le_ess_inf hx hf }

end conditionally_complete_linear_order

section complete_lattice
variable [complete_lattice β]

@[simp] lemma ess_sup_measure_zero {m : measurable_space α} {f : α → β} :
  ess_sup f (0 : measure α) = ⊥ :=
le_bot_iff.mp (Inf_le (by simp [set.mem_set_of_eq, eventually_le, ae_iff]))

@[simp] lemma ess_inf_measure_zero {m : measurable_space α} {f : α → β} :
  ess_inf f (0 : measure α) = ⊤ :=
@ess_sup_measure_zero α βᵒᵈ _ _ _

lemma ess_sup_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) : ess_sup f μ ≤ ess_sup g μ :=
limsup_le_limsup hfg

lemma ess_inf_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) : ess_inf f μ ≤ ess_inf g μ :=
liminf_le_liminf hfg

lemma ess_sup_le_of_ae_le {f : α → β} (c : β) (hf : f ≤ᵐ[μ] (λ _, c)) : ess_sup f μ ≤ c :=
begin
  refine (ess_sup_mono_ae hf).trans _,
  by_cases hμ : μ = 0,
  { simp [hμ], },
  { rwa ess_sup_const, },
end

lemma le_ess_inf_of_ae_le {f : α → β} (c : β) (hf : (λ _, c) ≤ᵐ[μ] f) : c ≤ ess_inf f μ :=
@ess_sup_le_of_ae_le α βᵒᵈ _ _ _ _ c hf

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
@order_iso.ess_sup_apply α βᵒᵈ _ _  γᵒᵈ _ _ _ g.dual

lemma ess_sup_mono_measure {f : α → β} (hμν : ν ≪ μ) : ess_sup f ν ≤ ess_sup f μ :=
begin
  refine limsup_le_limsup_of_le (measure.ae_le_iff_absolutely_continuous.mpr hμν) _ _,
  all_goals { is_bounded_default, },
end

lemma ess_sup_mono_measure' {α : Type*} {β : Type*} {m : measurable_space α}
  {μ ν : measure_theory.measure α} [complete_lattice β] {f : α → β} (hμν : ν ≤ μ) :
  ess_sup f ν ≤ ess_sup f μ := ess_sup_mono_measure (measure.absolutely_continuous_of_le hμν)

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

section topological_space

variables {γ : Type*} {mγ : measurable_space γ} {f : α → γ} {g : γ → β}

include mγ

lemma ess_sup_comp_le_ess_sup_map_measure (hf : ae_measurable f μ) :
  ess_sup (g ∘ f) μ ≤ ess_sup g (measure.map f μ) :=
begin
  refine Limsup_le_Limsup_of_le (λ t, _) (by is_bounded_default) (by is_bounded_default),
  simp_rw filter.mem_map,
  have : (g ∘ f) ⁻¹' t = f ⁻¹' (g ⁻¹' t), by { ext1 x, simp_rw set.mem_preimage, },
  rw this,
  exact λ h, mem_ae_of_mem_ae_map hf h,
end

lemma _root_.measurable_embedding.ess_sup_map_measure (hf : measurable_embedding f) :
  ess_sup g (measure.map f μ) = ess_sup (g ∘ f) μ :=
begin
  refine le_antisymm _ (ess_sup_comp_le_ess_sup_map_measure hf.measurable.ae_measurable),
  refine Limsup_le_Limsup (by is_bounded_default) (by is_bounded_default) (λ c h_le, _),
  rw eventually_map at h_le ⊢,
  exact hf.ae_map_iff.mpr h_le,
end

variables [measurable_space β] [topological_space β] [second_countable_topology β]
  [order_closed_topology β] [opens_measurable_space β]

lemma ess_sup_map_measure_of_measurable (hg : measurable g) (hf : ae_measurable f μ) :
  ess_sup g (measure.map f μ) = ess_sup (g ∘ f) μ :=
begin
  refine le_antisymm _ (ess_sup_comp_le_ess_sup_map_measure hf),
  refine Limsup_le_Limsup (by is_bounded_default) (by is_bounded_default) (λ c h_le, _),
  rw eventually_map at h_le ⊢,
  rw ae_map_iff hf (measurable_set_le hg measurable_const),
  exact h_le,
end

lemma ess_sup_map_measure (hg : ae_measurable g (measure.map f μ)) (hf : ae_measurable f μ) :
  ess_sup g (measure.map f μ) = ess_sup (g ∘ f) μ :=
begin
  rw [ess_sup_congr_ae hg.ae_eq_mk, ess_sup_map_measure_of_measurable hg.measurable_mk hf],
  refine ess_sup_congr_ae _,
  have h_eq := ae_of_ae_map hf hg.ae_eq_mk,
  rw ← eventually_eq at h_eq,
  exact h_eq.symm,
end

omit mγ

end topological_space

end complete_lattice

section complete_linear_order
variable [complete_linear_order β]

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
  { rsuffices ⟨x, hx⟩ : ∃ x, 0 ≤ f x ∧ f x ≤ c, from hx.1.trans hx.2,
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

lemma ess_sup_mul_le (f g : α → ℝ≥0∞) : ess_sup (f * g) μ ≤ ess_sup f μ * ess_sup g μ :=
limsup_mul_le f g

lemma ess_sup_add_le (f g : α → ℝ≥0∞) : ess_sup (f + g) μ ≤ ess_sup f μ + ess_sup g μ :=
limsup_add_le f g

lemma ess_sup_liminf_le {ι} [countable ι] [linear_order ι] (f : ι → α → ℝ≥0∞) :
  ess_sup (λ x, at_top.liminf (λ n, f n x)) μ ≤ at_top.liminf (λ n, ess_sup (λ x, f n x) μ) :=
by { simp_rw ess_sup, exact ennreal.limsup_liminf_le_liminf_limsup (λ a b, f b a), }

lemma coe_ess_sup {f : α → ℝ≥0} (hf : is_bounded_under (≤) μ.ae f) :
  (↑(ess_sup f μ) : ℝ≥0∞) = ess_sup (λ x, f x) μ :=
(ennreal.coe_Inf $ by exact hf).trans $ eq_of_forall_le_iff $ λ r,
  by simp [ess_sup, limsup, Limsup, eventually_map, ennreal.forall_ennreal]

end ennreal

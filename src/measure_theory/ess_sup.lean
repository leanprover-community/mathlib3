/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.measure_space
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

open measure_theory
open_locale ennreal

variables {α β : Type*} [measurable_space α] {μ : measure α}

section conditionally_complete_lattice
variable [conditionally_complete_lattice β]

/-- Essential supremum of `f` with respect to measure `μ`: the smallest `c : β` such that
`f x ≤ c` a.e. -/
def ess_sup (f : α → β) (μ : measure α) := μ.ae.limsup f

/-- Essential infimum of `f` with respect to measure `μ`: the greatest `c : β` such that
`c ≤ f x` a.e. -/
def ess_inf (f : α → β) (μ : measure α) := μ.ae.liminf f

lemma ess_sup_congr_ae {f g : α → β} (hfg : f =ᵐ[μ] g) : ess_sup f μ = ess_sup g μ :=
filter.limsup_congr hfg

lemma ess_inf_congr_ae {f g : α → β} (hfg : f =ᵐ[μ] g) :  ess_inf f μ = ess_inf g μ :=
@ess_sup_congr_ae α (order_dual β) _ _ _ _ _ hfg

end conditionally_complete_lattice

section complete_lattice
variable [complete_lattice β]

@[simp] lemma ess_sup_measure_zero {f : α → β} : ess_sup f 0 = ⊥ :=
le_bot_iff.mp (Inf_le (by simp [set.mem_set_of_eq, filter.eventually_le, ae_iff]))

@[simp] lemma ess_inf_measure_zero {f : α → β} : ess_inf f 0 = ⊤ :=
@ess_sup_measure_zero α (order_dual β) _ _ _

lemma ess_sup_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) : ess_sup f μ ≤ ess_sup g μ :=
filter.limsup_le_limsup hfg

lemma ess_inf_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) : ess_inf f μ ≤ ess_inf g μ :=
filter.liminf_le_liminf hfg

lemma ess_sup_const (c : β) (hμ : μ ≠ 0) : ess_sup (λ x : α, c) μ = c :=
begin
  haveI hμ_ne_bot : μ.ae.ne_bot := by rwa [filter.ne_bot_iff, ne.def, ae_eq_bot],
  exact filter.limsup_const c,
end

lemma ess_inf_const (c : β) (hμ : μ ≠ 0) : ess_inf (λ x : α, c) μ = c :=
@ess_sup_const α (order_dual β) _ _ _ _ hμ

lemma ess_sup_const_bot : ess_sup (λ x : α, (⊥ : β)) μ = (⊥ : β) :=
filter.limsup_const_bot

lemma ess_inf_const_top : ess_inf (λ x : α, (⊤ : β)) μ = (⊤ : β) :=
filter.liminf_const_top

lemma order_iso.ess_sup_apply {γ} [complete_lattice γ] (f : α → β) (μ : measure α)
  (g : β ≃o γ) :
  g (ess_sup f μ) = ess_sup (λ x, g (f x)) μ :=
begin
  refine order_iso.limsup_apply g _ _ _ _,
  all_goals { by filter.is_bounded_default},
end

lemma order_iso.ess_inf_apply {γ} [complete_lattice γ] (f : α → β) (μ : measure α)
  (g : β ≃o γ) :
  g (ess_inf f μ) = ess_inf (λ x, g (f x)) μ :=
@order_iso.ess_sup_apply α (order_dual β) _ _  (order_dual γ) _ _ _ g.dual

end complete_lattice

section complete_linear_order
variable [complete_linear_order β]

lemma ae_lt_of_ess_sup_lt {f : α → β} {x : β} (hf : ess_sup f μ < x) : ∀ᵐ y ∂μ, f y < x :=
filter.eventually_lt_of_limsup_lt hf

lemma ae_lt_of_lt_ess_inf {f : α → β} {x : β} (hf : x < ess_inf f μ) : ∀ᵐ y ∂μ, x < f y :=
@ae_lt_of_ess_sup_lt α (order_dual β) _ _ _ _ _ hf

end complete_linear_order

namespace ennreal

lemma ae_le_ess_sup (f : α → ℝ≥0∞) : ∀ᵐ y ∂μ, f y ≤ ess_sup f μ :=
eventually_le_limsup f

@[simp] lemma ess_sup_eq_zero_iff {f : α → ℝ≥0∞} : ess_sup f μ = 0 ↔ f =ᵐ[μ] 0 :=
limsup_eq_zero_iff

lemma ess_sup_const_mul {f : α → ℝ≥0∞} {a : ℝ≥0∞} :
  ess_sup (λ (x : α), a * (f x)) μ = a * ess_sup f μ :=
limsup_const_mul

lemma ess_sup_add_le (f g : α → ℝ≥0∞) : ess_sup (f + g) μ ≤ ess_sup f μ + ess_sup g μ :=
limsup_add_le f g

lemma ess_sup_liminf_le {ι} [encodable ι] [linear_order ι] (f : ι → α → ℝ≥0∞) :
  ess_sup (λ x, filter.at_top.liminf (λ n, f n x)) μ
    ≤ filter.at_top.liminf (λ n, ess_sup (λ x, f n x) μ) :=
by { simp_rw ess_sup, exact ennreal.limsup_liminf_le_liminf_limsup (λ a b, f b a), }

end ennreal

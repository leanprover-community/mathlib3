/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.measure_space

/-!
# Essential supremum and infimum

We define the essential supremum and infimum of a function `f : α → β` with respect to a measure
`μ` on `α`. The essential supremum is the infimum of the constants `c : β` such that `f x ≤ c`
almost everywhere.

TODO: The essential supremum of functions `α → ennreal` is used in particular to define the norm in
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

lemma ess_sup_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) :  ess_sup f μ ≤ ess_sup g μ :=
filter.limsup_mono hfg

lemma ess_inf_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) : ess_inf f μ ≤ ess_inf g μ :=
filter.liminf_mono hfg

lemma ess_sup_const (c : β) (hμ : μ ≠ 0) : ess_sup (λ x : α, c) μ = c :=
begin
  have hμ_ne_bot : μ.ae.ne_bot, by rwa [filter.ne_bot, ne.def, ae_eq_bot],
  exact @filter.limsup_const _ _ _ μ.ae hμ_ne_bot c,
end

lemma ess_inf_const (c : β) (hμ : μ ≠ 0) : ess_inf (λ x : α, c) μ = c :=
@ess_sup_const α (order_dual β) _ _ _ _ hμ

lemma order_iso.ess_sup_apply {γ} [complete_lattice γ] (f : α → β) (μ : measure α)
  (g : β ≃o γ) :
  g (ess_sup f μ) = ess_sup (λ x, g (f x)) μ :=
order_iso.limsup_apply g

lemma order_iso.ess_inf_apply {γ} [complete_lattice γ] (f : α → β) (μ : measure α)
  (g : β ≃o γ) :
  g (ess_inf f μ) = ess_inf (λ x, g (f x)) μ :=
@order_iso.ess_sup_apply α (order_dual β) _ _  (order_dual γ) _ _ _ g.dual

end complete_lattice

section complete_linear_order
variable [complete_linear_order β]

lemma ae_lt_of_ess_sup_lt {f : α → β} {x : β} (hf : ess_sup f μ < x) : ∀ᵐ y ∂μ, f y < x :=
filter.eventually_lt_of_limsup_lt' hf

lemma ae_lt_of_lt_ess_inf {f : α → β} {x : β} (hf : x < ess_inf f μ) : ∀ᵐ y ∂μ, x < f y :=
@ae_lt_of_ess_sup_lt α (order_dual β) _ _ _ _ _ hf

end complete_linear_order

section ennreal

open filter
lemma ennreal.eventually_le_limsup {α} {f : filter α} [countable_Inter_filter f] (u : α → ennreal) :
  ∀ᶠ y in f, u y ≤ f.limsup u :=
begin
  by_cases hx_top : f.limsup u = ⊤,
  { simp_rw hx_top,
    exact eventually_of_forall (λ a, le_top), },
  have h_forall_le : ∀ᶠ y in f, ∀ n : ℕ, u y < f.limsup u + (1:ennreal)/n,
  { rw eventually_countable_forall,
    refine λ n, eventually_lt_of_limsup_lt _,
    nth_rewrite 0 ←add_zero (f.limsup u),
    exact (ennreal.add_lt_add_iff_left (lt_top_iff_ne_top.mpr hx_top)).mpr (by simp), },
  refine h_forall_le.mono (λ y hy, ennreal.le_of_forall_epsilon_le (λ r hr_pos hx_top,_)),
  have hr_ne_zero : (r : ennreal) ≠ 0,
  { rw [ne.def, ennreal.coe_eq_zero],
    exact (ne_of_lt hr_pos).symm, },
  cases (ennreal.exists_inv_nat_lt hr_ne_zero) with i hi,
  refine le_trans (le_of_lt (hy i)) (add_le_add_left (le_of_lt _) (f.limsup u)),
  rwa [ennreal.div_def, one_mul],
end

lemma ennreal.ae_le_ess_sup (f : α → ennreal) : ∀ᵐ y ∂μ, f y ≤ ess_sup f μ :=
ennreal.eventually_le_limsup f

lemma ennreal.limsup_const_mul {α} {f : filter α} [ne_bot f] {u : α → ennreal} {a : ennreal}
  (ha_top : a ≠ ⊤) :
  f.limsup (λ (x : α), a * (u x)) = a * f.limsup u :=
begin
  by_cases ha_zero : a = 0,
  { simp [ha_zero, limsup_const (0 : ennreal)], },
  let g := λ x : ennreal, a * x,
  have hg_bij : function.bijective g,
  from function.bijective_iff_has_inverse.mpr ⟨(λ x, a⁻¹ * x),
    ⟨λ x, by simp [←mul_assoc, ennreal.inv_mul_cancel ha_zero ha_top],
    λ x, by simp [g, ←mul_assoc, ennreal.mul_inv_cancel ha_zero ha_top]⟩⟩,
  have hg_mono : strict_mono g,
  from strict_mono_of_monotone_of_injective
    (λ _ _ _, by rwa ennreal.mul_le_mul_left ha_zero ha_top) hg_bij.1,
  let g_iso := strict_mono.order_iso_of_surjective g hg_mono hg_bij.2,
  exact (order_iso.limsup_apply g_iso).symm,
end

lemma ennreal.ess_sup_const_mul {f : α → ennreal} {a : ennreal} (ha_top : a ≠ ⊤) :
  ess_sup (λ (x : α), a * (f x)) μ = a * ess_sup f μ :=
begin
  by_cases hμ : μ = 0,
  { simp [hμ], },
  have hμ_ne_bot : μ.ae.ne_bot, by rwa [filter.ne_bot, ne.def, ae_eq_bot],
  exact @ennreal.limsup_const_mul α μ.ae hμ_ne_bot f a ha_top,
end

lemma ennreal.limsup_add_le {α} (f : filter α) [countable_Inter_filter f] (u v : α → ennreal) :
  f.limsup (u + v) ≤ f.limsup u + f.limsup v :=
Inf_le ((ennreal.eventually_le_limsup u).mp ((ennreal.eventually_le_limsup v).mono
  (λ _ hxg hxf, add_le_add hxf hxg)))

lemma ennreal.ess_sup_add_le (f g : α → ennreal) : ess_sup (f + g) μ ≤ ess_sup f μ + ess_sup g μ :=
ennreal.limsup_add_le μ.ae f g

end ennreal

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

* `ess_sup f μ := Inf {c : β | f ≤ᵐ[μ] (λ x, c)}`
* `ess_inf f μ := Sup {c : β | (λ x, c) ≤ᵐ[μ] f}`

-/

open measure_theory

variables {α β : Type*} [measurable_space α] {μ : measure α}

section has_le
variable [has_le β]

/-- Essential supremum of `f` with respect to measure `μ`: the smallest `c : β` such that
`f x ≤ c` a.e. -/
def ess_sup [has_Inf β] (f : α → β) (μ : measure α) :=
Inf {c : β | f ≤ᵐ[μ] (λ x, c)}

/-- Essential infimum of `f` with respect to measure `μ`: the greatest `c : β` such that
`c ≤ f x` a.e. -/
def ess_inf [has_Sup β] (f : α → β) (μ : measure α) :=
Sup {c : β | (λ x, c) ≤ᵐ[μ] f}

lemma ess_sup_congr_ae [has_Inf β] {f g : α → β} (hfg : f =ᵐ[μ] g) : ess_sup f μ = ess_sup g μ :=
begin
  simp_rw ess_sup,
  congr,
  ext c,
  exact filter.eventually_congr (hfg.mono (λ x hx, by rw hx)),
end

lemma ess_inf_congr_ae [has_Sup β] {f g : α → β} (hfg : f =ᵐ[μ] g) :  ess_inf f μ = ess_inf g μ :=
@ess_sup_congr_ae α (order_dual β) _ _ _ _ _ _ hfg

end has_le

section complete_lattice
variable [complete_lattice β]

@[simp] lemma ess_sup_measure_zero {f : α → β} : ess_sup f 0 = ⊥ :=
le_bot_iff.mp (Inf_le (by simp [set.mem_set_of_eq, filter.eventually_le, ae_iff]))

@[simp] lemma ess_inf_measure_zero {f : α → β} : ess_inf f 0 = ⊤ :=
@ess_sup_measure_zero α (order_dual β) _ _ _

lemma ess_sup_mono {f g : α → β} (hfg : f ≤ g) : ess_sup f μ ≤ ess_sup g μ :=
Inf_le_Inf_of_forall_exists_le (λ x hx, ⟨x, ⟨hx.mono (λ y hy, le_trans (hfg y) hy), le_refl x⟩⟩)

lemma ess_inf_mono {f g : α → β} (hfg : f ≤ g) : ess_inf f μ ≤ ess_inf g μ :=
@ess_sup_mono α (order_dual β) _ _ _ _ _ (order_dual.to_dual_le_to_dual.mpr hfg)

lemma ess_sup_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) :  ess_sup f μ ≤ ess_sup g μ :=
Inf_le_Inf_of_forall_exists_le (λ x hx, ⟨x, ⟨hfg.trans hx, le_refl x⟩⟩)

lemma ess_inf_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) : ess_inf f μ ≤ ess_inf g μ :=
Sup_le_Sup_of_forall_exists_le (λ x hx, ⟨x, ⟨hx.trans hfg, le_refl x⟩⟩)

lemma ess_sup_const (c : β) (hμ : μ ≠ 0) : ess_sup (λ x : α, c) μ = c :=
begin
  rw ess_sup,
  refine le_antisymm _ _,
  { refine Inf_le _,
    rw set.mem_set_of_eq, },
  { refine le_Inf (λ a ha, _),
    rw set.mem_set_of_eq at ha,
    have h_ae_ne_bot : μ.ae.ne_bot, by rwa [filter.ne_bot, ne.def, ae_eq_bot],
    exact (@filter.eventually.exists _ _ _ h_ae_ne_bot ha).some_spec, },
end

lemma ess_inf_const (c : β) (hμ : μ ≠ 0) : ess_inf (λ x : α, c) μ = c :=
@ess_sup_const α (order_dual β) _ _ _ _ hμ

end complete_lattice

section complete_linear_order
variable [complete_linear_order β]

lemma ae_lt_of_ess_sup_lt {f : α → β} {x : β} (hf : ess_sup f μ < x) : ∀ᵐ y ∂μ, f y < x :=
begin
  rw [ess_sup, Inf_lt_iff] at hf,
  rcases hf with ⟨y, ⟨hy, hy_lt_x⟩⟩,
  exact hy.mono (λ z hz, lt_of_le_of_lt hz hy_lt_x),
end

lemma ae_lt_of_lt_ess_inf {f : α → β} {x : β} (hf : x < ess_inf f μ) : ∀ᵐ y ∂μ, x < f y :=
@ae_lt_of_ess_sup_lt α (order_dual β) _ _ _ _ _ hf

lemma order_iso.ess_sup_le {γ} [complete_lattice γ] {f : α → β} (g : β ≃o γ) :
  g (ess_sup f μ) ≤ ess_sup (λ x, g (f x)) μ :=
begin
  refine le_Inf (λ x hx, _),
  rw [(g.symm.symm_apply_apply x).symm, g.symm_symm],
  refine g.monotone (Inf_le _),
  refine hx.mono (λ y hy, _),
  rw (g.symm_apply_apply (f y)).symm,
  exact g.symm.monotone hy,
end

lemma order_iso.ess_sup_apply {γ} [complete_linear_order γ] (f : α → β) (μ : measure α)
  (g : β ≃o γ) :
  g (ess_sup f μ) = ess_sup (λ x, g (f x)) μ :=
begin
  refine le_antisymm (order_iso.ess_sup_le g) _,
  rw [←(g.symm.symm_apply_apply (ess_sup (λ (x : α), g (f x)) μ)), g.symm_symm],
  refine g.monotone _,
  have hf : f = λ i, g.symm (g (f i)), from funext (λ i, (g.symm_apply_apply (f i)).symm),
  nth_rewrite 0 hf,
  exact g.symm.ess_sup_le,
end

lemma order_iso.ess_inf_apply {γ} [complete_linear_order γ] (f : α → β) (μ : measure α)
  (g : β ≃o γ) :
  g (ess_inf f μ) = ess_inf (λ x, g (f x)) μ :=
@order_iso.ess_sup_apply α (order_dual β) _ _  (order_dual γ) _ _ _ g.dual

end complete_linear_order

section ennreal

lemma ennreal.ae_le_of_ess_sup_le {f : α → ennreal} {x : ennreal} (hf : ess_sup f μ ≤ x) :
  ∀ᵐ y ∂μ, f y ≤ x :=
begin
  by_cases hx_top : x = ⊤,
  { simp_rw hx_top,
    exact ae_of_all _ (λ a, le_top), },
  have h_forall_le : ∀ᵐ y ∂μ, ∀ n : ℕ, f y < x + (1:ennreal)/n,
  { rw ae_all_iff,
    refine λ n, ae_lt_of_ess_sup_lt (lt_of_le_of_lt hf _),
    nth_rewrite 0 ←add_zero x,
    exact (ennreal.add_lt_add_iff_left (lt_top_iff_ne_top.mpr hx_top)).mpr (by simp), },
  refine h_forall_le.mono (λ y hy, ennreal.le_of_forall_epsilon_le (λ r hr_pos hx_top,_)),
  have hr_ne_zero : (r : ennreal) ≠ 0,
  { rw [ne.def, ennreal.coe_eq_zero],
    exact (ne_of_lt hr_pos).symm, },
  cases (ennreal.exists_inv_nat_lt hr_ne_zero) with i hi,
  refine le_trans (le_of_lt (hy i)) (add_le_add_left (le_of_lt _) x),
  rwa [ennreal.div_def, one_mul],
end

lemma ennreal.ae_le_ess_sup (f : α → ennreal) : ∀ᵐ x ∂μ, f x ≤ ess_sup f μ :=
ennreal.ae_le_of_ess_sup_le (le_refl (ess_sup f μ))

lemma ennreal.ess_sup_const_mul {f : α → ennreal} {a : ennreal} (ha_top : a ≠ ⊤) :
  ess_sup (λ (x : α), a * (f x)) μ = a * ess_sup f μ :=
begin
  by_cases hμ : μ = 0,
  { simp [hμ], },
  by_cases ha_zero : a = 0,
  { simp [ha_zero, ess_sup_const (0 : ennreal) hμ], },
  let g := λ x : ennreal, a * x,
  have hg_bij : function.bijective g,
  from function.bijective_iff_has_inverse.mpr ⟨(λ x, a⁻¹ * x),
    ⟨λ x, by simp [←mul_assoc, ennreal.inv_mul_cancel ha_zero ha_top],
    λ x, by simp [g, ←mul_assoc, ennreal.mul_inv_cancel ha_zero ha_top]⟩⟩,
  have hg_mono : strict_mono g,
  from strict_mono_of_monotone_of_injective
    (λ _ _ _, by rwa ennreal.mul_le_mul_left ha_zero ha_top) hg_bij.1,
  let g_iso := strict_mono.order_iso_of_surjective g hg_mono hg_bij.2,
  exact (order_iso.ess_sup_apply f μ g_iso).symm,
end

lemma ennreal.ess_sup_add_le {f g : α → ennreal} : ess_sup (f + g) μ ≤ ess_sup f μ + ess_sup g μ :=
Inf_le ((ennreal.ae_le_ess_sup f).mp ((ennreal.ae_le_ess_sup g).mono
  (λ _ hxg hxf, add_le_add hxf hxg)))

end ennreal

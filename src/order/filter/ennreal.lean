/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import data.real.ennreal
import order.filter.countable_Inter
import order.liminf_limsup

/-!
# Order properties of extended non-negative reals

This file compiles filter-related results about `ℝ≥0∞` (see data/real/ennreal.lean).
-/

open filter
open_locale filter ennreal

namespace ennreal
variables {α : Type*} {f : filter α}

lemma eventually_le_limsup [countable_Inter_filter f] (u : α → ℝ≥0∞) :
  ∀ᶠ y in f, u y ≤ f.limsup u :=
begin
  by_cases hx_top : f.limsup u = ⊤,
  { simp_rw hx_top,
    exact eventually_of_forall (λ a, le_top), },
  have h_forall_le : ∀ᶠ y in f, ∀ n : ℕ, u y < f.limsup u + (1:ℝ≥0∞)/n,
  { rw eventually_countable_forall,
    refine λ n, eventually_lt_of_limsup_lt _,
    nth_rewrite 0 ←add_zero (f.limsup u),
    exact (add_lt_add_iff_left hx_top).mpr (by simp), },
  refine h_forall_le.mono (λ y hy, le_of_forall_pos_le_add (λ r hr_pos hx_top, _)),
  have hr_ne_zero : (r : ℝ≥0∞) ≠ 0,
  { rw [ne.def, coe_eq_zero],
    exact (ne_of_lt hr_pos).symm, },
  cases (exists_inv_nat_lt hr_ne_zero) with i hi,
  rw inv_eq_one_div at hi,
  exact (hy i).le.trans (add_le_add_left hi.le (f.limsup u)),
end

lemma limsup_eq_zero_iff [countable_Inter_filter f] {u : α → ℝ≥0∞} :
  f.limsup u = 0 ↔ u =ᶠ[f] 0 :=
begin
  split; intro h,
  { have hu_zero := eventually_le.trans (eventually_le_limsup u)
      (eventually_of_forall (λ _, le_of_eq h)),
    exact hu_zero.mono (λ x hx, le_antisymm hx (zero_le _)), },
  { rw limsup_congr h,
    simp_rw [pi.zero_apply, ←ennreal.bot_eq_zero, limsup_const_bot] },
end

lemma limsup_const_mul_of_ne_top {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha_top : a ≠ ⊤) :
  f.limsup (λ (x : α), a * (u x)) = a * f.limsup u :=
begin
  by_cases ha_zero : a = 0,
  { simp_rw [ha_zero, zero_mul, ←ennreal.bot_eq_zero],
    exact limsup_const_bot, },
  let g := λ x : ℝ≥0∞, a * x,
  have hg_bij : function.bijective g,
  from function.bijective_iff_has_inverse.mpr ⟨(λ x, a⁻¹ * x),
    ⟨λ x, by simp [←mul_assoc, inv_mul_cancel ha_zero ha_top],
    λ x, by simp [g, ←mul_assoc, mul_inv_cancel ha_zero ha_top]⟩⟩,
  have hg_mono : strict_mono g,
    from monotone.strict_mono_of_injective
      (λ _ _ _, by rwa mul_le_mul_left ha_zero ha_top) hg_bij.1,
  let g_iso := strict_mono.order_iso_of_surjective g hg_mono hg_bij.2,
  refine (order_iso.limsup_apply g_iso _ _ _ _).symm,
  all_goals { by is_bounded_default },
end

lemma limsup_const_mul [countable_Inter_filter f] {u : α → ℝ≥0∞} {a : ℝ≥0∞} :
  f.limsup (λ (x : α), a * (u x)) = a * f.limsup u :=
begin
  by_cases ha_top : a ≠ ⊤,
  { exact limsup_const_mul_of_ne_top ha_top, },
  push_neg at ha_top,
  by_cases hu : u =ᶠ[f] 0,
  { have hau : (λ x, a * (u x)) =ᶠ[f] 0,
    { refine hu.mono (λ x hx, _),
      rw pi.zero_apply at hx,
      simp [hx], },
    simp only [limsup_congr hu, limsup_congr hau, pi.zero_apply, ← bot_eq_zero, limsup_const_bot],
    simp, },
  { simp_rw [ha_top, top_mul],
    have hu_mul : ∃ᶠ (x : α) in f, ⊤ ≤ ite (u x = 0) (0 : ℝ≥0∞) ⊤,
    { rw [eventually_eq, not_eventually] at hu,
      refine hu.mono (λ x hx, _),
      rw pi.zero_apply at hx,
      simp [hx], },
    have h_top_le : f.limsup (λ (x : α), ite (u x = 0) (0 : ℝ≥0∞) ⊤) = ⊤,
      from eq_top_iff.mpr (le_limsup_of_frequently_le hu_mul),
    have hfu : f.limsup u ≠ 0, from mt limsup_eq_zero_iff.1 hu,
    simp only [h_top_le, hfu, if_false], },
end

lemma limsup_add_le [countable_Inter_filter f] (u v : α → ℝ≥0∞) :
  f.limsup (u + v) ≤ f.limsup u + f.limsup v :=
Inf_le ((eventually_le_limsup u).mp ((eventually_le_limsup v).mono
  (λ _ hxg hxf, add_le_add hxf hxg)))

lemma limsup_liminf_le_liminf_limsup {β} [encodable β] {f : filter α} [countable_Inter_filter f]
  {g : filter β} (u : α → β → ℝ≥0∞) :
  f.limsup (λ (a : α), g.liminf (λ (b : β), u a b)) ≤ g.liminf (λ b, f.limsup (λ a, u a b)) :=
begin
  have h1 : ∀ᶠ a in f, ∀ b, u a b ≤ f.limsup (λ a', u a' b),
    by { rw eventually_countable_forall, exact λ b, ennreal.eventually_le_limsup (λ a, u a b), },
  refine Inf_le (h1.mono (λ x hx, filter.liminf_le_liminf (filter.eventually_of_forall hx) _)),
  filter.is_bounded_default,
end

end ennreal

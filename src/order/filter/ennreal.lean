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

This file compiles order-related results about `ennreal` (see data/real/ennreal.lean).
-/

open filter
open_locale filter

namespace ennreal

lemma eventually_le_limsup {α} {f : filter α} [countable_Inter_filter f] (u : α → ennreal) :
  ∀ᶠ y in f, u y ≤ f.limsup u :=
begin
  by_cases hx_top : f.limsup u = ⊤,
  { simp_rw hx_top,
    exact eventually_of_forall (λ a, le_top), },
  have h_forall_le : ∀ᶠ y in f, ∀ n : ℕ, u y < f.limsup u + (1:ennreal)/n,
  { rw eventually_countable_forall,
    refine λ n, eventually_lt_of_limsup_lt _,
    nth_rewrite 0 ←add_zero (f.limsup u),
    exact (add_lt_add_iff_left (lt_top_iff_ne_top.mpr hx_top)).mpr (by simp), },
  refine h_forall_le.mono (λ y hy, le_of_forall_epsilon_le (λ r hr_pos hx_top,_)),
  have hr_ne_zero : (r : ennreal) ≠ 0,
  { rw [ne.def, coe_eq_zero],
    exact (ne_of_lt hr_pos).symm, },
  cases (exists_inv_nat_lt hr_ne_zero) with i hi,
  refine le_trans (le_of_lt (hy i)) (add_le_add_left (le_of_lt _) (f.limsup u)),
  rwa [div_def, one_mul],
end

lemma limsup_const_mul {α} {f : filter α} [ne_bot f] {u : α → ennreal} {a : ennreal}
  (ha_top : a ≠ ⊤) :
  f.limsup (λ (x : α), a * (u x)) = a * f.limsup u :=
begin
  by_cases ha_zero : a = 0,
  { simp [ha_zero, limsup_const (0 : ennreal)], },
  let g := λ x : ennreal, a * x,
  have hg_bij : function.bijective g,
  from function.bijective_iff_has_inverse.mpr ⟨(λ x, a⁻¹ * x),
    ⟨λ x, by simp [←mul_assoc, inv_mul_cancel ha_zero ha_top],
    λ x, by simp [g, ←mul_assoc, mul_inv_cancel ha_zero ha_top]⟩⟩,
  have hg_mono : strict_mono g,
  from strict_mono_of_monotone_of_injective
    (λ _ _ _, by rwa mul_le_mul_left ha_zero ha_top) hg_bij.1,
  let g_iso := strict_mono.order_iso_of_surjective g hg_mono hg_bij.2,
  refine (order_iso.limsup_apply g_iso _ _ _ _).symm,
  all_goals { by is_bounded_default},
end

lemma limsup_add_le {α} (f : filter α) [countable_Inter_filter f] (u v : α → ennreal) :
  f.limsup (u + v) ≤ f.limsup u + f.limsup v :=
Inf_le ((eventually_le_limsup u).mp ((eventually_le_limsup v).mono
  (λ _ hxg hxf, add_le_add hxf hxg)))

end ennreal

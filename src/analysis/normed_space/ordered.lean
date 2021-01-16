/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.normed_space.basic
import algebra.ring.basic
import analysis.asymptotics

/-!
# Ordered normed spaces

In this file, we define classes for fields and groups that are both normed and ordered.
These are mostly useful to avoid diamonds during type class inference.
-/

open filter asymptotics set
open_locale topological_space

/-- A `normed_linear_ordered_group` is an additive group that is both a `normed_group` and
    a `linear_ordered_add_comm_group`. This class is necessary to avoid diamonds. -/
class normed_linear_ordered_group (α : Type*)
extends linear_ordered_add_comm_group α, has_norm α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))

@[priority 100] instance normed_linear_ordered_group.to_normed_group (α : Type*)
  [normed_linear_ordered_group α] : normed_group α :=
⟨normed_linear_ordered_group.dist_eq⟩

/-- A `normed_linear_ordered_field` is a field that is both a `normed_field` and a
    `linear_ordered_field`. This class is necessary to avoid diamonds. -/
class normed_linear_ordered_field (α : Type*)
extends linear_ordered_field α, has_norm α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul' : ∀ a b, norm (a * b) = norm a * norm b)

@[priority 100] instance normed_linear_ordered_field.to_normed_field (α : Type*)
  [normed_linear_ordered_field α] : normed_field α :=
{ dist_eq := normed_linear_ordered_field.dist_eq,
  norm_mul' := normed_linear_ordered_field.norm_mul' }

@[priority 100] instance normed_linear_ordered_field.to_normed_linear_ordered_group (α : Type*)
[normed_linear_ordered_field α] : normed_linear_ordered_group α :=
⟨normed_linear_ordered_field.dist_eq⟩

noncomputable
instance : normed_linear_ordered_field ℚ :=
⟨dist_eq_norm, normed_field.norm_mul⟩

noncomputable
instance : normed_linear_ordered_field ℝ :=
⟨dist_eq_norm, normed_field.norm_mul⟩

variables {𝕜 : Type*} [normed_linear_ordered_field 𝕜]

lemma pow_div_pow_eventually_eq_at_top {p q : ℕ} :
  (λ x : 𝕜, x^p / x^q) =ᶠ[at_top] (λ x, x^((p : ℤ) -q)) :=
begin
  apply ((eventually_gt_at_top (0 : 𝕜)).mono (λ x hx, _)),
  simp [fpow_sub hx.ne'],
end

lemma pow_div_pow_eventually_eq_at_bot {p q : ℕ} :
  (λ x : 𝕜, x^p / x^q) =ᶠ[at_bot] (λ x, x^((p : ℤ) -q)) :=
begin
  apply ((eventually_lt_at_bot (0 : 𝕜)).mono (λ x hx, _)),
  simp [fpow_sub hx.ne'.symm],
end

lemma tendsto_fpow_at_top_at_top {n : ℤ} (hn : 0 < n) : tendsto (λ x : 𝕜, x^n) at_top at_top :=
begin
  lift n to ℕ using hn.le,
  exact tendsto_pow_at_top (nat.succ_le_iff.mpr $int.coe_nat_pos.mp hn)
end

lemma tendsto_fpow_at_top_zero [order_topology 𝕜] {n : ℤ} (hn : n < 0) :
  tendsto (λ x : 𝕜, x^n) at_top (𝓝 0) :=
begin
  have : 1 ≤ -n, by linarith,
  apply tendsto.congr (show ∀ x : 𝕜, x^-(-n) = x^n, by simp),
  lift -n to ℕ using le_of_lt (neg_pos.mpr hn) with N,
  exact tendsto_pow_neg_at_top (by exact_mod_cast this)
end

lemma tendsto_pow_div_pow_at_top_at_top {p q : ℕ} (hpq : q < p) :
  tendsto (λ x : 𝕜, x^p / x^q) at_top at_top :=
begin
  rw tendsto_congr' pow_div_pow_eventually_eq_at_top,
  apply tendsto_fpow_at_top_at_top,
  linarith
end

lemma tendsto_pow_div_pow_at_top_zero
  [order_topology 𝕜] {p q : ℕ} (hpq : p < q) :
  tendsto (λ x : 𝕜, x^p / x^q) at_top (𝓝 0) :=
begin
  rw tendsto_congr' pow_div_pow_eventually_eq_at_top,
  apply tendsto_fpow_at_top_zero,
  linarith
end

lemma asymptotics.is_o_pow_pow_at_top_of_lt
  [order_topology 𝕜] {p q : ℕ} (hpq : p < q) :
  is_o (λ x : 𝕜, x^p) (λ x, x^q) at_top :=
begin
  refine (is_o_iff_tendsto' _).mpr (tendsto_pow_div_pow_at_top_zero hpq),
  exact (eventually_gt_at_top 0).mono (λ x hx hxq, (pow_ne_zero q hx.ne' hxq).elim),
end

lemma asymptotics.is_O.trans_tendsto_norm_at_top {α : Type*} {u v : α → 𝕜} {l : filter α}
  (huv : is_O u v l) (hu : tendsto (λ x, ∥u x∥) l at_top) : tendsto (λ x, ∥v x∥) l at_top :=
begin
  rcases huv.exists_pos with ⟨c, hc, hcuv⟩,
  rw is_O_with at hcuv,
  convert tendsto.at_top_div_const hc (tendsto_at_top_mono' l hcuv hu),
  ext x,
  rw mul_div_cancel_left _ hc.ne.symm,
end

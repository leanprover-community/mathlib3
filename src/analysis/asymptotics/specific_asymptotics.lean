/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.normed_space.ordered
import analysis.asymptotics.asymptotics

/-!
# A collection of specific asymptotic results

This file contains specific lemmas about asymptotics which don't have their place in the general
theory developped in `analysis.asymptotics.asymptotics`.
-/

open filter asymptotics
open_locale topological_space

section nat_coe

-- TODO: Is there some better place to put these lemmas?

lemma norm_coe_nat_le_coe_nat_real (R : Type*) [semi_normed_ring R] [norm_one_class R] :
  ∀ (n : ℕ), ∥(n : R)∥ ≤ (n : ℝ)
| 0 := by simp only [norm_zero, nat.cast_zero]
| (n+1) := (norm_add_le _ _).trans (add_le_add (norm_coe_nat_le_coe_nat_real n) (le_of_eq norm_one))

lemma coe_nat_is_O_coe_nat_real (R : Type*) [semi_normed_ring R] [norm_one_class R] :
  asymptotics.is_O (coe : ℕ → R) (coe : ℕ → ℝ) filter.at_top :=
asymptotics.is_O_of_le filter.at_top
  (λ n, le_trans (norm_coe_nat_le_coe_nat_real R n) (le_abs.2 (or.inl le_rfl)))

lemma coe_nat_tendsto_at_top (R : Type*) [ordered_semiring R] [nontrivial R] [archimedean R] :
  filter.tendsto (λ (n : ℕ), (↑n : R)) filter.at_top filter.at_top :=
filter.tendsto_at_top.2 (λ x, let ⟨m, hm⟩ := exists_nat_ge x in
  filter.eventually_at_top.2 ⟨m, λ y hy, hm.trans $ nat.cast_le.2 hy⟩)

end nat_coe

section linear_ordered_field

variables {𝕜 : Type*} [linear_ordered_field 𝕜]

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

lemma tendsto_fpow_at_top_at_top {n : ℤ}
  (hn : 0 < n) : tendsto (λ x : 𝕜, x^n) at_top at_top :=
begin
  lift n to ℕ using hn.le,
  simp only [gpow_coe_nat],
  exact tendsto_pow_at_top (nat.succ_le_iff.mpr $int.coe_nat_pos.mp hn)
end

lemma tendsto_pow_div_pow_at_top_at_top {p q : ℕ}
  (hpq : q < p) : tendsto (λ x : 𝕜, x^p / x^q) at_top at_top :=
begin
  rw tendsto_congr' pow_div_pow_eventually_eq_at_top,
  apply tendsto_fpow_at_top_at_top,
  linarith
end

lemma tendsto_pow_div_pow_at_top_zero [topological_space 𝕜] [order_topology 𝕜] {p q : ℕ}
  (hpq : p < q) : tendsto (λ x : 𝕜, x^p / x^q) at_top (𝓝 0) :=
begin
  rw tendsto_congr' pow_div_pow_eventually_eq_at_top,
  apply tendsto_fpow_at_top_zero,
  linarith
end

end linear_ordered_field

section normed_linear_ordered_field

variables {𝕜 : Type*} [normed_linear_ordered_field 𝕜]

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

end normed_linear_ordered_field

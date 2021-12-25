/-
Copyright (c) 2021 Malo Jaffré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malo Jaffré
-/
import analysis.convex.slope
import analysis.normed_space.basic
import data.set.intervals.basic
import topology.metric_space.basic

section real

open metric real set
open_locale topological_space

variables {f : ℝ → ℝ} {s: set ℝ}

lemma convex_on.lipschitz_on_with (hf : convex_on ℝ s f)
  {w x y z: ℝ} (hw : w ∈ s) (hz : z ∈ s) (hwx: w < x) (hyz : y < z) :
  lipschitz_on_with
    (max (abs ((f x - f w) / (x - w))) (abs ((f z - f y) / (z - y)))).to_nnreal
    f
    (Icc x y) :=
begin
  rw lipschitz_on_with_iff_dist_le_mul,
  rintros b ⟨hxb, hby⟩ a ⟨hxa, hay⟩,
  rcases eq_or_ne a b with rfl | hab,
  { simp only [le_refl, real.coe_to_nnreal', mul_zero, dist_self], },
  have : 0 < |b - a| := by rwa [abs_pos, sub_ne_zero, ne_comm],
  rw [dist_eq, dist_eq, coe_to_nnreal _ (le_max_of_le_left (abs_nonneg _)),
    ←div_le_iff this, ←abs_div],
  have hwzs : Icc w z ⊆ s := hf.1.ord_connected.out hw hz,
  have ha : a ∈ s := hwzs ⟨hwx.le.trans hxa, hay.trans hyz.le⟩,
  have hb : b ∈ s := hwzs ⟨hwx.le.trans hxb, hby.trans hyz.le⟩,
  cases hab.lt_or_lt with hab hba,
  {
    have h₁ := hf.slope_mono hw hb hwx hxa hab,
    have h₂ := hf.slope_mono ha hz hab hby hyz,
    exact abs_le_max_abs_abs h₁ h₂,
  },
  {
    have h₁ := hf.slope_mono hw ha hwx hxb hba,
    have h₂ := hf.slope_mono hb hz hba hay hyz,
    rw [←neg_sub (f b), ←neg_sub b, neg_div_neg_eq] at h₁ h₂,
    exact abs_le_max_abs_abs h₁ h₂,
  },
end

lemma convex_on.uniform_continuous_on_Icc (hf : convex_on ℝ s f)
  {w x y z: ℝ} (hw : w ∈ s) (hz : z ∈ s) (hwx: w < x) (hyz : y < z) :
  uniform_continuous_on f (Icc x y) :=
(hf.lipschitz_on_with hw hz hwx hyz).uniform_continuous_on

lemma convex_on.continuous_on_Icc (hf : convex_on ℝ s f)
  {w x y z: ℝ} (hw : w ∈ s) (hz : z ∈ s) (hwx: w < x) (hyz : y < z) :
  continuous_on f (Icc x y) :=
(hf.uniform_continuous_on_Icc hw hz hwx hyz).continuous_on

lemma convex_on.continuous_at (hf : convex_on ℝ s f) {a: ℝ} (hsa : s ∈ 𝓝 a):
  continuous_at f a :=
begin
  obtain ⟨ε, εpos, hε⟩ : ∃ ε (hε : 0 < ε), closed_ball a ε ⊆ s :=
    nhds_basis_closed_ball.mem_iff.1 hsa,
  rw closed_ball_eq_Icc at hε,
  have hwz : a - ε ≤ a + ε := by linarith,
  have hwx : a - ε < a - ε/2 := by linarith,
  have hyz : a + ε/2 < a + ε := by linarith,
  have hw : a - ε ∈ s,
  { apply hε, rw [set.left_mem_Icc], linarith, },
  have hz : a + ε ∈ s,
  { apply hε, rw [set.right_mem_Icc], linarith, },
  have hcont_on := hf.continuous_on_Icc hw hz hwx hyz,
  have : Icc (a - ε/2) (a + ε/2) ∈ 𝓝 a,
  { apply Icc_mem_nhds; linarith, },
  exact hcont_on.continuous_at this,
end

lemma convex_on.continuous_on (hf : convex_on ℝ s f) (hsa : is_open s):
  continuous_on f s :=
begin
  apply continuous_at.continuous_on,
  intros a ha,
  exact hf.continuous_at (hsa.mem_nhds ha),
end

end real

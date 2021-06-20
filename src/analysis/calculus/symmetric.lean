/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.deriv

open asymptotics set
open_locale topological_space

section
variables {E F : Type*} [normed_group E] [normed_space ℝ E]
[normed_group F] [normed_space ℝ F]
{s : set E}
(s_conv : convex s) (s_open : is_open s)
{f : E → F} {f' : E → (E →L[ℝ] F)} {f'' : E →L[ℝ] (E →L[ℝ] F)}
(hf : ∀ x ∈ s, has_fderiv_at f (f' x) x)
{x : E} (xs : x ∈ closure s) (hx : has_fderiv_within_at f' f'' s x)

include s_conv s_open hx

lemma zoug {x y : E} (hx : x ∈ closure s) (hy : y ∈ s) : open_segment x y ⊆ s :=
begin
  -- let : has_continuous_smul (units ℝ) E := by apply_instance,
  rw open_segment_eq_image',
  assume z hz,
  rcases (mem_image _ _ _).1 hz with ⟨t, ⟨tpos, tlt_1⟩, zt⟩,
  rw ← zt,
end



#exit



lemma glou (v w : E) (hv : x + v ∈ s) (hw : x + v + w ∈ s) :
  is_o (λ (h : ℝ), f (x + h • v + h • w) - f (x + h • v) - h • f' x w
    - h^2 • f'' v w - (h^2/2) • f'' w w) (λ h, h^2) (𝓝[Ioi (0 : ℝ)] 0) :=
begin
  apply is_o_iff.2 (λ ε εpos, _),
  rw [has_fderiv_within_at, has_fderiv_at_filter, is_o_iff] at hx,
  rcases metric.mem_nhds_within_iff.1 (hx εpos) with ⟨δ, δpos, sδ⟩,
  have E1 : ∀ᶠ h in 𝓝[Ioi (0:ℝ)] 0, h * (∥v∥ + ∥w∥) < δ,
  { have : filter.tendsto (λ h, h * (∥v∥ + ∥w∥)) (𝓝[Ioi (0:ℝ)] 0) (𝓝 (0 * (∥v∥ + ∥w∥))) :=
      (continuous_id.mul continuous_const).continuous_within_at,
    apply (tendsto_order.1 this).2 δ,
    simpa using δpos },
  have E2 : ∀ᶠ h in 𝓝[Ioi (0:ℝ)] 0, (h : ℝ) < 1 :=
    mem_nhds_within_Ioi_iff_exists_Ioo_subset.2 ⟨(1 : ℝ), by simp, λ x hx, hx.2⟩,
  filter_upwards [E1, E2, self_mem_nhds_within],
  assume h hδ h_lt_1 hpos,
  replace hpos : 0 < h := hpos,
  let g := λ t, f (x + h • v + (t * h) • w) - (t * h) • f' x w  - (t * h^2) • f'' v w
    - ((t * h)^2/2) • f'' w w,
  set g' := λ t, f' (x + h • v + (t * h) • w) (h • w) - h • f' x w
    - h^2 • f'' v w - (t * h^2) • f'' w w with hg',
  have : ∀ t ∈ Icc (0 : ℝ) 1, has_deriv_within_at g (g' t) (Icc 0 1) t,
  have : ∀ t ∈ Icc (0 : ℝ) 1, ∥g' t∥ ≤ ε,
  { assume t ht,
    have I : ∥h • v + (t * h) • w∥ ≤ h * (∥v∥ + ∥w∥) := calc
      ∥h • v + (t * h) • w∥ ≤ ∥h • v∥ + ∥(t * h) • w∥ : norm_add_le _ _
      ... = h * ∥v∥ + t * (h * ∥w∥) :
        by simp [norm_smul, real.norm_eq_abs, hpos.le, abs_of_nonneg, abs_mul, ht.1, mul_assoc]
      ... ≤ h * ∥v∥ + 1 * (h * ∥w∥) :
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_right ht.2
          (mul_nonneg hpos.le (norm_nonneg _)))
      ... = h * (∥v∥ + ∥w∥) : by ring,
    calc ∥g' t∥ = ∥(f' (x + h • v + (t * h) • w) - f' x - f'' (h • v + (t * h) • w)) (h • w)∥ :
    sorry/-begin
      rw hg',
      have : h * (t * h) = t * (h * h), by ring,
      simp only [continuous_linear_map.coe_sub', continuous_linear_map.map_add, pow_two,
        continuous_linear_map.add_apply, pi.smul_apply, smul_sub, smul_add, smul_smul, ← sub_sub,
        continuous_linear_map.coe_smul', pi.sub_apply, continuous_linear_map.map_smul, this]
    end-/
    ... ≤ ∥f' (x + h • v + (t * h) • w) - f' x - f'' (h • v + (t * h) • w)∥ * ∥h • w∥ :
      continuous_linear_map.le_op_norm _ _
    ... ≤ (ε * ∥h • v + (t * h) • w∥) * (∥h • w∥) :
    begin
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
      suffices H : x + h • v + (t * h) • w ∈ metric.ball x δ ∩ s,
      { have := sδ H,
        simp only [mem_set_of_eq] at this,
        convert this;
        abel },
      split,
      { rw [add_assoc, add_mem_ball_iff_norm],
        exact I.trans_lt hδ },


    end
    ... ≤ ε : sorry

  }

end


end

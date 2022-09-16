import measure_theory.measure.lebesgue
import analysis.calculus.deriv
import measure_theory.covering.differentiation
import measure_theory.covering.vitali

open set filter function metric measure_theory measure_theory.measure_space
open_locale nnreal ennreal topological_space


section

variables {α : Type*} [metric_space α] [measurable_space α] {μ : measure α}

lemma vitali_family.tendsto_filter_at (v : vitali_family μ) {β : Type*} {l : filter β}
  {f : β → set α} {x : α}
  (H : ∀ᶠ i in l, f i ∈ v.sets_at x) (H' : ∀ (ε > (0 : ℝ)), ∀ᶠ i in l, f i ⊆ closed_ball x ε) :
  tendsto f l (v.filter_at x)  :=
begin
  assume s hs,
  change ∀ᶠ i in l, f i ∈ s,
  obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ) (H : ε > 0), ∀ (a : set α),
    a ∈ v.sets_at x → a ⊆ closed_ball x ε → a ∈ s :=
      (vitali_family.mem_filter_at_iff _).1 hs,
  filter_upwards [H, H' ε εpos] with i hi h'i using hε _ hi h'i,
end

end




open measure_theory measure_theory.measure set filter

open_locale nnreal ennreal topological_space

namespace real

protected noncomputable def vitali_family : vitali_family (volume : measure ℝ) :=
begin
  refine vitali.vitali_family (volume : measure ℝ) (12 : ℝ≥0)
    (λ x ε εpos, ⟨ε, ⟨εpos, le_refl _⟩, _⟩),
  have : (0 : ℝ) ≤ 6, by norm_num,
  suffices H : 2 * 6 * ennreal.of_real ε ≤ 2 * 12 * ennreal.of_real ε,
    by simpa [ennreal.of_real_mul, this, ← mul_assoc, mul_comm _ (2 : ℝ≥0∞)] using H,
  apply ennreal.mul_le_mul (ennreal.mul_le_mul (le_refl _) _) (le_refl _),
  have : ennreal.of_real 6 ≤ ennreal.of_real 12,
    from ennreal.of_real_le_of_real (by norm_num),
  simpa using this,
end

lemma diam_Icc {a b : ℝ} (h : a ≤ b) : metric.diam (Icc a b) = b - a :=
by simp [metric.diam, ennreal.to_real_of_real, sub_nonneg.2 h]

lemma Icc_mem_vitali_family_at_right {x y : ℝ} (hxy : x < y) :
  Icc x y ∈ real.vitali_family.sets_at x :=
begin
  have H : ennreal.of_real (2 * (3 * metric.diam (Icc x y))) ≤ 12 * ennreal.of_real (y - x),
  { simp only [ennreal.of_real_mul, zero_le_three, real.diam_Icc hxy.le, ←mul_assoc,
      zero_le_mul_left, zero_lt_bit0, zero_lt_one, zero_le_bit0, zero_le_one,
      ennreal.of_real_bit0, ennreal.of_real_one, ennreal.of_real_bit1],
    apply ennreal.mul_le_mul _ (le_refl _),
    have : ennreal.of_real (2 * 3) ≤ ennreal.of_real 12,
      from ennreal.of_real_le_of_real (by norm_num),
    simpa [ennreal.of_real_mul] using this },
  simpa [real.vitali_family, vitali.vitali_family, hxy, hxy.le, is_closed_Icc] using H,
end

lemma tendsto_Icc_vitali_family_right (x : ℝ) :
  tendsto (λ y, Icc x y) (𝓝[>] x) (real.vitali_family.filter_at x) :=
begin
  apply vitali_family.tendsto_filter_at,
  { filter_upwards [self_mem_nhds_within] with y hy using Icc_mem_vitali_family_at_right hy },
  { assume ε εpos,
    have : x ∈ Ico x (x + ε) := ⟨le_refl _, by linarith⟩,
    filter_upwards [Icc_mem_nhds_within_Ioi this] with y hy,
    rw closed_ball_eq_Icc,
    exact Icc_subset_Icc (by linarith) hy.2 }
end

lemma Icc_mem_vitali_family_at_left {x y : ℝ} (hxy : x < y) :
  Icc x y ∈ real.vitali_family.sets_at y :=
begin
  have H : ennreal.of_real (2 * (3 * metric.diam (Icc x y))) ≤ 12 * ennreal.of_real (y - x),
  { simp only [ennreal.of_real_mul, zero_le_three, real.diam_Icc hxy.le, ←mul_assoc,
      zero_le_mul_left, zero_lt_bit0, zero_lt_one, zero_le_bit0, zero_le_one,
      ennreal.of_real_bit0, ennreal.of_real_one, ennreal.of_real_bit1],
    apply ennreal.mul_le_mul _ (le_refl _),
    have : ennreal.of_real (2 * 3) ≤ ennreal.of_real 12,
      from ennreal.of_real_le_of_real (by norm_num),
    simpa [ennreal.of_real_mul] using this },
  simpa [real.vitali_family, vitali.vitali_family, hxy, hxy.le, is_closed_Icc] using H,
end

lemma tendsto_Icc_vitali_family_left (x : ℝ) :
  tendsto (λ y, Icc y x) (𝓝[<] x) (real.vitali_family.filter_at x) :=
begin
  apply vitali_family.tendsto_filter_at,
  { filter_upwards [self_mem_nhds_within] with y hy using Icc_mem_vitali_family_at_left hy },
  { assume ε εpos,
    have : x ∈ Ioc (x - ε) x := ⟨by linarith, le_refl _⟩,
    filter_upwards [Icc_mem_nhds_within_Iio this] with y hy,
    rw closed_ball_eq_Icc,
    exact Icc_subset_Icc hy.1 (by linarith) }
end

@[to_additive] lemma tendsto_const_mul_nhds_right {α : Type*}
  [linear_ordered_comm_group α] [topological_space α] [has_continuous_mul α]
  (x a : α) : tendsto (λ y, x * y) (𝓝[>] a) (𝓝[>] (x * a)) :=
begin
  apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
  { exact (tendsto.const_mul x tendsto_id).mono_left nhds_within_le_nhds },
  { filter_upwards [self_mem_nhds_within],
    rintros y (hy : a < y),
    rw mem_Ioi,
    exact mul_lt_mul_left' hy _, }
end

@[to_additive] lemma tendsto_mul_const_nhds_right {α : Type*}
  [linear_ordered_comm_group α] [topological_space α] [has_continuous_mul α]
  (x a : α) : tendsto (λ y, y * x) (𝓝[>] a) (𝓝[>] (a * x)) :=
begin
  apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
  { exact (tendsto.mul_const x tendsto_id).mono_left nhds_within_le_nhds },
  { filter_upwards [self_mem_nhds_within],
    rintros y (hy : a < y),
    rw mem_Ioi,
    exact mul_lt_mul_right' hy _, }
end


@[to_additive] lemma tendsto_const_mul_nhds_left {α : Type*}
  [linear_ordered_comm_group α] [topological_space α] [has_continuous_mul α]
  (x a : α) : tendsto (λ y, x * y) (𝓝[<] a) (𝓝[<] (x * a)) :=
begin
  apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
  { exact (tendsto.const_mul x tendsto_id).mono_left nhds_within_le_nhds },
  { filter_upwards [self_mem_nhds_within],
    rintros y (hy : y < a),
    rw mem_Iio,
    exact mul_lt_mul_left' hy _, }
end

@[to_additive] lemma tendsto_mul_const_nhds_left {α : Type*}
  [linear_ordered_comm_group α] [topological_space α] [has_continuous_mul α]
  (x a : α) : tendsto (λ y, y * x) (𝓝[<] a) (𝓝[<] (a * x)) :=
begin
  apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
  { exact (tendsto.mul_const x tendsto_id).mono_left nhds_within_le_nhds },
  { filter_upwards [self_mem_nhds_within],
    rintros y (hy : y < a),
    rw mem_Iio,
    exact mul_lt_mul_right' hy _, }
end

lemma foo (f : stieltjes_function) :
  ∀ᵐ x, has_deriv_at f (rn_deriv f.measure volume x).to_real x :=
begin
  filter_upwards [vitali_family.ae_tendsto_rn_deriv real.vitali_family f.measure,
    rn_deriv_lt_top f.measure volume] with x hx h'x,
  have A : f.left_lim x = f x := sorry,
  have L1 : tendsto (λ y, (f y - f x) / (y - x))
    (𝓝[>] x) (𝓝 ((rn_deriv f.measure volume x).to_real)),
  { apply tendsto.congr' _
      ((ennreal.tendsto_to_real h'x.ne).comp (hx.comp (tendsto_Icc_vitali_family_right x))),
    filter_upwards [self_mem_nhds_within],
    rintros y (hxy : x < y),
    simp only [comp_app, stieltjes_function.measure_Icc, volume_Icc, A],
    rw [← ennreal.of_real_div_of_pos (sub_pos.2 hxy), ennreal.to_real_of_real],
    exact div_nonneg (sub_nonneg.2 (f.mono hxy.le)) (sub_pos.2 hxy).le },
  have L2 : tendsto (λ y, (f.left_lim y - f x) / (y - x))
    (𝓝[<] x) (𝓝 ((rn_deriv f.measure volume x).to_real)),
  { apply tendsto.congr' _
      ((ennreal.tendsto_to_real h'x.ne).comp (hx.comp (tendsto_Icc_vitali_family_left x))),
    filter_upwards [self_mem_nhds_within],
    rintros y (hxy : y < x),
    simp only [comp_app, stieltjes_function.measure_Icc, volume_Icc, A],
    rw [← ennreal.of_real_div_of_pos (sub_pos.2 hxy), ennreal.to_real_of_real, ← neg_neg (y - x),
        div_neg, neg_div', neg_sub, neg_sub],
    exact div_nonneg (sub_nonneg.2 (f.left_lim_le hxy.le)) (sub_pos.2 hxy).le },
  have L3 : tendsto (λ y, (f.left_lim (y + (x - y)^2) - f x) / (y - x))
    (𝓝[<] x) (𝓝 ((rn_deriv f.measure volume x).to_real)), sorry,
  have L4 : tendsto (λ y, (f y - f x) / (y - x))
    (𝓝[<] x) (𝓝 ((rn_deriv f.measure volume x).to_real)),
  { apply tendsto_of_tendsto_of_tendsto_of_le_of_le' L3 L2,
    { filter_upwards [self_mem_nhds_within],
      rintros y (hy : y < x),
      refine div_le_div_of_nonpos_of_le (by linarith) ((sub_le_sub_iff_right _).2 _),
      apply f.le_left_lim,
      have : 0 < (x - y)^2 := sq_pos_of_pos (sub_pos.2 hy),
      linarith },
    { filter_upwards [self_mem_nhds_within],
      rintros y (hy : y < x),
      refine div_le_div_of_nonpos_of_le (by linarith) _,
      simpa only [sub_le_sub_iff_right] using f.left_lim_le (le_refl y) } },
end

#exit

/-- A monotone right-continuous function `f` is almost everywhere differentiable. Its derivative is
given by the Radon-Nikodym derivative of the Stieltjes measure associated to `f` with respect to
Lebesgue measure. -/
lemma foo (f : stieltjes_function) :
  ∀ᵐ x, has_deriv_at f (rn_deriv f.measure volume x).to_real x :=
begin
  filter_upwards [vitali_family.ae_tendsto_rn_deriv real.vitali_family f.measure,
    rn_deriv_lt_top f.measure volume] with x hx h'x,
  have A : f.left_lim x = f x := sorry,
  have L1 : tendsto (λ r, (f (x + r) - f x) / r)
    (𝓝[>] 0) (𝓝 ((rn_deriv f.measure volume x).to_real)),
  sorry { have L : tendsto (λ r, x + r) (𝓝[>] 0) (𝓝[>] x),
      by simpa using tendsto_const_add_nhds_right x 0,
    apply tendsto.congr' _
      ((ennreal.tendsto_to_real h'x.ne).comp (hx.comp ((tendsto_Icc_vitali_family_right x).comp L))),
    filter_upwards [self_mem_nhds_within],
    rintros r (rpos : 0 < r),
    simp only [comp_app, stieltjes_function.measure_Icc, volume_Icc, A, add_tsub_cancel_left],
    rw [← ennreal.of_real_div_of_pos rpos, ennreal.to_real_of_real],
    exact div_nonneg (sub_nonneg.2 (f.mono (by linarith))) epos.le, },
  have L2 : tendsto (λ r, (f.left_lim (x + r) - f x) / r)
    (𝓝[<] 0) (𝓝 ((rn_deriv f.measure volume x).to_real)),
  sorry { have L : tendsto (λ r, x + r) (𝓝[<] 0) (𝓝[<] x),
      by simpa using tendsto_const_add_nhds_left x 0,
    apply tendsto.congr' _
      ((ennreal.tendsto_to_real h'x.ne).comp (hx.comp ((tendsto_Icc_vitali_family_left x).comp L))),
    filter_upwards [self_mem_nhds_within],
    rintros r (rneg : r < 0),
    simp only [comp_app, stieltjes_function.measure_Icc, volume_Icc, A, sub_add_cancel'],
    rw [← ennreal.of_real_div_of_pos (neg_pos.2 rneg), ennreal.to_real_of_real,
        div_neg, neg_div', neg_sub],
    exact div_nonneg (sub_nonneg.2 (f.left_lim_le (by linarith))) (neg_pos.2 rneg).le },
  have L3 : tendsto (λ r, (f.left_lim (x + r * (1 - |r|)) - f x) / r)
    (𝓝[<] 0) (𝓝 ((rn_deriv f.measure volume x).to_real)), sorry,
  have L4 : tendsto (λ r, (f (x + r) - f x) / r)
    (𝓝[<] 0) (𝓝 ((rn_deriv f.measure volume x).to_real)),
  sorry { apply tendsto_of_tendsto_of_tendsto_of_le_of_le' L3 L2,
    { filter_upwards [self_mem_nhds_within],
      rintros r (rneg : r < 0),
      apply div_le_div_of_nonpos_of_le rneg.le ((sub_le_sub_iff_right _).2 _),
      apply f.le_left_lim,
      have : r * |r| < 0 := mul_neg_of_neg_of_pos rneg (abs_pos_of_neg rneg),
      rw [mul_sub_left_distrib],
      linarith },
    { filter_upwards [self_mem_nhds_within],
      rintros r (rneg : r < 0),
      apply div_le_div_of_nonpos_of_le rneg.le,
      simpa only [sub_le_sub_iff_right] using f.left_lim_le (le_refl (x + r)) } },
  rw has_deriv_at_iff_tendsto_slope,


end


#exit

have : tendsto (λ y, (f y - f x) / (y - x))
    (𝓝[>] x) (𝓝 ((rn_deriv f.measure volume x).to_real)),
  { apply tendsto.congr' _
      ((ennreal.tendsto_to_real h'x.ne).comp (hx.comp (tendsto_Icc_vitali_family_right x))),
    filter_upwards [self_mem_nhds_within],
    rintros y (hxy : x < y),
    simp only [comp_app, stieltjes_function.measure_Icc, volume_Icc, A],
    rw [← ennreal.of_real_div_of_pos (sub_pos.2 hxy), ennreal.to_real_of_real],
    exact div_nonneg (sub_nonneg.2 (f.mono hxy.le)) (sub_pos.2 hxy).le },
  have : tendsto (λ y, (f x - f.left_lim y) / (x - y))
    (𝓝[<] x) (𝓝 ((rn_deriv f.measure volume x).to_real)),
  { apply tendsto.congr' _
      ((ennreal.tendsto_to_real h'x.ne).comp (hx.comp (tendsto_Icc_vitali_family_left x))),
    filter_upwards [self_mem_nhds_within],
    rintros y (hxy : y < x),
    simp only [comp_app, stieltjes_function.measure_Icc, volume_Icc, A],
    rw [← ennreal.of_real_div_of_pos (sub_pos.2 hxy), ennreal.to_real_of_real],
    exact div_nonneg (sub_nonneg.2 (f.left_lim_le hxy.le)) (sub_pos.2 hxy).le }

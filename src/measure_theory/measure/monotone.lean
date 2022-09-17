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

lemma _root_.monotone.countable_not_continuous_at {f : ℝ → ℝ} (hf : monotone f) :
  set.countable {x | ¬(continuous_at f x)} :=
begin
  have : ∀ x, ¬(continuous_at f x) →
    ∃ (y : ℚ), monotone.left_lim f x < y ∧ (y : ℝ) < monotone.right_lim f x,
  { assume x hx,
    have : monotone.left_lim f x < monotone.right_lim f x,
    { rcases eq_or_lt_of_le (hf.left_lim_le_right_lim (le_refl x)) with h|h,
      { exact (hx (hf.left_lim_eq_right_lim_iff_continuous_at.1 h)).elim },
      { exact h } },
    exact exists_rat_btwn this },
  choose! F hF using this,
  have A : maps_to F {x | ¬(continuous_at f x)} (univ : set ℚ) := maps_to_univ _ _,
  have B : inj_on F {x | ¬(continuous_at f x)},
  { apply strict_mono_on.inj_on,
    assume x hx y hy hxy,
    have : (F x : ℝ) < F y, from calc
      (F x : ℝ) < monotone.right_lim f x : (hF _ hx).2
      ... ≤ monotone.left_lim f y : hf.right_lim_le_left_lim hxy
      ... < F y : (hF _ hy).1,
    exact_mod_cast this },
  exact maps_to.countable_of_inj_on A B countable_univ,
end

lemma _root_.stieltjes_function.countable_left_lim_ne (f : stieltjes_function) :
  set.countable {x | f.left_lim x ≠ f x} :=
begin
  apply countable.mono _ (f.mono.countable_not_continuous_at),
  assume x hx h'x,
  apply hx,
  exact tendsto_nhds_unique (f.tendsto_left_lim x) (h'x.tendsto.mono_left nhds_within_le_nhds),
end

/-- A monotone right-continuous function `f` is almost everywhere differentiable. Its derivative is
given by the Radon-Nikodym derivative of the Stieltjes measure associated to `f` with respect to
Lebesgue measure. -/
lemma foo (f : stieltjes_function) :
  ∀ᵐ x, has_deriv_at f (rn_deriv f.measure volume x).to_real x :=
begin
  filter_upwards [vitali_family.ae_tendsto_rn_deriv real.vitali_family f.measure,
    rn_deriv_lt_top f.measure volume, f.countable_left_lim_ne.ae_not_mem volume] with x hx h'x h''x,
  have L1 : tendsto (λ y, (f y - f x) / (y - x))
    (𝓝[>] x) (𝓝 ((rn_deriv f.measure volume x).to_real)),
  { apply tendsto.congr' _
      ((ennreal.tendsto_to_real h'x.ne).comp (hx.comp (tendsto_Icc_vitali_family_right x))),
    filter_upwards [self_mem_nhds_within],
    rintros y (hxy : x < y),
    simp only [comp_app, stieltjes_function.measure_Icc, volume_Icc, not_not.1 h''x],
    rw [← ennreal.of_real_div_of_pos (sub_pos.2 hxy), ennreal.to_real_of_real],
    exact div_nonneg (sub_nonneg.2 (f.mono hxy.le)) (sub_pos.2 hxy).le },
  have L2 : tendsto (λ y, (f.left_lim y - f x) / (y - x))
    (𝓝[<] x) (𝓝 ((rn_deriv f.measure volume x).to_real)),
  { apply tendsto.congr' _
      ((ennreal.tendsto_to_real h'x.ne).comp (hx.comp (tendsto_Icc_vitali_family_left x))),
    filter_upwards [self_mem_nhds_within],
    rintros y (hxy : y < x),
    simp only [comp_app, stieltjes_function.measure_Icc, volume_Icc],
    rw [← ennreal.of_real_div_of_pos (sub_pos.2 hxy), ennreal.to_real_of_real, ← neg_neg (y - x),
        div_neg, neg_div', neg_sub, neg_sub],
    exact div_nonneg (sub_nonneg.2 (f.left_lim_le hxy.le)) (sub_pos.2 hxy).le },
  have L3 : tendsto (λ y, (f.left_lim (y + (x - y)^2) - f x) / (y - x))
    (𝓝[<] x) (𝓝 ((rn_deriv f.measure volume x).to_real)),
  { have fylt : ∀ y ∈ Ioo (x-1) x, y + (x-y)^2 < x,
    { rintros y ⟨hy : x - 1 < y, h'y : y < x⟩, nlinarith },
    have Ioo_lt : Ioo (x - 1) x ∈ 𝓝[<] x,
    { apply Ioo_mem_nhds_within_Iio, exact ⟨by linarith, le_refl _⟩ },
    have L : tendsto (λ y, y + (x - y)^2) (𝓝[<] x) (𝓝[<] x),
    { apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
      { apply tendsto.mono_left _ nhds_within_le_nhds,
        have : tendsto (λ (y : ℝ), y + (x - y) ^ 2) (𝓝 x) (𝓝 (x + (x - x)^2)) :=
          tendsto_id.add ((tendsto.const_sub x tendsto_id).pow 2),
        simpa using this },
      { filter_upwards [Ioo_lt] with y hy using fylt y hy } },
    have L' : tendsto (λ y, (y + (x - y)^2 - x) / (y - x)) (𝓝[<] x) (𝓝 1),
    { have : tendsto (λ y, (1 + (y - x))) (𝓝[<] x) (𝓝 (1 + (x - x))),
      { apply tendsto.mono_left _ nhds_within_le_nhds,
        exact (tendsto_id.sub_const x).const_add 1 },
      simp only [_root_.sub_self, add_zero] at this,
      apply tendsto.congr' _ this,
      filter_upwards [self_mem_nhds_within],
      rintros y (hy : y < x),
      have : y - x < 0, by linarith,
      field_simp [this.ne],
      ring },
    have Z := (L2.comp L).mul L',
    rw mul_one at Z,
    apply tendsto.congr' _ Z,
    filter_upwards [Ioo_lt] with y hy,
    have A : y + (x - y) ^ 2 - x < 0, by linarith [fylt y hy],
    field_simp [A.ne] },
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
  rw [has_deriv_at_iff_tendsto_slope, slope_fun_def_field],
  have : 𝓝[≠] x = 𝓝[<] x ⊔ 𝓝[>] x, by simp only [← nhds_within_union, Iio_union_Ioi],
  rw [this, tendsto_sup],
  exact ⟨L4, L1⟩
end

end real

/-- If a function `f : ℝ → ℝ` is monotone, then the function mapping `x` to the right limit of `f`
at `x` is a Stieltjes function, i.e., it is monotone and right-continuous. -/
noncomputable def stieltjes_function.of_monotone (f : ℝ → ℝ) (hf : monotone f) :
  stieltjes_function :=
{ to_fun := monotone.right_lim f,
  mono' := λ x y hxy, hf.right_lim_le_right_lim hxy,
  right_continuous' :=
  begin
    assume x s hs,
    obtain ⟨l, u, hlu, lus⟩ : ∃ (l u : ℝ), monotone.right_lim f x ∈ Ioo l u ∧ Ioo l u ⊆ s :=
      mem_nhds_iff_exists_Ioo_subset.1 hs,
    obtain ⟨y, xy, h'y⟩ : ∃ (y : ℝ) (H : x < y), Ioc x y ⊆ f ⁻¹' (Ioo l u) :=
      mem_nhds_within_Ioi_iff_exists_Ioc_subset.1
        (hf.tendsto_right_lim x (Ioo_mem_nhds hlu.1 hlu.2)),
    change ∀ᶠ y in 𝓝[≥] x, monotone.right_lim f y ∈ s,
    filter_upwards [Ico_mem_nhds_within_Ici ⟨le_refl x, xy⟩] with z hz,
    apply lus,
    refine ⟨hlu.1.trans_le (hf.right_lim_le_right_lim hz.1), _⟩,
    obtain ⟨a, za, ay⟩ : ∃ (a : ℝ), z < a ∧ a < y := exists_between hz.2,
    calc monotone.right_lim f z ≤ f a : hf.right_lim_le za
                            ... < u   : (h'y ⟨hz.1.trans_lt za, ay.le⟩).2,
  end }

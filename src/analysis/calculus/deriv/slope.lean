import analysis.calculus.deriv

/-!
-/


/-- If the domain has dimension one, then Fréchet derivative is equivalent to the classical
definition with a limit. In this version we have to take the limit along the subset `-{x}`,
because for `y=x` the slope equals zero due to the convention `0⁻¹=0`. -/
lemma has_deriv_at_filter_iff_tendsto_slope {x : 𝕜} {L : filter 𝕜} :
  has_deriv_at_filter f f' x L ↔ tendsto (slope f x) (L ⊓ 𝓟 {x}ᶜ) (𝓝 f') :=
begin
  conv_lhs { simp only [has_deriv_at_filter_iff_tendsto, (norm_inv _).symm,
    (norm_smul _ _).symm, tendsto_zero_iff_norm_tendsto_zero.symm] },
  conv_rhs { rw [← nhds_translation_sub f', tendsto_comap_iff] },
  refine (tendsto_inf_principal_nhds_iff_of_forall_eq $ by simp).symm.trans (tendsto_congr' _),
  refine (eventually_principal.2 $ λ z hz, _).filter_mono inf_le_right,
  simp only [(∘)],
  rw [smul_sub, ← mul_smul, inv_mul_cancel (sub_ne_zero.2 hz), one_smul, slope_def_module]
end

lemma has_deriv_within_at_iff_tendsto_slope :
  has_deriv_within_at f f' s x ↔ tendsto (slope f x) (𝓝[s \ {x}] x) (𝓝 f') :=
begin
  simp only [has_deriv_within_at, nhds_within, diff_eq, inf_assoc.symm, inf_principal.symm],
  exact has_deriv_at_filter_iff_tendsto_slope
end

lemma has_deriv_within_at_iff_tendsto_slope' (hs : x ∉ s) :
  has_deriv_within_at f f' s x ↔ tendsto (slope f x) (𝓝[s] x) (𝓝 f') :=
begin
  convert ← has_deriv_within_at_iff_tendsto_slope,
  exact diff_singleton_eq_self hs
end

lemma has_deriv_at_iff_tendsto_slope :
  has_deriv_at f f' x ↔ tendsto (slope f x) (𝓝[≠] x) (𝓝 f') :=
has_deriv_at_filter_iff_tendsto_slope

/-! ### Upper estimates on liminf and limsup -/

section real

variables {f : ℝ → ℝ} {f' : ℝ} {s : set ℝ} {x : ℝ} {r : ℝ}

lemma has_deriv_within_at.limsup_slope_le (hf : has_deriv_within_at f f' s x) (hr : f' < r) :
  ∀ᶠ z in 𝓝[s \ {x}] x, slope f x z < r :=
has_deriv_within_at_iff_tendsto_slope.1 hf (is_open.mem_nhds is_open_Iio hr)

lemma has_deriv_within_at.limsup_slope_le' (hf : has_deriv_within_at f f' s x)
  (hs : x ∉ s) (hr : f' < r) :
  ∀ᶠ z in 𝓝[s] x, slope f x z < r :=
(has_deriv_within_at_iff_tendsto_slope' hs).1 hf (is_open.mem_nhds is_open_Iio hr)

lemma has_deriv_within_at.liminf_right_slope_le
  (hf : has_deriv_within_at f f' (Ici x) x) (hr : f' < r) :
  ∃ᶠ z in 𝓝[>] x, slope f x z < r :=
(hf.Ioi_of_Ici.limsup_slope_le' (lt_irrefl x) hr).frequently

end real

section real_space

open metric

variables {E : Type u} [normed_add_comm_group E] [normed_space ℝ E] {f : ℝ → E} {f' : E} {s : set ℝ}
  {x r : ℝ}

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ‖f'‖` the ratio
`‖f z - f x‖ / ‖z - x‖` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `‖f'‖`. -/
lemma has_deriv_within_at.limsup_norm_slope_le
  (hf : has_deriv_within_at f f' s x) (hr : ‖f'‖ < r) :
  ∀ᶠ z in 𝓝[s] x, ‖z - x‖⁻¹ * ‖f z - f x‖ < r :=
begin
  have hr₀ : 0 < r, from lt_of_le_of_lt (norm_nonneg f') hr,
  have A : ∀ᶠ z in 𝓝[s \ {x}] x, ‖(z - x)⁻¹ • (f z - f x)‖ ∈ Iio r,
    from (has_deriv_within_at_iff_tendsto_slope.1 hf).norm (is_open.mem_nhds is_open_Iio hr),
  have B : ∀ᶠ z in 𝓝[{x}] x, ‖(z - x)⁻¹ • (f z - f x)‖ ∈ Iio r,
    from mem_of_superset self_mem_nhds_within
      (singleton_subset_iff.2 $ by simp [hr₀]),
  have C := mem_sup.2 ⟨A, B⟩,
  rw [← nhds_within_union, diff_union_self, nhds_within_union, mem_sup] at C,
  filter_upwards [C.1],
  simp only [norm_smul, mem_Iio, norm_inv],
  exact λ _, id
end

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ‖f'‖` the ratio
`(‖f z‖ - ‖f x‖) / ‖z - x‖` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `‖f'‖`.

This lemma is a weaker version of `has_deriv_within_at.limsup_norm_slope_le`
where `‖f z‖ - ‖f x‖` is replaced by `‖f z - f x‖`. -/
lemma has_deriv_within_at.limsup_slope_norm_le
  (hf : has_deriv_within_at f f' s x) (hr : ‖f'‖ < r) :
  ∀ᶠ z in 𝓝[s] x, ‖z - x‖⁻¹ * (‖f z‖ - ‖f x‖) < r :=
begin
  apply (hf.limsup_norm_slope_le hr).mono,
  assume z hz,
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (norm_sub_norm_le _ _) _) hz,
  exact inv_nonneg.2 (norm_nonneg _)
end

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ‖f'‖` the ratio
`‖f z - f x‖ / ‖z - x‖` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `‖f'‖`. See also `has_deriv_within_at.limsup_norm_slope_le`
for a stronger version using limit superior and any set `s`. -/
lemma has_deriv_within_at.liminf_right_norm_slope_le
  (hf : has_deriv_within_at f f' (Ici x) x) (hr : ‖f'‖ < r) :
  ∃ᶠ z in 𝓝[>] x, ‖z - x‖⁻¹ * ‖f z - f x‖ < r :=
(hf.Ioi_of_Ici.limsup_norm_slope_le hr).frequently

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ‖f'‖` the ratio
`(‖f z‖ - ‖f x‖) / (z - x)` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `‖f'‖`.

See also

* `has_deriv_within_at.limsup_norm_slope_le` for a stronger version using
  limit superior and any set `s`;
* `has_deriv_within_at.liminf_right_norm_slope_le` for a stronger version using
  `‖f z - f x‖` instead of `‖f z‖ - ‖f x‖`. -/
lemma has_deriv_within_at.liminf_right_slope_norm_le
  (hf : has_deriv_within_at f f' (Ici x) x) (hr : ‖f'‖ < r) :
  ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (‖f z‖ - ‖f x‖) < r :=
begin
  have := (hf.Ioi_of_Ici.limsup_slope_norm_le hr).frequently,
  refine this.mp (eventually.mono self_mem_nhds_within _),
  assume z hxz hz,
  rwa [real.norm_eq_abs, abs_of_pos (sub_pos_of_lt hxz)] at hz
end

end real_space

import analysis.normed_space.spectrum
import analysis.complex.liouville

/-! This file shows that the spectrum in a (nontrivial) complex Banach algebra is nonempty. -/

section algebra_algebra_spectrum

open spectrum

variables {R A : Type*} [comm_ring R] [ring A] [algebra R A]

/-- The unit `1 - r⁻¹ • a` constructed from `r • 1 - a` when the latter is a unit. -/
@[simps]
def units.sub_inv_smul {r : Rˣ} {a : A}
  {u : Aˣ} (h : (u : A) = r • 1 - a) : Aˣ :=
{ val := 1 - r⁻¹ • a,
  inv := r • ↑u⁻¹,
  val_inv := by { rw [mul_smul_comm, ←smul_mul_assoc, smul_sub, smul_inv_smul, ←h],
                  exact u.val_inv },
  inv_val := by { rw [smul_mul_assoc, ←mul_smul_comm, smul_sub, smul_inv_smul, ←h],
                  exact u.inv_val } }

lemma spectrum.smul_resolvent_self {r : Rˣ} {a : A} :
  r • resolvent a (r : R) = resolvent (r⁻¹ • a) (1 : R) :=
begin
  by_cases h : (r : R) ∈ spectrum R a,
  { rw [mem_iff] at h,
    simp only [resolvent, algebra.algebra_map_eq_smul_one, ←units.smul_def, one_smul] at *,
    have h' := (not_iff_not.mpr is_unit.smul_sub_iff_sub_inv_smul).mp h,
    simp only [ring.inverse_non_unit _ h, ring.inverse_non_unit _ h', smul_zero] },
  { rw not_mem_iff at h,
    simp only [resolvent, algebra.algebra_map_eq_smul_one, ←units.smul_def, one_smul] at *,
    rcases h with ⟨u, hu⟩,
    rw [←hu, ←units.coe_sub_inv_smul hu, ring.inverse_unit, ←units.coe_inv_sub_inv_smul hu,
      ring.inverse_unit] },
end

/- The resolvent is a unit when the argument is in the resolvent set. -/
lemma spectrum.is_unit_resolvent {r : R} {a : A} (h : r ∈ resolvent_set R a) :
  is_unit (resolvent a r) :=
(resolvent_eq h).symm ▸ ⟨⟨(h.unit⁻¹ : Aˣ), h.unit, _, _⟩, rfl⟩

end algebra_algebra_spectrum

section analysis_normed_space_spectrum

open spectrum asymptotics filter

variables
{𝕜 A : Type*}
[nondiscrete_normed_field 𝕜] [normed_ring A]
[normed_algebra 𝕜 A] [complete_space A]

/- this wants to be `tendsto (λ z, ∥resolvent a z∥) (cobounded 𝕜) (𝓝 0)` where `cobounded 𝕜` is the
natural bornology on `𝕜`, but the definition of bornology hasn't been merged yet, let along the API
developed. Another option until that is developed would be
`tendsto (λ z, ∥resolvent a z∥) (comap norm at_top) (𝓝 0)` because we will have the propositional
equality `cobounded 𝕜 = comap norm at_top` eventually. However, I just left it like this for now
to keep it as easy as possible to use in `spectrum.nonempty`. We can actually be more specific than
the above if we wanted as well since we can give the asymptotics explicitly:
`is_O (resolvent a) (λ z, z⁻¹) (cobounded 𝕜)`. In fact, the latter should be easy to show once we
have the API for `cobounded 𝕜` developed. Namely, we will eventually have the result that in a
nondiscrete normed field that `map inv (𝓝[≠] 0) = cobounded 𝕜` and vice versa, from this it should
be just be pretty straightforward to prove the asymptotics and turn this whole lemma into something
the way a mathematician would argue it using `normed_ring.inverse_one_sub_norm` -/

lemma spectrum.norm_resolvent_le (a : A) :
  ∀ ε > 0, ∃ R > 0, ∀ z : 𝕜, R ≤ ∥z∥ → ∥resolvent a z∥ ≤ ε :=
begin
  obtain ⟨c, c_pos, hc⟩ := (@normed_ring.inverse_one_sub_norm A _ _).exists_pos,
  rw [is_O_with_iff, eventually_iff, metric.mem_nhds_iff] at hc,
  rcases hc with ⟨δ, δ_pos, hδ⟩,
  simp only [cstar_ring.norm_one, mul_one] at hδ,
  intros ε hε,
  have ha₁ : 0 < ∥a∥ + 1 := lt_of_le_of_lt (norm_nonneg a) (lt_add_one _),
  have min_pos : 0 < min (δ * (∥a∥ + 1)⁻¹) (ε * c⁻¹),
    from lt_min (mul_pos δ_pos (inv_pos.mpr ha₁)) (mul_pos hε (inv_pos.mpr c_pos)),
  refine ⟨(min (δ * (∥a∥ + 1)⁻¹) (ε * c⁻¹))⁻¹, inv_pos.mpr min_pos, (λ z hz, _)⟩,
  have hnz : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (inv_pos.mpr min_pos) hz),
  replace hz := inv_le_of_inv_le min_pos hz,
  rcases (⟨units.mk0 z hnz, units.coe_mk0 hnz⟩ : is_unit z) with ⟨z, rfl⟩,
  have lt_δ : ∥z⁻¹ • a∥ < δ,
  { rw [units.smul_def, norm_smul, units.coe_inv', normed_field.norm_inv],
    calc ∥(z : 𝕜)∥⁻¹ * ∥a∥ ≤ δ * (∥a∥ + 1)⁻¹ * ∥a∥
        : mul_le_mul_of_nonneg_right (hz.trans (min_le_left _ _)) (norm_nonneg _)
    ...                   < δ
        : by { conv { rw mul_assoc, to_rhs, rw (mul_one δ).symm },
               exact mul_lt_mul_of_pos_left
                 ((inv_mul_lt_iff ha₁).mpr ((mul_one (∥a∥ + 1)).symm ▸ (lt_add_one _))) δ_pos } },
  rw [←inv_smul_smul z (resolvent a (z : 𝕜)), smul_resolvent_self, resolvent,
    algebra.algebra_map_eq_smul_one, one_smul, units.smul_def, norm_smul, units.coe_inv',
    normed_field.norm_inv],
  calc _ ≤ ε * c⁻¹ * c : mul_le_mul (hz.trans (min_le_right _ _)) (hδ (mem_ball_zero_iff.mpr lt_δ))
                           (norm_nonneg _) (mul_pos hε (inv_pos.mpr c_pos)).le
  ...    = _           : inv_mul_cancel_right₀ c_pos.ne.symm ε,
end

end analysis_normed_space_spectrum


open spectrum


local notation `σ` := spectrum ℂ

/-- In a (nontrivial) complex Banach algebra, every element has nonempty spectrum. -/
theorem spectrum.nonempty {A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
  [nontrivial A] [topological_space.second_countable_topology A] [measurable_space A]
  [borel_space A] (a : A) : (σ a).nonempty :=
begin
  /- Suppose `σ a = ∅`, then resolvent set is `ℂ`, any `(z • 1 - a)` is a unit, and `resolvent`
  is differentiable on `ℂ`. -/
  rw ←set.ne_empty_iff_nonempty,
  by_contra h,
  have H₀ : resolvent_set ℂ a = set.univ, by rwa [spectrum, set.compl_empty_iff] at h,
  have H₁ : differentiable ℂ (λ z : ℂ, resolvent a z), from λ z,
    (has_deriv_at_resolvent (H₀.symm ▸ set.mem_univ z : z ∈ resolvent_set ℂ a)).differentiable_at,
  /- The norm of the resolvent is small for all sufficently large `z`, and by compactness and
  continuity it is bounded on the complement of a large ball, thus uniformly bounded on `ℂ`.
  By Liouville's theorem `λ z, resolvent a z` is constant -/
  have H₂ := norm_resolvent_le a,
  have H₃ : ∀ z : ℂ, resolvent a z = resolvent a (0 : ℂ),
  { refine λ z, complex.apply_eq_apply_of_differentiable_of_bounded H₁ _ z 0,
    rw bounded_iff_exists_norm_le,
    rcases H₂ 1 zero_lt_one with ⟨R, R_pos, hR⟩,
    rcases (proper_space.is_compact_closed_ball (0 : ℂ) R).exists_bound_of_continuous_on
      H₁.continuous.continuous_on with ⟨C, hC⟩,
    use max C 1,
    rintros _ ⟨w, rfl⟩,
    refine or.elim (em (∥w∥ ≤ R)) (λ hw, _) (λ hw, _),
      { exact (hC w (mem_closed_ball_zero_iff.mpr hw)).trans (le_max_left _ _) },
      { exact (hR w (not_le.mp hw).le).trans (le_max_right _ _), }, },
  /- `resolvent a 0 = 0`, which is a contradition because it isn't a unit. -/
  have H₅ : resolvent a (0 : ℂ) = 0,
  { refine norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add (λ ε hε, _)) (norm_nonneg _)),
    rcases H₂ ε hε with ⟨R, R_pos, hR⟩,
    simpa only [H₃ R] using (zero_add ε).symm.subst
      (hR R (by exact_mod_cast (real.norm_of_nonneg R_pos.lt.le).symm.le)), },
  /- `not_is_unit_zero` is where we need `nontrivial A`, it is unavoidable. -/
  exact not_is_unit_zero (H₅.subst (is_unit_resolvent
    (mem_resolvent_set_iff.mp (H₀.symm ▸ set.mem_univ 0)))),
end

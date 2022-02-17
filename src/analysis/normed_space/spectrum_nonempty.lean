import analysis.normed_space.spectrum
import analysis.complex.cauchy_integral

/-! This is the proof that the spectrum is nonempty -/

variables
{A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
namespace spectrum



local notation `σ` := spectrum ℂ

open_locale topological_space
open filter asymptotics

set_option profiler true


def _root_.units.sub_inv_smul {R : Type*} {A : Type*}
  [comm_ring R] [ring A] [algebra R A] {r : Rˣ} {a : A}
  {u : Aˣ} (h : (u : A) = r • 1 - a) : Aˣ :=
{ val := 1 - r⁻¹ • a,
  inv := r • ↑u⁻¹,
  val_inv := by { rw [mul_smul_comm, ←smul_mul_assoc, smul_sub, smul_inv_smul, ←h],
                  exact u.val_inv },
  inv_val := by { rw [smul_mul_assoc, ←mul_smul_comm, smul_sub, smul_inv_smul, ←h],
                  exact u.inv_val } }

lemma _root_.units.sub_inv_smul_coe_eq {R : Type*} {A : Type*}
  [comm_ring R] [ring A] [algebra R A] {r : Rˣ} {a : A}
  {u : Aˣ} (h : (u : A) = r • 1 - a) :
  ↑(units.sub_inv_smul h) = 1 - r⁻¹ • a :=
rfl

lemma _root_.units.sub_inv_smul_coe_inv_eq {R : Type*} {A : Type*}
  [comm_ring R] [ring A] [algebra R A] {r : Rˣ} {a : A}
  {u : Aˣ} (h : (u : A) = r • 1 - a) :
  (↑(units.sub_inv_smul h)⁻¹ : A) = r • ↑u⁻¹ :=
rfl

lemma smul_resolvent_self (z : ℂˣ) (a : A) :
  z • resolvent a (z : ℂ) = resolvent (z⁻¹ • a) (1 : ℂ) :=
begin
  by_cases h : (z : ℂ) ∈ σ a,
  { rw [mem_iff] at h,
    simp only [resolvent, algebra.algebra_map_eq_smul_one, ←units.smul_def, one_smul] at *,
    have h' := (not_iff_not.mpr is_unit.smul_sub_iff_sub_inv_smul).mp h,
    simp only [ring.inverse_non_unit _ h, ring.inverse_non_unit _ h', smul_zero] },
  { rw not_mem_iff at h,
    simp only [resolvent, algebra.algebra_map_eq_smul_one, ←units.smul_def, one_smul] at *,
    rcases h with ⟨u, hu⟩,
    rw [←hu, ←units.sub_inv_smul_coe_eq hu, ring.inverse_unit, ←units.sub_inv_smul_coe_inv_eq hu,
      ring.inverse_unit] },
end

lemma is_unit_resolvent {z : ℂ} {a : A} (h : z ∈ resolvent_set ℂ a) :
  is_unit (resolvent a z) :=
begin
  rw mem_resolvent_set_iff at h,
  rw resolvent_eq h,
  exact ⟨⟨(h.unit⁻¹ : Aˣ), h.unit, _, _⟩, rfl⟩,
end


lemma norm_resolvent_le (a : A) (hna : a ≠ 0) :
  ∀ ε > 0, ∃ R > 0, ∀ z : ℂˣ, R ≤ ∥(z : ℂ)∥ → ∥resolvent a (z : ℂ)∥ ≤ ε :=
begin
  obtain ⟨c, c_pos, hc⟩ := (@normed_ring.inverse_one_sub_norm A _ _).exists_pos,
  rw [is_O_with_iff, eventually_iff, metric.mem_nhds_iff] at hc,
  rcases hc with ⟨δ, δ_pos, hδ⟩,
  simp only [cstar_ring.norm_one, mul_one] at hδ,
  intros ε hε,
  have min_pos : 0 < min (δ / 2 * ∥a∥⁻¹) (ε * c⁻¹),
    from lt_min (mul_pos (half_pos δ_pos) (inv_pos.mpr (norm_pos_iff.mpr hna)))
      (mul_pos hε (inv_pos.mpr c_pos)),
  refine ⟨(min (δ / 2 * ∥a∥⁻¹) (ε * c⁻¹))⁻¹, inv_pos.mpr min_pos, (λ z hz, _)⟩,
  have hnz : 0 < ∥(z : ℂ)∥ := norm_pos_iff.mpr (λ hz', not_is_unit_zero ⟨z, hz'⟩),
  replace hz := inv_le_of_inv_le min_pos hz,
  have lt_δ : ∥z⁻¹ • a∥ < δ,
  { rw [units.smul_def, norm_smul, units.coe_inv', normed_field.norm_inv],
  calc ∥(z : ℂ)∥⁻¹ * ∥a∥ ≤ (δ / 2) * ∥a∥⁻¹ * ∥a∥
      : mul_le_mul_of_nonneg_right (hz.trans (min_le_left _ _)) (norm_nonneg _)
  ...                   = δ / 2 : inv_mul_cancel_right₀ (norm_pos_iff.mpr hna).ne.symm _
  ...                   < _ : half_lt_self δ_pos },
  rw [←inv_smul_smul z (resolvent a (z : ℂ)), smul_resolvent_self, resolvent,
    algebra.algebra_map_eq_smul_one, one_smul, units.smul_def, norm_smul, units.coe_inv',
    normed_field.norm_inv],
  calc _ ≤ ε * c⁻¹ * c
         : by { refine mul_le_mul _ _ _ _,
                exact (hz.trans (min_le_right _ _)),
                exact hδ (mem_ball_zero_iff.mpr lt_δ),
                exact (norm_nonneg _),
                exact (mul_pos hε (inv_pos.mpr c_pos)).le, }
  ...    = _ : inv_mul_cancel_right₀ c_pos.ne.symm ε,
end

variables [nontrivial A] [measurable_space A] [borel_space A] [topological_space.second_countable_topology A]

theorem spectrum.nonempty (a : A) : (spectrum ℂ a).nonempty :=
begin
  /- Suppose the spectrum is empty -/
  rw ←set.ne_empty_iff_nonempty,
  by_contra' h,
  /- `a ≠ 0` is `A` is nontrivial. We don't strictly need this, but it makes things
  convenient later. -/
  have hna : a ≠ 0, from λ ha, by
  { rw ha at h,
    simpa only [←h, spectrum.zero_eq] using (set.singleton_nonempty (0 : ℂ)).ne_empty, },
  /- The resolvent set is `ℂ` and every `(z • 1 - a)` is a unit. -/
  have H₀ : resolvent_set ℂ a = set.univ,
  { rwa [spectrum, set.compl_empty_iff] at h, },
  have H₀' : ∀ z : ℂ, is_unit (algebra_map ℂ A z - a) :=
    λ z, spectrum.mem_resolvent_set_iff.mp (H₀.symm ▸ set.mem_univ z),
  /- The resolvent is differentiable on `ℂ`. -/
  have H₁ : differentiable ℂ (λ z : ℂ, resolvent a z),
  { refine λ z, (has_deriv_at_resolvent _).differentiable_at,
    rw H₀,
    trivial, },
  /- The norm of the resolvent is small for all sufficently large `z`. restrict to units for
  convenience in the proof. -/
  have H₂ := norm_resolvent_le a hna,
  have H₃ : ∃ C : ℝ, ∀ z : ℂ, ∥resolvent a (z : ℂ)∥ ≤ C,
  { rcases H₂ 1 zero_lt_one with ⟨R, R_pos, hR⟩,
    rcases (proper_space.is_compact_closed_ball (0 : ℂ) R).exists_bound_of_continuous_on
      H₁.continuous.continuous_on with ⟨C, hC⟩,
    refine ⟨max C 1, (λ z, _)⟩,
    by_cases hz : ∥z∥ ≤ R,
    { exact (hC z (mem_closed_ball_zero_iff.mpr hz)).trans (le_max_left _ _) },
    { push_neg at hz,
      have := norm_pos_iff.mp (lt_trans R_pos hz),
      refine (hR (units.mk0 z this) _).trans (le_max_right _ _),
      rw units.coe_mk0 this,
      exact hz.le }, },
  /- apply Liouville's theorem to conclude `λ z, resolvent a z` is constant-/
  rcases H₃ with ⟨C, hC⟩,
  have H₄ := H₁.const_of_bounded hC,
  /- Since the resolvent is constant and has arbitrarily small norm at infinity it must be 0. -/
  have H₅ : resolvent a (0 : ℂ) = 0,
  { refine norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add (λ ε hε, _)) (norm_nonneg _)),
    rcases H₂ ε hε with ⟨R, R_pos, hR⟩,
    have foo₁ : (R : ℂ) ≠ 0, by exact_mod_cast R_pos.lt.ne.symm,
    rw zero_add ε,
    have foo₂ := hR (units.mk0 R foo₁) (by simpa only [units.coe_mk0, complex.norm_real] using le_abs_self R),
    simp only [units.coe_mk0] at foo₂,
    have foo₃ := congr_fun H₄ (R : ℂ),
    simp at foo₃,
    simpa only [←foo₃] using foo₂, },
  /- `not_is_unit_zero` is what requires `nontrivial A`. -/
  exact not_is_unit_zero (H₅.subst (is_unit_resolvent (H₀' 0))),
end

end spectrum

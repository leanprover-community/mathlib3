/-
Copyright (c) 2022 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich
-/
import measure_theory.measure.measure_space

/-!
# Subtraction of measures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `μ - ν` to be the least measure `τ` such that `μ ≤ τ + ν`.
It is the equivalent of `(μ - ν) ⊔ 0` if `μ` and `ν` were signed measures.
Compare with `ennreal.has_sub`.
Specifically, note that if you have `α = {1,2}`, and  `μ {1} = 2`, `μ {2} = 0`, and
`ν {2} = 2`, `ν {1} = 0`, then `(μ - ν) {1, 2} = 2`. However, if `μ ≤ ν`, and
`ν univ ≠ ∞`, then `(μ - ν) + ν = μ`.
-/

open set

namespace measure_theory

namespace measure

/-- The measure `μ - ν` is defined to be the least measure `τ` such that `μ ≤ τ + ν`.
It is the equivalent of `(μ - ν) ⊔ 0` if `μ` and `ν` were signed measures.
Compare with `ennreal.has_sub`.
Specifically, note that if you have `α = {1,2}`, and  `μ {1} = 2`, `μ {2} = 0`, and
`ν {2} = 2`, `ν {1} = 0`, then `(μ - ν) {1, 2} = 2`. However, if `μ ≤ ν`, and
`ν univ ≠ ∞`, then `(μ - ν) + ν = μ`. -/
noncomputable instance has_sub {α : Type*} [measurable_space α] : has_sub (measure α) :=
⟨λ μ ν, Inf {τ | μ ≤ τ + ν} ⟩

variables {α : Type*} {m : measurable_space α} {μ ν : measure α} {s : set α}

lemma sub_def : μ - ν = Inf {d | μ ≤ d + ν} := rfl

lemma sub_le_of_le_add {d} (h : μ ≤ d + ν) : μ - ν ≤ d := Inf_le h

lemma sub_eq_zero_of_le (h : μ ≤ ν) : μ - ν = 0 :=
nonpos_iff_eq_zero'.1 $ sub_le_of_le_add $ by rwa zero_add

lemma sub_le : μ - ν ≤ μ :=
sub_le_of_le_add $ measure.le_add_right le_rfl

@[simp] lemma sub_top : μ - ⊤ = 0 := sub_eq_zero_of_le le_top
@[simp] lemma zero_sub : 0 - μ = 0 := sub_eq_zero_of_le μ.zero_le
@[simp] lemma sub_self : μ - μ = 0 := sub_eq_zero_of_le le_rfl

/-- This application lemma only works in special circumstances. Given knowledge of
when `μ ≤ ν` and `ν ≤ μ`, a more general application lemma can be written. -/
lemma sub_apply [is_finite_measure ν] (h₁ : measurable_set s) (h₂ : ν ≤ μ) :
  (μ - ν) s = μ s - ν s :=
begin
  -- We begin by defining `measure_sub`, which will be equal to `(μ - ν)`.
  let measure_sub : measure α := @measure_theory.measure.of_measurable α _
    (λ (t : set α) (h_t_measurable_set : measurable_set t), (μ t - ν t))
    begin
      simp
    end
    begin
      intros g h_meas h_disj, simp only, rw ennreal.tsum_sub,
      repeat { rw ← measure_theory.measure_Union h_disj h_meas },
      exacts [measure_theory.measure_ne_top _ _, λ i, h₂ _ (h_meas _)]
    end,
  -- Now, we demonstrate `μ - ν = measure_sub`, and apply it.
  begin
    have h_measure_sub_add : (ν + measure_sub = μ),
    { ext t h_t_measurable_set,
      simp only [pi.add_apply, coe_add],
      rw [measure_theory.measure.of_measurable_apply _ h_t_measurable_set, add_comm,
        tsub_add_cancel_of_le (h₂ t h_t_measurable_set)] },
    have h_measure_sub_eq : (μ - ν) = measure_sub,
    { rw measure_theory.measure.sub_def, apply le_antisymm,
      { apply @Inf_le (measure α) measure.complete_semilattice_Inf,
        simp [le_refl, add_comm, h_measure_sub_add] },
      apply @le_Inf (measure α) measure.complete_semilattice_Inf,
      intros d h_d, rw [← h_measure_sub_add, mem_set_of_eq, add_comm d] at h_d,
      apply measure.le_of_add_le_add_left h_d },
    rw h_measure_sub_eq,
    apply measure.of_measurable_apply _ h₁,
  end
end

lemma sub_add_cancel_of_le [is_finite_measure ν] (h₁ : ν ≤ μ) : μ - ν + ν = μ :=
begin
  ext s h_s_meas,
  rw [add_apply, sub_apply h_s_meas h₁, tsub_add_cancel_of_le (h₁ s h_s_meas)],
end

lemma restrict_sub_eq_restrict_sub_restrict (h_meas_s : measurable_set s) :
  (μ - ν).restrict s = (μ.restrict s) - (ν.restrict s) :=
begin
  repeat {rw sub_def},
  have h_nonempty : {d | μ ≤ d + ν}.nonempty, from ⟨μ, measure.le_add_right le_rfl⟩,
  rw restrict_Inf_eq_Inf_restrict h_nonempty h_meas_s,
  apply le_antisymm,
  { refine Inf_le_Inf_of_forall_exists_le _,
    intros ν' h_ν'_in, rw mem_set_of_eq at h_ν'_in,
    refine ⟨ν'.restrict s, _, restrict_le_self⟩,
    refine ⟨ν' + (⊤ : measure α).restrict sᶜ, _, _⟩,
    { rw [mem_set_of_eq, add_right_comm, measure.le_iff],
      intros t h_meas_t,
      repeat { rw ← measure_inter_add_diff t h_meas_s },
      refine add_le_add _ _,
      { rw [add_apply, add_apply],
        apply le_add_right _,
        rw [← restrict_eq_self μ (inter_subset_right _ _),
          ← restrict_eq_self ν (inter_subset_right _ _)],
        apply h_ν'_in _ (h_meas_t.inter h_meas_s) },
      { rw [add_apply, restrict_apply (h_meas_t.diff h_meas_s), diff_eq, inter_assoc,
          inter_self, ← add_apply],
        have h_mu_le_add_top : μ ≤ ν' + ν + ⊤, by simp only [add_top, le_top],
        exact measure.le_iff'.1 h_mu_le_add_top _ } },
    { ext1 t h_meas_t,
      simp [restrict_apply h_meas_t, restrict_apply (h_meas_t.inter h_meas_s), inter_assoc] } },
  { refine Inf_le_Inf_of_forall_exists_le _,
    refine ball_image_iff.2 (λ t h_t_in, ⟨t.restrict s, _, le_rfl⟩),
    rw [set.mem_set_of_eq, ← restrict_add],
    exact restrict_mono subset.rfl h_t_in }
end

lemma sub_apply_eq_zero_of_restrict_le_restrict
  (h_le : μ.restrict s ≤ ν.restrict s) (h_meas_s : measurable_set s) :
  (μ - ν) s = 0 :=
by rw [← restrict_apply_self, restrict_sub_eq_restrict_sub_restrict, sub_eq_zero_of_le]; simp *

instance is_finite_measure_sub [is_finite_measure μ] : is_finite_measure (μ - ν) :=
is_finite_measure_of_le μ sub_le

end measure

end measure_theory

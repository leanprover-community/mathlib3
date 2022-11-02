import measure_theory.integral.lebesgue

open_locale big_operators

lemma ae_not_top_of_has_finite_integral {α : Type*} {m : measurable_space α} {μ : measure_theory.measure α} {f : α → ennreal}
  (h : ∫⁻ (a : α), f a ∂μ < ⊤) (hf : measurable f) :
  ∀ᵐ (a : α) ∂μ,  f a < ⊤  :=
begin
  refine measure_theory.ae_lt_top hf _,
  exact ne_of_lt h,
end

/--

  rw measure_theory.ae_iff,
  set s := {a : α | ¬ f a < ⊤},
  by_contra hs,
  have μ_pos : μ s > 0 := zero_lt_iff.mpr hs,
  let g : α → ennreal := λ a, if a∈s then 1 else 0,
  have : g ≤ f,
  { intros a,
    by_cases ha : a ∈ s,
    { have : ¬ f a < ⊤ := ha,
      rw not_lt_top_iff at this,
      rw this,
      simp, },
    { have : g a = 0,
      { simp only [ite_eq_right_iff, set.mem_set_of_eq, not_lt_top_iff, one_ne_zero],
        have : ¬ ¬ f a < ⊤ := ha,
        push_neg at this,
        intros hfa,
        exact lt_top_iff_ne_top.mp this hfa, },
      rw this,
      simp, }, },
  have int_g_le_int_f : ∫⁻ (a : α), g a ∂μ ≤ ∫⁻ (a : α), f a ∂μ := measure_theory.lintegral_mono this,
  have : ⊤ ≤ ∫⁻ (a : α), g a ∂μ,
  { rw top_le_iff,
    sorry, },
  have int_f_eq_top : ∫⁻ (a : α), f a ∂μ = ⊤,
  { rw ← top_le_iff,
    calc ⊤ ≤ ∫⁻ (a : α), g a ∂μ : this
    ... ≤ ∫⁻ (a : α), f a ∂μ : int_g_le_int_f, },
  exact ennreal.not_lt_top.mpr int_f_eq_top h,

-/

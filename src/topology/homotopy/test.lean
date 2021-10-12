import topology.homotopy.path

universe u

variables {X : Type u} [topological_space X]

variables {x₀ x₁ x₂ x₃ : X}

noncomputable theory

open_locale unit_interval

def g_aux (t : I) : ℝ :=
  if (t : ℝ) ≤ 1/4 then
    2 * t
  else if (t : ℝ) ≤ 1/2 then
    t + 1/4
  else
    1/2 * (t + 1)

lemma g_aux_le_half_iff (t : I) : g_aux t ≤ 1/2 ↔ (t : ℝ) ≤ 1/2 :=
begin
  sorry
end

@[continuity]
lemma continuous_g_aux : continuous g_aux :=
begin
  refine continuous_if_le _ _ (continuous.continuous_on _) (continuous_if_le _ _ (continuous.continuous_on _) (continuous.continuous_on _) _).continuous_on _;
    [continuity, continuity, continuity, continuity, continuity, continuity, continuity,
     skip, skip];
    { intros x hx,
      norm_num [hx], }
end

lemma g_aux_mem_I (t : I) : g_aux t ∈ I :=
begin
  unfold g_aux,
  split_ifs; split; linarith [unit_interval.le_one t, unit_interval.nonneg t]
end

lemma g_aux_zero : g_aux 0 = 0 :=
by norm_num [g_aux]

lemma g_aux_one : g_aux 1 = 1 :=
by norm_num [g_aux]

example {x₀ x₁ x₂ x₃ : X} (p : path x₀ x₁) (q : path x₁ x₂) (r : path x₂ x₃) :
  p.trans (q.trans r) = ((p.trans q).trans r).reparam (λ t, ⟨g_aux t, g_aux_mem_I t⟩)
    (by continuity) (subtype.ext g_aux_zero) (subtype.ext g_aux_one) :=
begin
  ext,
  simp,
end

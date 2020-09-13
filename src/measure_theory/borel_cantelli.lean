import measure_theory.measure_space tactic

universe u

open measure_theory filter
open_locale filter topological_space

section
variables {α : Type u} [complete_lattice α]

lemma limsup_eq_infi_supr_of_nat' {u : ℕ → α} : limsup at_top u = ⨅n:ℕ, ⨆i, u (i + n) :=
begin
  rw limsup_eq_infi_supr_of_nat,
  congr,
  ext,
  apply le_antisymm,
  { simp only [supr_le_iff, ge_iff_le],
    intros i hi,
    rw show i = (i - x) + x, by omega,
    apply le_Sup,
    use i - x },
  { simp only [supr_le_iff, ge_iff_le],
    intro i,
    apply le_Sup,
    use i + x,
    simp }
end

end

section

lemma tendsto_sum_add (f : ℕ → ennreal) (hf : (∑' i, f i) < ⊤) :
  tendsto (λ i, ∑' k, f (k + i)) at_top (𝓝 0) :=
begin
  rw ennreal.tendsto_nhds ennreal.zero_ne_top,

  sorry,
end


end

section

variables {α : Type u} [measurable_space α] {μ : measure α}
variables {s : ℕ → set α} (hs : ∀ i, is_measurable (s i))
variables (hs' : (∑' i, μ (s i)) < ⊤)

include hs hs'

/-- The Borel-Cantelli lemma. -/
lemma measure_limsup_eq_zero : μ (limsup at_top s) = 0 :=
begin
  rw limsup_eq_infi_supr_of_nat',

  refine tendsto_nhds_unique
    (tendsto_measure_Inter (λ i, is_measurable.Union (λ b, hs (b + i))) _
      ⟨0, lt_of_le_of_lt (measure_Union_le s) hs'⟩)
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_sum_add (μ ∘ s) hs')
      (eventually_of_forall (by simp only [forall_const, zero_le]))
      (eventually_of_forall (λ i, measure_Union_le _))),

  intros n m hnm x hx,
  simp only [set.mem_Union] at hx ⊢,
  rcases hx with ⟨i, hi⟩,
  use i + (m - n),
  convert hi using 2,
  omega
end

end

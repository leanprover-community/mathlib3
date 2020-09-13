import measure_theory.measure_space tactic

universe u

open measure_theory filter
open_locale filter topological_space

section
variables {α : Type u} [complete_lattice α]

lemma limsup_eq_infi_supr_of_nat' {u : ℕ → α} : limsup at_top u = ⨅n:ℕ, ⨆i, u (n + i) :=
begin
  rw limsup_eq_infi_supr_of_nat,
  congr,
  ext,
  apply le_antisymm,
  { simp only [supr_le_iff, ge_iff_le],
    intros i hi,
    rw show i = x + (i - x), by omega,
    apply le_Sup,
    use i - x },
  { simp only [supr_le_iff, ge_iff_le],
    intro i,
    apply le_Sup,
    use x + i,
    simp }
end

end

section

lemma nnreal.sub_lt_iff {a b c : nnreal} (h : b ≤ a) : a - b < c ↔ a < b + c :=
begin
  rw [←nnreal.coe_lt_coe, ←nnreal.coe_lt_coe, nnreal.coe_sub h, nnreal.coe_add],
  exact sub_lt_iff_lt_add'
end

lemma sub_lt_iff {a b c : ennreal} (h : b < a) : a - b < c ↔ a < b + c :=
begin
  cases a; cases b,
  { exact false.elim (ne_of_lt h rfl) },
  { simp },
  { simp only [ennreal.none_eq_top, not_top_lt] at h,
    contradiction },
  cases c,
  { simp only [ennreal.none_eq_top, ennreal.coe_lt_top, iff_true, ennreal.some_eq_coe,
      ennreal.add_top],
    rw ←ennreal.coe_sub,
    exact ennreal.coe_lt_top },
  { simp at *,
    rw [←ennreal.coe_sub, ennreal.coe_lt_coe, nnreal.sub_lt_iff (le_of_lt h), ←ennreal.coe_add,
      ennreal.coe_lt_coe] }
end

#check sum_add_tsum_nat_add

set_option pp.proofs true

lemma exists_coe_of_sum_lt_top {α : Type u} {f : α → ennreal} (hf : (∑' i, f i) < ⊤) :
  ∃ g : α → nnreal, (∀ x, f x = g x) ∧ summable g :=
begin
  have : ∀ i, f i < ⊤,
  { contrapose! hf,
    rcases hf with ⟨x, hx⟩,
    rw top_le_iff at hx,
    convert @ennreal.le_tsum _ f x,
    exact hx.symm },
  let g : α → nnreal := λ x, classical.some (ennreal.lt_iff_exists_coe.1 (this x)),
  have hg : ∀ x, f x = g x := λ x, (classical.some_spec (ennreal.lt_iff_exists_coe.1 (this x))).1,
  refine ⟨g, ⟨hg, _⟩⟩,
  simp only [←ennreal.tsum_coe_ne_top_iff_summable, ←hg, ←ennreal.lt_top_iff_ne_top, hf]
end

lemma tendsto_sum_add (f : ℕ → ennreal) (hf : (∑' i, f i) < ⊤) :
  tendsto (λ i, ∑' k, f (i + k)) at_top (𝓝 0) :=
begin
  rcases exists_coe_of_sum_lt_top hf with ⟨g, ⟨hg : ∀ x, f x = g x, hg'⟩⟩,
  simp only [hg],
  have : ∀ i, summable (λ k, g (i + k)),
  { sorry, },

  simp only [←ennreal.coe_zero, λ i, ennreal.coe_tsum (this i)],



  /-by_cases h : ∀ i, f i = 0,
  { simp only [h, tsum_zero],
    exact tendsto_const_nhds },
  refine tendsto_order.2 ⟨λ a ha, false.elim (ennreal.not_lt_zero ha), λ a ha, _⟩,
  have := summable.has_sum (@ennreal.summable _ f),
  rw [ennreal.has_sum_iff_tendsto_nat, tendsto_order] at this,
  rcases this with ⟨this, -⟩,
  simp only [ge_iff_le, eventually_at_top] at ⊢ this,
  --rcases ennreal.lt_iff_exists_coe.1 hf with ⟨p, hp, -⟩,
  have tsum_sub_lt : (∑' i, f i) - a < ∑' i, f i,
  { apply ennreal.sub_lt_sub_self,
    { exact ne_of_lt hf },
    { push_neg at h,
      rcases h with ⟨n, hn⟩,
      rw ←zero_lt_iff_ne_zero,
      apply lt_of_lt_of_le (zero_lt_iff_ne_zero.2 hn),
      exact ennreal.le_tsum n },
    { exact ha } },
  rcases this _ tsum_sub_lt with ⟨n, hn⟩,
  refine ⟨n, λ m hm, _⟩,
  specialize hn m hm,
  rw sub_lt_iff at hn,-/


  /-by_cases h : a < ∑' i, f i,
  { --specialize this a h,
    obtain ⟨n, hn⟩ := this a h,
    refine ⟨n, λ m hm, _⟩,
    specialize hn m hm,

    --have := @sum_add_tsum_nat_add _ _ _ _ _ f m (@ennreal.summable f),
    --have := sum_add_tsum_nat_add,

   },-/
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
    (tendsto_measure_Inter (λ i, is_measurable.Union (λ b, hs (i + b))) _
      ⟨0, by { convert lt_of_le_of_lt (measure_Union_le s) hs', simp only [zero_add] }⟩)
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

#print axioms measure_limsup_eq_zero

end

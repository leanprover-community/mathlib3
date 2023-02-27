/-
Copyright (c) 2023 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Yury G. Kudryashov, Heather Macbeth
-/
import measure_theory.function.strongly_measurable.ae_sequence

/-!
# Supreme and infinite sums of (ae-)strongly measurable functions

We prove lemmas for suprema and infima of `strongly_measurable` and `ae_strongly_measurable`
functions, as well as, lemmas for their `tsum`s into `ennreal` and `nnreal`.

-/

open measure_theory filter topological_space function set measure_theory.measure
open_locale ennreal topological_space measure_theory nnreal big_operators

variables {α β ι' : Type*} {ι : Sort*} [measurable_space α] [topological_space β]

section strongly_measurable

open measure_theory set filter topological_space
open_locale filter topological_space

lemma finset.strongly_measurable_sup'
  [semilattice_sup β] [has_continuous_sup β] {f : ι' → α → β} {s : finset ι'} (hs : s.nonempty)
  (hf : ∀ i ∈ s, strongly_measurable (f i)) : strongly_measurable (s.sup' hs f) :=
finset.sup'_induction _ _ (λ _ h₁ _ h₂, h₁.sup h₂) hf

lemma finset.strongly_measurable_sup'_pw
  [semilattice_sup β] [has_continuous_sup β] {f : ι' → α → β} {s : finset ι'} (hs : s.nonempty)
  (hf : ∀ i ∈ s, strongly_measurable (f i)) : strongly_measurable (λ x, s.sup' hs (λ i, f i x)) :=
by simpa only [← finset.sup'_apply] using finset.strongly_measurable_sup' hs hf

lemma strongly_measurable.is_lub [countable ι] [semilattice_sup β] [metrizable_space β]
  [Sup_convergence_class β] [has_continuous_sup β] {f : ι → α → β} {g : α → β}
  (hf : ∀ i, strongly_measurable (f i)) (hg : ∀ x, is_lub (range $ λ i, f i x) (g x)) :
  strongly_measurable g :=
begin
  casesI is_empty_or_nonempty ι,
  { simp only [range_eq_empty, is_lub_empty_iff] at hg,
    exact strongly_measurable_const' (λ x y, (hg x _).antisymm (hg y _)) },
  replace hg : ∀ (x : α), is_lub (range ((λ (i : ι), f i x) ∘ @plift.down ι)) (g x),
  { intro x,
    dunfold set.range at ⊢ hg,
    simp_rw plift.exists,
    exact hg x, },
  have := λ x, tendsto_finset_sup'_is_lub (hg x),
  letI := classical.dec_eq ι,
  refine strongly_measurable_of_tendsto _ (λ s, _) (tendsto_pi_nhds.2 this),
  exact finset.strongly_measurable_sup'_pw _ (λ i _, hf _),
end

lemma strongly_measurable.is_glb [countable ι] [semilattice_inf β] [metrizable_space β]
  [Inf_convergence_class β] [has_continuous_inf β] {f : ι → α → β} {g : α → β}
  (hf : ∀ i, strongly_measurable (f i)) (hg : ∀ x, is_glb (range $ λ i, f i x) (g x)) :
  strongly_measurable g := @strongly_measurable.is_lub α (order_dual β) ι _ _ _ _ _ _ _ f g hf hg

lemma strongly_measurable_supr [complete_linear_order β]
  [order_topology β] [metrizable_space β]
  [countable ι] {f : ι → α → β} (hf : ∀ i, strongly_measurable (f i)) :
  strongly_measurable (λ b, ⨆ i, f i b) :=
strongly_measurable.is_lub hf $ λ b, is_lub_supr

lemma strongly_measurable_infi [complete_linear_order β]
  [order_topology β] [metrizable_space β]
  [countable ι] {f : ι → α → β} (hf : ∀ i, strongly_measurable (f i)) :
  strongly_measurable (λ b, ⨅ i, f i b) :=
strongly_measurable.is_glb hf $ λ b, is_glb_infi

theorem strongly_measurable.ennreal_tsum [countable ι'] {f : ι' → α → ℝ≥0∞}
  (h : ∀ (i : ι'), strongly_measurable (f i)) :
strongly_measurable (λ (x : α), ∑' (i : ι'), f i x):=
by { simp_rw [ennreal.tsum_eq_supr_sum], apply strongly_measurable_supr,
  exact λ s, s.strongly_measurable_sum (λ i _, h i) }

lemma strongly_measurable.ennreal_tsum' [countable ι'] {f : ι' → α → ℝ≥0∞}
  (h : ∀ i, strongly_measurable (f i)) :
  strongly_measurable (∑' i, f i) :=
begin
  convert strongly_measurable.ennreal_tsum h,
  ext1 x,
  exact tsum_apply (pi.summable.2 (λ _, ennreal.summable)),
end

lemma strongly_measurable.nnreal_tsum [countable ι'] {f : ι' → α → ℝ≥0}
  (h : ∀ i, strongly_measurable (f i)) :
  strongly_measurable (λ x, ∑' i, f i x) :=
begin
  simp_rw [nnreal.tsum_eq_to_nnreal_tsum],
  exact (strongly_measurable.ennreal_tsum (λ i, (h i).coe_nnreal_ennreal)).ennreal_to_nnreal,
end


end strongly_measurable

section ae_strongly_measureable

open measure_theory

open_locale classical

private lemma ae_strongly_measurable.is_lub_of_nonempty {α : Type*} {δ : Type*}
  [topological_space α] [measurable_space α] [borel_space α] [measurable_space δ] [linear_order α]
  [order_topology α] [metrizable_space α]
  [topological_space.second_countable_topology α] {ι : Sort*} {μ : measure_theory.measure δ}
  [countable ι] (hι : nonempty ι) {f : ι → δ → α} {g : δ → α}
  (hf : ∀ (i : ι), ae_strongly_measurable (f i) μ)
  (hg : ∀ᵐ (b : δ) ∂μ, is_lub {a : α | ∃ (i : ι), f i b = a} (g b)) :
  ae_strongly_measurable g μ :=
begin
  let p : δ → (ι → α) → Prop := λ x f', is_lub {a | ∃ i, f' i = a} (g x),
  let g_seq := λ x, ite (x ∈ ae_strongly_seq_set hf p) (g x) (⟨g x⟩ : nonempty α).some,
  have hg_seq : ∀ b, is_lub {a | ∃ i, ae_strongly_seq hf p i b = a} (g_seq b),
  { intro b,
    haveI hα : nonempty α := nonempty.map g ⟨b⟩,
    simp only [ae_strongly_seq, g_seq],
    split_ifs,
    { have h_set_eq : {a : α | ∃ (i : ι), (hf i).mk (f i) b = a} = {a : α | ∃ (i : ι), f i b = a},
      { ext x,
        simp_rw [set.mem_set_of_eq, ae_strongly_seq.mk_eq_fun_of_mem_ae_strongly_seq_set hf h], },
      rw h_set_eq,
      exact ae_strongly_seq.fun_prop_of_mem_ae_strongly_seq_set hf h, },
    { have h_singleton : {a : α | ∃ (i : ι), hα.some = a} = {hα.some},
      { ext1 x,
        exact ⟨λ hx, hx.some_spec.symm, λ hx, ⟨hι.some, hx.symm⟩⟩, },
      rw h_singleton,
      exact is_lub_singleton, }, },
  refine ⟨g_seq, strongly_measurable.is_lub (ae_strongly_seq.strongly_measurable hf p) hg_seq, _⟩,
  exact (ite_ae_eq_of_measure_compl_zero g (λ x, (⟨g x⟩ : nonempty α).some)
    (ae_strongly_seq_set hf p)
    (ae_strongly_seq.measure_compl_ae_strongly_seq_set_eq_zero hf hg)).symm,
end

theorem ae_strongly_measurable.is_lub {α : Type*} {δ : Type*} [topological_space α]
  [measurable_space α] [borel_space α] [measurable_space δ] [linear_order α] [order_topology α]
  [topological_space.second_countable_topology α]  [metrizable_space α] {ι : Type*}
  {μ : measure_theory.measure δ}
  [countable ι] {f : ι → δ → α} {g : δ → α} (hf : ∀ (i : ι), ae_strongly_measurable (f i) μ)
  (hg : ∀ᵐ (b : δ) ∂μ, is_lub {a : α | ∃ (i : ι), f i b = a} (g b)) :
  ae_strongly_measurable g μ :=
begin
  by_cases hμ : μ = 0, { rw hμ, apply ae_strongly_measurable_zero_measure },
  haveI : μ.ae.ne_bot, { simpa [ne_bot_iff] },
  by_cases hι : nonempty ι, { exact ae_strongly_measurable.is_lub_of_nonempty hι hf hg, },
  suffices : ∃ x, g =ᵐ[μ] λ y, g x,
  by { exact ⟨(λ y, g this.some), strongly_measurable_const, this.some_spec⟩, },
  have h_empty : ∀ x, {a : α | ∃ (i : ι), f i x = a} = ∅,
  { intro x,
    ext1 y,
    rw [set.mem_set_of_eq, set.mem_empty_iff_false, iff_false],
    exact λ hi, hι (nonempty_of_exists hi), },
  simp_rw h_empty at hg,
  exact ⟨hg.exists.some, hg.mono (λ y hy, is_lub.unique hy hg.exists.some_spec)⟩,
end

theorem ae_strongly_measurable.is_glb {α : Type*} {δ : Type*} [topological_space α]
  [measurable_space α] [borel_space α] [measurable_space δ] [linear_order α] [order_topology α]
  [topological_space.second_countable_topology α]  [metrizable_space α] {ι : Type*}
  {μ : measure_theory.measure δ}
  [countable ι] {f : ι → δ → α} {g : δ → α} (hf : ∀ (i : ι), ae_strongly_measurable (f i) μ)
  (hg : ∀ᵐ (b : δ) ∂μ, is_glb {a : α | ∃ (i : ι), f i b = a} (g b)) :
  ae_strongly_measurable g μ :=
@ae_strongly_measurable.is_lub (order_dual α) δ _ _ _ _ _ _ _ _ ι μ _ f g hf hg

theorem ae_strongly_measurable_supr [measurable_space β] [borel_space β] [complete_linear_order β]
  [order_topology β] [topological_space.second_countable_topology β] [metrizable_space β]
  {ι : Type*} {μ : measure α} [countable ι] {f : ι → α → β}
  (hf : ∀ (i : ι), ae_strongly_measurable (f i) μ) :
  ae_strongly_measurable (λ (b : α), ⨆ (i : ι), f i b) μ :=
ae_strongly_measurable.is_lub hf  (ae_of_all μ (λ b, is_lub_supr))


theorem ae_strongly_measurable_infi [measurable_space β] [borel_space β] [complete_linear_order β]
  [order_topology β] [topological_space.second_countable_topology β] [metrizable_space β]
  {ι : Type*} {μ : measure α} [countable ι] {f : ι → α → β}
  (hf : ∀ (i : ι), ae_strongly_measurable (f i) μ) :
  ae_strongly_measurable (λ (b : α), ⨅ (i : ι), f i b) μ :=
ae_strongly_measurable.is_glb hf  (ae_of_all μ (λ b, is_glb_infi))

theorem ae_strongly_measurable.ennreal_tsum {α : Type*} [measurable_space α] {ι : Type*}
  [countable ι] {f : ι → α → ennreal} {μ : measure_theory.measure α}
  (h : ∀ (i : ι), ae_strongly_measurable (f i) μ) :
  ae_strongly_measurable (λ (x : α), ∑' (i : ι), f i x) μ :=
begin
  simp_rw [ennreal.tsum_eq_supr_sum],
  apply ae_strongly_measurable_supr,
  exact λ s, finset.ae_strongly_measurable_sum s (λ i _, h i),
end

theorem ae_strongly_measurable.nnreal_tsum {α : Type*} [measurable_space α] {ι : Type*}
  [countable ι] {f : ι → α → nnreal} {μ : measure_theory.measure α}
  (h : ∀ (i : ι), ae_strongly_measurable (f i) μ) :
  ae_strongly_measurable (λ (x : α), ∑' (i : ι), f i x) μ :=
begin
  simp_rw [nnreal.tsum_eq_to_nnreal_tsum],
  exact (ae_strongly_measurable.ennreal_tsum (λ i, (h i).coe_nnreal_ennreal)).ennreal_to_nnreal,
end

end ae_strongly_measureable

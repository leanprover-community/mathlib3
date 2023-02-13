/-
Copyright (c) 2023 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/

import measure_theory.function.strongly_measurable.basic

/-!
# Sequence of strongly measurable functions associated to a sequence of a.e.-strongly-measurable
  functions

We define here tools to prove statements about limits (infi, supr...) of sequences of
`ae_strongly_measurable` functions.
Given a sequence of a.e.-strongly-measurable functions `f : ι → α → β` with hypothesis
`hf : ∀ i, ae_strongly_measurable (f i) μ`, and a pointwise property `p : α → (ι → β) → Prop` such
that we have `hp : ∀ᵐ x ∂μ, p x (λ n, f n x)`, we define a sequence of strongly measurable functions
`ae_strongly_seq hf p` and a measurable set `ae_strongly_seq_set hf p`, such that
* `μ (ae_strongly_seq_set hf p)ᶜ = 0`
* `x ∈ ae_strongly_seq_set hf p → ∀ i : ι, ae_strongly_seq hf hp i x = f i x`
* `x ∈ ae_strongly_seq_set hf p → p x (λ n, f n x)`
-/

open measure_theory filter topological_space function set measure_theory.measure
open_locale ennreal topological_space measure_theory nnreal big_operators

open measure_theory
open_locale classical

variables {α β : Type*} {ι : Sort*}  [measurable_space α]
  [topological_space β] {f : ι → α → β} {μ : measure α} {p : α → (ι → β) → Prop}

/-- If we have the additional hypothesis `∀ᵐ x ∂μ, p x (λ n, f n x)`, this is a measurable set
whose complement has measure 0 such that for all `x ∈ ae_strongly_seq_set`, `f i x` is equal to
`(hf i).mk (f i) x` for all `i` and we have the pointwise property `p x (λ n, f n x)`. -/
def ae_strongly_seq_set (hf : ∀ i, ae_strongly_measurable (f i) μ) (p : α → (ι → β) → Prop) :
  set α :=
(to_measurable μ {x | (∀ i, f i x = (hf i).mk (f i) x) ∧ p x (λ n, f n x)}ᶜ)ᶜ

/-- A sequence of measurable functions that are equal to `f` and verify property `p` on the
measurable set `ae_strongly_seq_set hf p`. -/
noncomputable
def ae_strongly_seq (hf : ∀ i, ae_strongly_measurable (f i) μ) (p : α → (ι → β) → Prop) :
  ι → α → β :=
λ i x, if (x ∈ ae_strongly_seq_set hf p) then ((hf i).mk (f i) x) else (⟨f i x⟩ : nonempty β).some

namespace ae_strongly_seq

lemma mk_eq_fun_of_mem_ae_strongly_seq_set
  (hf : ∀ i, ae_strongly_measurable (f i) μ) {x : α}
  (hx : x ∈ ae_strongly_seq_set hf p) (i : ι) :
  (hf i).mk (f i) x = f i x :=
begin
  have h_ss : ae_strongly_seq_set hf p ⊆ {x | ∀ i, f i x = (hf i).mk (f i) x},
  { rw [ae_strongly_seq_set, ←compl_compl {x | ∀ i, f i x = (hf i).mk (f i) x},
      set.compl_subset_compl],
    refine set.subset.trans (set.compl_subset_compl.mpr (λ x h, _)) (subset_to_measurable _ _),
    exact h.1, },
  exact (h_ss hx i).symm,
end

lemma ae_strongly_seq_eq_mk_of_mem_ae_strongly_seq_set (hf : ∀ i, ae_strongly_measurable (f i) μ)
  {x : α} (hx : x ∈ ae_strongly_seq_set hf p) (i : ι) :
  ae_strongly_seq hf p i x = (hf i).mk (f i) x :=
by simp only [ae_strongly_seq, hx, if_true]

lemma ae_strongly_seq_eq_fun_of_mem_ae_strongly_seq_set (hf : ∀ i, ae_strongly_measurable (f i) μ)
  {x : α} (hx : x ∈ ae_strongly_seq_set hf p) (i : ι) :
  ae_strongly_seq hf p i x = f i x :=
by simp only [ae_strongly_seq_eq_mk_of_mem_ae_strongly_seq_set hf hx i,
  mk_eq_fun_of_mem_ae_strongly_seq_set hf hx i]

lemma prop_of_mem_ae_strongly_seq_set (hf : ∀ i, ae_strongly_measurable (f i) μ)
  {x : α} (hx : x ∈ ae_strongly_seq_set hf p) :
  p x (λ n, ae_strongly_seq hf p n x) :=
begin
  simp only [ae_strongly_seq, hx, if_true],
  rw funext (λ n, mk_eq_fun_of_mem_ae_strongly_seq_set hf hx n),
  have h_ss : ae_strongly_seq_set hf p ⊆ {x | p x (λ n, f n x)},
  { rw [←compl_compl {x | p x (λ n, f n x)}, ae_strongly_seq_set, set.compl_subset_compl],
    refine set.subset.trans (set.compl_subset_compl.mpr _) (subset_to_measurable _ _),
    exact λ x hx, hx.2, },
  have hx' := set.mem_of_subset_of_mem h_ss hx,
  exact hx',
end

lemma fun_prop_of_mem_ae_strongly_seq_set (hf : ∀ i, ae_strongly_measurable (f i) μ)
  {x : α} (hx : x ∈ ae_strongly_seq_set hf p) :
  p x (λ n, f n x) :=
begin
  have h_eq : (λ n, f n x) = λ n, ae_strongly_seq hf p n x,
    from funext (λ n, (ae_strongly_seq_eq_fun_of_mem_ae_strongly_seq_set hf hx n).symm),
  rw h_eq,
  exact prop_of_mem_ae_strongly_seq_set hf hx,
end

lemma ae_strongly_seq_set_measurable_set {hf : ∀ i, ae_strongly_measurable (f i) μ} :
  measurable_set (ae_strongly_seq_set hf p) :=
(measurable_set_to_measurable _ _).compl

lemma strongly_measurable (hf : ∀ i, ae_strongly_measurable (f i) μ) (p : α → (ι → β) → Prop)
  (i : ι) :
  strongly_measurable (ae_strongly_seq hf p i) :=
  strongly_measurable.ite ae_strongly_seq_set_measurable_set
  (hf i).strongly_measurable_mk $ strongly_measurable_const' $
  λ x y, rfl

lemma measure_compl_ae_strongly_seq_set_eq_zero [countable ι]
  (hf : ∀ i, ae_strongly_measurable (f i) μ)
  (hp : ∀ᵐ x ∂μ, p x (λ n, f n x)) :
  μ (ae_strongly_seq_set hf p)ᶜ = 0 :=
begin
  rw [ae_strongly_seq_set, compl_compl, measure_to_measurable],
  have hf_eq := λ i, (hf i).ae_eq_mk,
  simp_rw [filter.eventually_eq, ←ae_all_iff] at hf_eq,
  exact filter.eventually.and hf_eq hp,
end

end ae_strongly_seq

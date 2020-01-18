/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/

import measure_theory.bochner_integration
import measure_theory.indicator_function
import measure_theory.lebesgue_measure

/-!
# Set integral

Integrate a function over a subset of a measure space.

## Main definition

`measurable_on`, `integrable_on`, `integral_on`

## Tags

indicator, characteristic
-/

noncomputable theory
open_locale classical topological_space
open set lattice filter topological_space ennreal emetric measure_theory

set_option class.instance_max_depth 50

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

section measurable_on
variables [measurable_space α] [measurable_space β] [has_zero β] {s : set α} {f : α → β}

/-- `measurable_on s f` means `f` is measurable over the set `s`. -/
@[reducible]
def measurable_on (s : set α) (f : α → β) : Prop := measurable (indicator s f)

lemma measurable_on_empty : measurable_on ∅ f :=
by { rw [measurable_on, indicator_empty], exact measurable_const }

lemma measurable_on_univ (hf : measurable f) : measurable_on univ f :=
hf.if is_measurable.univ measurable_const

lemma measurable.measurable_on (hs : is_measurable s) (hf : measurable f) : measurable_on s f :=
hf.if hs measurable_const

lemma is_measurable.inter_preimage {B : set β}
  (hs : is_measurable s) (hB : is_measurable B) (hf : measurable_on s f):
  is_measurable (s ∩ f ⁻¹' B) :=
begin
  replace hf : is_measurable ((indicator s f)⁻¹' B) := hf B hB,
  rw indicator_preimage at hf,
  replace hf := hf.diff _,
  rwa union_diff_cancel_right at hf,
  { assume a, simp {contextual := tt} },
  exact hs.compl.inter (measurable_const.preimage hB)
end

lemma measurable_on.subset {t : set α} (hs : is_measurable s) (h : s ⊆ t) (hf : measurable_on t f) :
  measurable_on s f :=
begin
  have : measurable_on s (indicator t f) := measurable.measurable_on hs hf,
  simp only [measurable_on, indicator_indicator] at this,
  rwa [inter_eq_self_of_subset_left h] at this,
end

lemma measurable_on.union {t : set α} {f : α → β}
  (hs : is_measurable s) (ht : is_measurable t) (hsm : measurable_on s f) (htm : measurable_on t f) :
  measurable_on (s ∪ t) f :=
begin
  assume B hB,
  show is_measurable ((indicator (s ∪ t) f)⁻¹' B),
  rw indicator_preimage,
  refine is_measurable.union _ ((hs.union ht).compl.inter (measurable_const.preimage hB)),
  simp only [union_inter_distrib_right],
  exact (hs.inter_preimage hB hsm).union (ht.inter_preimage hB htm)
end

lemma measurable_on_singleton {α} [topological_space α] [t1_space α] {a : α} {f : α → β} :
  measurable_on {a} f :=
λ s hs, show is_measurable ((indicator _ _)⁻¹' s),
begin
  rw indicator_preimage,
  refine is_measurable.union _ (is_measurable_singleton.compl.inter $ measurable_const.preimage hs),
  by_cases h : a ∈ f⁻¹' s,
  { rw inter_eq_self_of_subset_left,
    { exact is_measurable_singleton },
    rwa singleton_subset_iff },
  rw [singleton_inter_eq_empty.2 h],
  exact is_measurable.empty
end

end measurable_on

section integrable_on
variables [measure_space α] [normed_group β] {s t : set α} {f g : α → β}

/-- `integrable_on s f` means `f` is integrable over the set `s`. -/
@[reducible]
def integrable_on (s : set α) (f : α → β) : Prop := integrable (indicator s f)

lemma integrable_on_congr (h : ∀x, x ∈ s → f x = g x) : integrable_on s f ↔ integrable_on s g :=
by simp only [integrable_on, indicator_congr h]

lemma integrable_on_congr_ae (h : ∀ₘx, x ∈ s → f x = g x) :
  integrable_on s f ↔ integrable_on s g :=
by { apply integrable_congr_ae, exact indicator_congr_ae h }

lemma integrable_on_empty : integrable_on ∅ f :=
by { simp only [integrable_on, indicator_empty], exact integrable_zero }

lemma integrable_on_of_integrable (s : set α) (hf : integrable f) : integrable_on s f :=
by { refine integrable_of_le (λa, _) hf, apply norm_indicator_le_norm_self }

lemma integrable_on.subset (h : s ⊆ t) : integrable_on t f → integrable_on s f :=
by { apply integrable_of_le_ae, filter_upwards [] norm_indicator_le_of_subset h _ }

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma integrable_on.smul (s : set α) (c : 𝕜) {f : α → β} : integrable_on s f → integrable_on s (λa, c • f a) :=
by { simp only [integrable_on, indicator_smul], apply integrable.smul }

lemma integrable_on.mul_left (s : set α) (r : ℝ) {f : α → ℝ} (hf : integrable_on s f) :
  integrable_on s (λa, r * f a) :=
by { simp only [smul_eq_mul.symm], exact hf.smul s r }

lemma integrable_on.mul_right (s : set α) (r : ℝ) {f : α → ℝ} (hf : integrable_on s f) :
  integrable_on s (λa, f a * r) :=
by { simp only [mul_comm], exact hf.mul_left _ _ }

lemma integrable_on.divide (s : set α) (r : ℝ) {f : α → ℝ} (hf : integrable_on s f) :
  integrable_on s (λa, f a / r) :=
by { simp only [div_eq_mul_inv], exact hf.mul_right _ _ }

lemma integrable_on.add (hfm : measurable_on s f) (hfi : integrable_on s f) (hgm : measurable_on s g)
  (hgi : integrable_on s g) : integrable_on s (λa, f a + g a) :=
by { rw [integrable_on, indicator_add], exact hfi.add hfm hgm hgi }

lemma integrable_on.neg (hf : integrable_on s f) : integrable_on s (λa, -f a) :=
by { rw [integrable_on, indicator_neg], exact hf.neg }

lemma integrable_on.sub (hfm : measurable_on s f) (hfi : integrable_on s f) (hgm : measurable_on s g)
  (hgi : integrable_on s g) : integrable_on s (λa, f a - g a) :=
by { rw [integrable_on, indicator_sub], exact hfi.sub hfm hgm hgi }

lemma integrable_on.union (hs : is_measurable s) (ht : is_measurable t) (hsm : measurable_on s f)
  (hsi : integrable_on s f) (htm : measurable_on t f) (hti : integrable_on t f) :
  integrable_on (s ∪ t) f :=
begin
  rw ← union_diff_self,
  rw [integrable_on, indicator_union_of_disjoint],
  { refine integrable.add hsm hsi (htm.subset _ _) (hti.subset _),
    { exact ht.diff hs },
    { exact diff_subset _ _ },
    { exact diff_subset _ _ } },
  exact disjoint_diff
end

lemma integrable_on_norm_iff (s : set α) (f : α → β) :
  integrable_on s (λa, ∥f a∥) ↔ integrable_on s f :=
begin
  simp only [integrable_on],
  convert integrable_norm_iff (indicator s f),
  funext,
  rw norm_indicator_eq_indicator_norm,
end

end integrable_on

section integral_on
variables [measure_space α]
  [normed_group β] [second_countable_topology β] [normed_space ℝ β] [complete_space β]
  {s t : set α} {f g : α → β}
  {a b : ℝ} {h : ℝ → β}

notation `∫` binders ` in ` s `, ` r:(scoped f, integral (indicator s f)) := r

variables (β)
@[simp] lemma integral_on_zero (s : set α) : (∫ a in s, (0:β)) = 0 :=
by rw [indicator_zero, integral_zero]
variables {β}

lemma integral_on_congr (h : ∀ x ∈ s, f x = g x) : (∫ a in s, f a) = (∫ a in s, g a) :=
by simp only [indicator_congr h]

lemma integral_on_congr_of_ae_eq (hf : measurable_on s f) (hg : measurable_on s g)
  (h : ∀ₘ x, x ∈ s → f x = g x) : (∫ a in s, f a) = (∫ a in s, g a) :=
integral_congr_ae hf hg (indicator_congr_ae h)

lemma integral_on_congr_of_set (hsm : measurable_on s f) (htm : measurable_on t f)
  (h : ∀ₘ x, x ∈ s ↔ x ∈ t) : (∫ a in s, f a) = (∫ a in t, f a) :=
integral_congr_ae hsm htm $ indicator_congr_of_set h

variables (s t)

lemma integral_on_smul (r : ℝ) (f : α → β) : (∫ a in s, r • (f a)) = r • (∫ a in s, f a) :=
by rw [← integral_smul, indicator_smul]

lemma integral_on_mul_left (r : ℝ) (f : α → ℝ) : (∫ a in s, r * (f a)) = r * (∫ a in s, f a) :=
integral_on_smul s r f

lemma integral_on_mul_right (r : ℝ) (f : α → ℝ) : (∫ a in s, (f a) * r) = (∫ a in s, f a) * r :=
by { simp only [mul_comm], exact integral_on_mul_left s r f }

lemma integral_on_div (r : ℝ) (f : α → ℝ) : (∫ a in s, (f a) / r) = (∫ a in s, f a) / r :=
by { simp only [div_eq_mul_inv], apply integral_on_mul_right }

lemma integral_on_neg (f : α → β) : (∫ a in s, -f a) = - (∫ a in s, f a) :=
by { simp only [indicator_neg], exact integral_neg _ }

variables {s t}

lemma integral_on_add {s : set α} (hfm : measurable_on s f) (hfi : integrable_on s f) (hgm : measurable_on s g)
  (hgi : integrable_on s g) : (∫ a in s, f a + g a) = (∫ a in s, f a) + (∫ a in s, g a) :=
by { simp only [indicator_add], exact integral_add hfm hfi hgm hgi }

lemma integral_on_sub (hfm : measurable_on s f) (hfi : integrable_on s f) (hgm : measurable_on s g)
  (hgi : integrable_on s g) : (∫ a in s, f a - g a) = (∫ a in s, f a) - (∫ a in s, g a) :=
by { simp only [indicator_sub], exact integral_sub hfm hfi hgm hgi }

lemma integral_on_le_integral_on_ae {f g : α → ℝ} (hfm : measurable_on s f) (hfi : integrable_on s f)
  (hgm : measurable_on s g) (hgi : integrable_on s g) (h : ∀ₘ a, a ∈ s → f a ≤ g a) :
  (∫ a in s, f a) ≤ (∫ a in s, g a) :=
begin
  apply integral_le_integral_ae hfm hfi hgm hgi,
  apply indicator_le_indicator_ae,
  exact h
end

lemma integral_on_le_integral_on {f g : α → ℝ} (hfm : measurable_on s f) (hfi : integrable_on s f)
  (hgm : measurable_on s g) (hgi : integrable_on s g) (h : ∀ a, a ∈ s → f a ≤ g a) :
  (∫ a in s, f a) ≤ (∫ a in s, g a) :=
integral_on_le_integral_on_ae hfm hfi hgm hgi $ by filter_upwards [] h

lemma integral_on_union (hsm : measurable_on s f) (hsi : integrable_on s f)
  (htm : measurable_on t f) (hti : integrable_on t f) (h : disjoint s t) :
  (∫ a in (s ∪ t), f a) = (∫ a in s, f a) + (∫ a in t, f a) :=
by { rw [indicator_union_of_disjoint h, integral_add hsm hsi htm hti] }

lemma integral_on_union_ae (hs : is_measurable s) (ht : is_measurable t) (hsm : measurable_on s f)
  (hsi : integrable_on s f) (htm : measurable_on t f) (hti : integrable_on t f) (h : ∀ₘ a, a ∉ s ∩ t) :
  (∫ a in (s ∪ t), f a) = (∫ a in s, f a) + (∫ a in t, f a) :=
begin
  have := integral_congr_ae _ _ (indicator_union_ae h f),
  rw [this, integral_add hsm hsi htm hti],
  { exact hsm.union hs ht htm },
  { exact hsm.add htm }
end

lemma tendsto_integral_on_of_monotone {s : ℕ → set α} {f : α → β} (hsm : ∀i, is_measurable (s i))
  (h_mono : monotone s) (hfm : measurable_on (Union s) f) (hfi : integrable_on (Union s) f) :
  tendsto (λi, ∫ a in (s i), f a) at_top (nhds (∫ a in (Union s), f a)) :=
let bound : α → ℝ := indicator (Union s) (λa, ∥f a∥) in
begin
  apply tendsto_integral_of_dominated_convergence,
  { assume i, exact hfm.subset (hsm i) (subset_Union _ _) },
  { assumption },
  { show integrable_on (Union s) (λa, ∥f a∥), rwa integrable_on_norm_iff },
  { assume i, apply all_ae_of_all,
    assume a,
    rw [norm_indicator_eq_indicator_norm],
    exact indicator_le_indicator_of_subset (subset_Union _ _) (λa, norm_nonneg _) _ },
  { filter_upwards [] λa, le_trans (tendsto_indicator_of_monotone _ h_mono _ _) (pure_le_nhds _) }
end

lemma tendsto_integral_on_of_antimono (s : ℕ → set α) (f : α → β) (hsm : ∀i, is_measurable (s i))
  (h_mono : ∀i j, i ≤ j → s j ⊆ s i) (hfm : measurable_on (s 0) f) (hfi : integrable_on (s 0) f) :
  tendsto (λi, ∫ a in (s i), f a) at_top (nhds (∫ a in (Inter s), f a)) :=
let bound : α → ℝ := indicator (s 0) (λa, ∥f a∥) in
begin
  apply tendsto_integral_of_dominated_convergence,
  { assume i, refine hfm.subset (hsm i) (h_mono _ _ (zero_le _)) },
  { exact hfm.subset (is_measurable.Inter hsm) (Inter_subset _ _) },
  { show integrable_on (s 0) (λa, ∥f a∥), rwa integrable_on_norm_iff },
  { assume i, apply all_ae_of_all,
    assume a,
    rw [norm_indicator_eq_indicator_norm],
    refine indicator_le_indicator_of_subset (h_mono _ _ (zero_le _)) (λa, norm_nonneg _) _ },
  { filter_upwards [] λa, le_trans (tendsto_indicator_of_antimono _ h_mono _ _) (pure_le_nhds _) }
end

-- TODO : prove the following proposition

-- lemma integral_on_Union (s : ℕ → set α) (f : α → β) (hm : ∀i, is_measurable (s i))
--   (hd : pairwise (disjoint on s)) (hf : integrable_on (Union s) f) :
--   integral_on (Union s) f = ∑i, integral_on (s i) f := sorry

end integral_on

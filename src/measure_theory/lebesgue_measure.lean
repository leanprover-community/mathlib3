/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import measure_theory.measure_space
import measure_theory.borel_space

/-!
# Lebesgue measure on the real line
-/

noncomputable theory
open classical set filter
open ennreal (of_real)
open_locale big_operators

namespace measure_theory

/-- Length of an interval. This is the largest monotonic function which correctly
  measures all intervals. -/
def lebesgue_length (s : set ℝ) : ennreal := ⨅a b (h : s ⊆ Ico a b), of_real (b - a)

@[simp] lemma lebesgue_length_empty : lebesgue_length ∅ = 0 :=
le_zero_iff_eq.1 $ infi_le_of_le 0 $ infi_le_of_le 0 $ by simp

@[simp] lemma lebesgue_length_Ico (a b : ℝ) :
  lebesgue_length (Ico a b) = of_real (b - a) :=
begin
  refine le_antisymm (infi_le_of_le a $ binfi_le b (subset.refl _))
    (le_infi $ λ a', le_infi $ λ b', le_infi $ λ h, ennreal.coe_le_coe.2 _),
  cases le_or_lt b a with ab ab,
  { rw nnreal.of_real_of_nonpos (sub_nonpos.2 ab), apply zero_le },
  cases (Ico_subset_Ico_iff ab).1 h with h₁ h₂,
  exact nnreal.of_real_le_of_real (sub_le_sub h₂ h₁)
end

lemma lebesgue_length_mono {s₁ s₂ : set ℝ} (h : s₁ ⊆ s₂) :
  lebesgue_length s₁ ≤ lebesgue_length s₂ :=
infi_le_infi $ λ a, infi_le_infi $ λ b, infi_le_infi2 $ λ h', ⟨subset.trans h h', le_refl _⟩

lemma lebesgue_length_eq_infi_Ioo (s) :
  lebesgue_length s = ⨅a b (h : s ⊆ Ioo a b), of_real (b - a) :=
begin
  refine le_antisymm
    (infi_le_infi $ λ a, infi_le_infi $ λ b, infi_le_infi2 $ λ h,
      ⟨subset.trans h Ioo_subset_Ico_self, le_refl _⟩) _,
  refine le_infi (λ a, le_infi $ λ b, le_infi $ λ h, _),
  refine ennreal.le_of_forall_epsilon_le (λ ε ε0 _, _),
  refine infi_le_of_le (a - ε) (infi_le_of_le b $ infi_le_of_le
    (subset.trans h $ Ico_subset_Ioo_left $ (sub_lt_self_iff _).2 ε0) _),
  rw ← sub_add,
  refine le_trans ennreal.of_real_add_le (add_le_add_left _ _),
  simp only [ennreal.of_real_coe_nnreal, le_refl]
end

@[simp] lemma lebesgue_length_Ioo (a b : ℝ) :
  lebesgue_length (Ioo a b) = of_real (b - a) :=
begin
  rw ← lebesgue_length_Ico,
  refine le_antisymm (lebesgue_length_mono Ioo_subset_Ico_self) _,
  rw lebesgue_length_eq_infi_Ioo (Ioo a b),
  refine (le_infi $ λ a', le_infi $ λ b', le_infi $ λ h, _),
  cases le_or_lt b a with ab ab, {simp [ab]},
  cases (Ioo_subset_Ioo_iff ab).1 h with h₁ h₂,
  rw [lebesgue_length_Ico],
  exact ennreal.of_real_le_of_real (sub_le_sub h₂ h₁)
end

lemma lebesgue_length_eq_infi_Icc (s) :
  lebesgue_length s = ⨅a b (h : s ⊆ Icc a b), of_real (b - a) :=
begin
  refine le_antisymm _
    (infi_le_infi $ λ a, infi_le_infi $ λ b, infi_le_infi2 $ λ h,
      ⟨subset.trans h Ico_subset_Icc_self, le_refl _⟩),
  refine le_infi (λ a, le_infi $ λ b, le_infi $ λ h, _),
  refine ennreal.le_of_forall_epsilon_le (λ ε ε0 _, _),
  refine infi_le_of_le a (infi_le_of_le (b + ε) $ infi_le_of_le
    (subset.trans h $ Icc_subset_Ico_right $ (lt_add_iff_pos_right _).2 ε0) _),
  rw [← sub_add_eq_add_sub],
  refine le_trans ennreal.of_real_add_le (add_le_add_left _ _),
  simp only [ennreal.of_real_coe_nnreal, le_refl]
end

@[simp] lemma lebesgue_length_Icc (a b : ℝ) :
  lebesgue_length (Icc a b) = of_real (b - a) :=
begin
  rw ← lebesgue_length_Ico,
  refine le_antisymm _ (lebesgue_length_mono Ico_subset_Icc_self),
  rw lebesgue_length_eq_infi_Icc (Icc a b),
  exact infi_le_of_le a (infi_le_of_le b $ infi_le_of_le (by refl) (by simp [le_refl]))
end

/-- The Lebesgue outer measure, as an outer measure of ℝ. -/
def lebesgue_outer : outer_measure ℝ :=
outer_measure.of_function lebesgue_length lebesgue_length_empty

lemma lebesgue_outer_le_length (s : set ℝ) : lebesgue_outer s ≤ lebesgue_length s :=
outer_measure.of_function_le _

lemma lebesgue_length_subadditive {a b : ℝ} {c d : ℕ → ℝ}
  (ss : Icc a b ⊆ ⋃i, Ioo (c i) (d i)) :
  (of_real (b - a) : ennreal) ≤ ∑' i, of_real (d i - c i) :=
begin
  suffices : ∀ (s:finset ℕ) b
    (cv : Icc a b ⊆ ⋃ i ∈ (↑s:set ℕ), Ioo (c i) (d i)),
    (of_real (b - a) : ennreal) ≤ ∑ i in s, of_real (d i - c i),
  { rcases compact_Icc.elim_finite_subcover_image (λ (i : ℕ) (_ : i ∈ univ),
      @is_open_Ioo _ _ _ _ (c i) (d i)) (by simpa using ss) with ⟨s, su, hf, hs⟩,
    have e : (⋃ i ∈ (↑hf.to_finset:set ℕ),
      Ioo (c i) (d i)) = (⋃ i ∈ s, Ioo (c i) (d i)), {simp [set.ext_iff]},
    rw ennreal.tsum_eq_supr_sum,
    refine le_trans _ (le_supr _ hf.to_finset),
    exact this hf.to_finset _ (by simpa [e]) },
  clear ss b,
  refine λ s, finset.strong_induction_on s (λ s IH b cv, _),
  cases le_total b a with ab ab,
  { rw ennreal.of_real_eq_zero.2 (sub_nonpos.2 ab), exact zero_le _ },
  have := cv ⟨ab, le_refl _⟩, simp at this,
  rcases this with ⟨i, is, cb, bd⟩,
  rw [← finset.insert_erase is] at cv ⊢,
  rw [finset.coe_insert, bUnion_insert] at cv,
  rw [finset.sum_insert (finset.not_mem_erase _ _)],
  refine le_trans _ (add_le_add_left (IH _ (finset.erase_ssubset is) (c i) _) _),
  { refine le_trans (ennreal.of_real_le_of_real _) ennreal.of_real_add_le,
    rw sub_add_sub_cancel,
    exact sub_le_sub_right (le_of_lt bd) _ },
  { rintro x ⟨h₁, h₂⟩,
    refine (cv ⟨h₁, le_trans h₂ (le_of_lt cb)⟩).resolve_left
      (mt and.left (not_lt_of_le h₂)) }
end

@[simp] lemma lebesgue_outer_Icc (a b : ℝ) :
  lebesgue_outer (Icc a b) = of_real (b - a) :=
begin
  refine le_antisymm (by rw ← lebesgue_length_Icc; apply lebesgue_outer_le_length)
    (le_binfi $ λ f hf, ennreal.le_of_forall_epsilon_le $ λ ε ε0 h, _),
  rcases ennreal.exists_pos_sum_of_encodable
    (ennreal.zero_lt_coe_iff.2 ε0) ℕ with ⟨ε', ε'0, hε⟩,
  refine le_trans _ (add_le_add_left (le_of_lt hε) _),
  rw ← ennreal.tsum_add,
  choose g hg using show
    ∀ i, ∃ p:ℝ×ℝ, f i ⊆ Ioo p.1 p.2 ∧ (of_real (p.2 - p.1) : ennreal) < lebesgue_length (f i) + ε' i,
  { intro i,
    have := (ennreal.lt_add_right (lt_of_le_of_lt (ennreal.le_tsum i) h)
        (ennreal.zero_lt_coe_iff.2 (ε'0 i))),
    conv at this {to_lhs, rw lebesgue_length_eq_infi_Ioo},
    simpa [infi_lt_iff] },
  refine le_trans _ (ennreal.tsum_le_tsum $ λ i, le_of_lt (hg i).2),
  exact lebesgue_length_subadditive (subset.trans hf $
    Union_subset_Union $ λ i, (hg i).1)
end

@[simp] lemma lebesgue_outer_singleton (a : ℝ) : lebesgue_outer {a} = 0 :=
by simpa using lebesgue_outer_Icc a a

@[simp] lemma lebesgue_outer_Ico (a b : ℝ) :
  lebesgue_outer (Ico a b) = of_real (b - a) :=
by rw [← Icc_diff_right, lebesgue_outer.diff_null _ (lebesgue_outer_singleton _),
  lebesgue_outer_Icc]

@[simp] lemma lebesgue_outer_Ioo (a b : ℝ) :
  lebesgue_outer (Ioo a b) = of_real (b - a) :=
by rw [← Ico_diff_left, lebesgue_outer.diff_null _ (lebesgue_outer_singleton _), lebesgue_outer_Ico]

@[simp] lemma lebesgue_outer_Ioc (a b : ℝ) :
  lebesgue_outer (Ioc a b) = of_real (b - a) :=
by rw [← Icc_diff_left, lebesgue_outer.diff_null _ (lebesgue_outer_singleton _), lebesgue_outer_Icc]

lemma is_lebesgue_measurable_Iio {c : ℝ} :
  lebesgue_outer.caratheodory.is_measurable (Iio c) :=
outer_measure.of_function_caratheodory $ λ t,
le_infi $ λ a, le_infi $ λ b, le_infi $ λ h, begin
  refine le_trans (add_le_add
    (lebesgue_length_mono $ inter_subset_inter_left _ h)
    (lebesgue_length_mono $ diff_subset_diff_left h)) _,
  cases le_total a c with hac hca; cases le_total b c with hbc hcb;
    simp [*, -sub_eq_add_neg, sub_add_sub_cancel', le_refl],
  { simp [*, ← ennreal.of_real_add, -sub_eq_add_neg, sub_add_sub_cancel', le_refl] },
  { simp only [ennreal.of_real_eq_zero.2 (sub_nonpos.2 (le_trans hbc hca)), zero_add, le_refl] }
end

theorem lebesgue_outer_trim : lebesgue_outer.trim = lebesgue_outer :=
begin
  refine le_antisymm (λ s, _) (outer_measure.le_trim _),
  rw outer_measure.trim_eq_infi,
  refine le_infi (λ f, le_infi $ λ hf,
    ennreal.le_of_forall_epsilon_le $ λ ε ε0 h, _),
  rcases ennreal.exists_pos_sum_of_encodable
    (ennreal.zero_lt_coe_iff.2 ε0) ℕ with ⟨ε', ε'0, hε⟩,
  refine le_trans _ (add_le_add_left (le_of_lt hε) _),
  rw ← ennreal.tsum_add,
  choose g hg using show
    ∀ i, ∃ s, f i ⊆ s ∧ is_measurable s ∧ lebesgue_outer s ≤ lebesgue_length (f i) + of_real (ε' i),
  { intro i,
    have := (ennreal.lt_add_right (lt_of_le_of_lt (ennreal.le_tsum i) h)
        (ennreal.zero_lt_coe_iff.2 (ε'0 i))),
    conv at this {to_lhs, rw lebesgue_length},
    simp only [infi_lt_iff] at this,
    rcases this with ⟨a, b, h₁, h₂⟩,
    rw ← lebesgue_outer_Ico at h₂,
    exact ⟨_, h₁, is_measurable_Ico, le_of_lt $ by simpa using h₂⟩ },
  simp at hg,
  apply infi_le_of_le (Union g) _,
  apply infi_le_of_le (subset.trans hf $ Union_subset_Union (λ i, (hg i).1)) _,
  apply infi_le_of_le (is_measurable.Union (λ i, (hg i).2.1)) _,
  exact le_trans (lebesgue_outer.Union _) (ennreal.tsum_le_tsum $ λ i, (hg i).2.2)
end

lemma borel_le_lebesgue_measurable : borel ℝ ≤ lebesgue_outer.caratheodory :=
begin
  rw real.borel_eq_generate_from_Iio_rat,
  refine measurable_space.generate_from_le _,
  simp [is_lebesgue_measurable_Iio] { contextual := tt }
end

/-- Lebesgue measure on the Borel sets

The outer Lebesgue measure is the completion of this measure. (TODO: proof this)
-/
instance real.measure_space : measure_space ℝ :=
⟨{to_outer_measure := lebesgue_outer,
  m_Union := λ f hf, lebesgue_outer.Union_eq_of_caratheodory $
    λ i, borel_le_lebesgue_measurable _ (hf i),
  trimmed := lebesgue_outer_trim }⟩

@[simp] theorem lebesgue_to_outer_measure :
  (volume : measure ℝ).to_outer_measure = lebesgue_outer := rfl

end measure_theory

open measure_theory

section volume

open_locale interval

theorem real.volume_val (s) : volume s = lebesgue_outer s := rfl

instance real.no_atoms_volume : no_atoms_measure (volume : measure ℝ) :=
⟨lebesgue_outer_singleton⟩

@[simp]
lemma real.volume_Ico {a b : ℝ} : volume (Ico a b) = of_real (b - a) := lebesgue_outer_Ico a b

@[simp]
lemma real.volume_Icc {a b : ℝ} : volume (Icc a b) = of_real (b - a) := lebesgue_outer_Icc a b

@[simp]
lemma real.volume_Ioo {a b : ℝ} : volume (Ioo a b) = of_real (b - a) := lebesgue_outer_Ioo a b

@[simp]
lemma real.volume_Ioc {a b : ℝ} : volume (Ioc a b) = of_real (b - a) := lebesgue_outer_Ioc a b

@[simp]
lemma real.volume_singleton {a : ℝ} : volume ({a} : set ℝ) = 0 := lebesgue_outer_singleton a

@[simp] lemma real.volume_interval {a b : ℝ} : volume [a, b] = of_real (abs (b - a)) :=
begin
  rw [interval, real.volume_Icc],
  congr,
  exact max_sub_min_eq_abs _ _
end

instance real.locally_finite_volume : locally_finite_measure (volume : measure ℝ) :=
⟨λ x, ⟨Ioo (x - 1) (x + 1),
  mem_nhds_sets is_open_Ioo ⟨sub_lt_self _ zero_lt_one, lt_add_of_pos_right _ zero_lt_one⟩,
  by simp only [real.volume_Ioo, ennreal.of_real_lt_top]⟩⟩

lemma real.map_volume_add_left (a : ℝ) : measure.map ((+) a) volume = volume :=
eq.symm $ real.measure_ext_Ioo_rat $ λ p q,
  by simp [measure.map_apply (measurable_add_left a) is_measurable_Ioo, sub_sub_sub_cancel_right]

lemma real.map_volume_add_right (a : ℝ) : measure.map (λ x, x + a) volume = volume :=
by simpa only [add_comm] using real.map_volume_add_left a

lemma real.smul_map_volume_mul_left {a : ℝ} (h : a ≠ 0) :
  ennreal.of_real (abs a) • measure.map ((*) a) volume = volume :=
begin
  refine (real.measure_ext_Ioo_rat $ λ p q, _).symm,
  cases lt_or_gt_of_ne h with h h,
  { simp only [real.volume_Ioo, measure.smul_apply, ← ennreal.of_real_mul (le_of_lt $ neg_pos.2 h),
      measure.map_apply (measurable_mul_left a) is_measurable_Ioo, neg_sub_neg,
      ← neg_mul_eq_neg_mul, preimage_const_mul_Ioo_of_neg _ _ h, abs_of_neg h, mul_sub,
      mul_div_cancel' _ (ne_of_lt h)] },
  { simp only [real.volume_Ioo, measure.smul_apply, ← ennreal.of_real_mul (le_of_lt h),
      measure.map_apply (measurable_mul_left a) is_measurable_Ioo, preimage_const_mul_Ioo _ _ h,
      abs_of_pos h, mul_sub, mul_div_cancel' _ (ne_of_gt h)] }
end

lemma real.map_volume_mul_left {a : ℝ} (h : a ≠ 0) :
  measure.map ((*) a) volume = ennreal.of_real (abs a⁻¹) • volume :=
by conv_rhs { rw [← real.smul_map_volume_mul_left h, smul_smul,
  ← ennreal.of_real_mul (abs_nonneg _), ← abs_mul, inv_mul_cancel h, abs_one, ennreal.of_real_one,
  one_smul] }

lemma real.smul_map_volume_mul_right {a : ℝ} (h : a ≠ 0) :
  ennreal.of_real (abs a) • measure.map (λ x, x * a) volume = volume :=
by simpa only [mul_comm] using real.smul_map_volume_mul_left h

lemma real.map_volume_mul_right {a : ℝ} (h : a ≠ 0) :
  measure.map (λ x, x * a) volume = ennreal.of_real (abs a⁻¹) • volume :=
by simpa only [mul_comm] using real.map_volume_mul_left h

@[simp] lemma real.map_volume_neg : measure.map has_neg.neg (volume : measure ℝ) = volume :=
eq.symm $ real.measure_ext_Ioo_rat $ λ p q,
  by simp [measure.map_apply measurable_neg is_measurable_Ioo]

end volume
/-
section vitali

def vitali_aux_h (x : ℝ) (h : x ∈ Icc (0:ℝ) 1) :
  ∃ y ∈ Icc (0:ℝ) 1, ∃ q:ℚ, ↑q = x - y :=
⟨x, h, 0, by simp⟩

def vitali_aux (x : ℝ) (h : x ∈ Icc (0:ℝ) 1) : ℝ :=
classical.some (vitali_aux_h x h)

theorem vitali_aux_mem (x : ℝ) (h : x ∈ Icc (0:ℝ) 1) : vitali_aux x h ∈ Icc (0:ℝ) 1 :=
Exists.fst (classical.some_spec (vitali_aux_h x h):_)

theorem vitali_aux_rel (x : ℝ) (h : x ∈ Icc (0:ℝ) 1) :
 ∃ q:ℚ, ↑q = x - vitali_aux x h :=
Exists.snd (classical.some_spec (vitali_aux_h x h):_)

def vitali : set ℝ := {x | ∃ h, x = vitali_aux x h}

theorem vitali_nonmeasurable : ¬ is_null_measurable measure_space.μ vitali :=
sorry

end vitali
-/

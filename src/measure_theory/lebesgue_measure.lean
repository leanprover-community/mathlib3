/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import measure_theory.pi

/-!
# Lebesgue measure on the real line and on `ℝⁿ`
-/

noncomputable theory
open classical set filter
open ennreal (of_real)
open_locale big_operators ennreal

namespace measure_theory

/-!
### Preliminary definitions
-/

/-- Length of an interval. This is the largest monotonic function which correctly
  measures all intervals. -/
def lebesgue_length (s : set ℝ) : ℝ≥0∞ := ⨅a b (h : s ⊆ Ico a b), of_real (b - a)

@[simp] lemma lebesgue_length_empty : lebesgue_length ∅ = 0 :=
nonpos_iff_eq_zero.1 $ infi_le_of_le 0 $ infi_le_of_le 0 $ by simp

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
  refine ennreal.le_of_forall_pos_le_add (λ ε ε0 _, _),
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
  refine ennreal.le_of_forall_pos_le_add (λ ε ε0 _, _),
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
  (of_real (b - a) : ℝ≥0∞) ≤ ∑' i, of_real (d i - c i) :=
begin
  suffices : ∀ (s:finset ℕ) b
    (cv : Icc a b ⊆ ⋃ i ∈ (↑s:set ℕ), Ioo (c i) (d i)),
    (of_real (b - a) : ℝ≥0∞) ≤ ∑ i in s, of_real (d i - c i),
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
    (le_binfi $ λ f hf, ennreal.le_of_forall_pos_le_add $ λ ε ε0 h, _),
  rcases ennreal.exists_pos_sum_of_encodable
    (ennreal.zero_lt_coe_iff.2 ε0) ℕ with ⟨ε', ε'0, hε⟩,
  refine le_trans _ (add_le_add_left (le_of_lt hε) _),
  rw ← ennreal.tsum_add,
  choose g hg using show
    ∀ i, ∃ p:ℝ×ℝ, f i ⊆ Ioo p.1 p.2 ∧ (of_real (p.2 - p.1) : ℝ≥0∞) <
      lebesgue_length (f i) + ε' i,
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
  lebesgue_outer.caratheodory.measurable_set' (Iio c) :=
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
    ennreal.le_of_forall_pos_le_add $ λ ε ε0 h, _),
  rcases ennreal.exists_pos_sum_of_encodable
    (ennreal.zero_lt_coe_iff.2 ε0) ℕ with ⟨ε', ε'0, hε⟩,
  refine le_trans _ (add_le_add_left (le_of_lt hε) _),
  rw ← ennreal.tsum_add,
  choose g hg using show
    ∀ i, ∃ s, f i ⊆ s ∧ measurable_set s ∧
      lebesgue_outer s ≤ lebesgue_length (f i) + of_real (ε' i),
  { intro i,
    have := (ennreal.lt_add_right (lt_of_le_of_lt (ennreal.le_tsum i) h)
        (ennreal.zero_lt_coe_iff.2 (ε'0 i))),
    conv at this {to_lhs, rw lebesgue_length},
    simp only [infi_lt_iff] at this,
    rcases this with ⟨a, b, h₁, h₂⟩,
    rw ← lebesgue_outer_Ico at h₂,
    exact ⟨_, h₁, measurable_set_Ico, le_of_lt $ by simpa using h₂⟩ },
  simp at hg,
  apply infi_le_of_le (Union g) _,
  apply infi_le_of_le (subset.trans hf $ Union_subset_Union (λ i, (hg i).1)) _,
  apply infi_le_of_le (measurable_set.Union (λ i, (hg i).2.1)) _,
  exact le_trans (lebesgue_outer.Union _) (ennreal.tsum_le_tsum $ λ i, (hg i).2.2)
end

lemma borel_le_lebesgue_measurable : borel ℝ ≤ lebesgue_outer.caratheodory :=
begin
  rw real.borel_eq_generate_from_Iio_rat,
  refine measurable_space.generate_from_le _,
  simp [is_lebesgue_measurable_Iio] { contextual := tt }
end

/-!
### Definition of the Lebesgue measure and lengths of intervals
-/

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

namespace real

variables {ι : Type*} [fintype ι]

open_locale topological_space

theorem volume_val (s) : volume s = lebesgue_outer s := rfl

instance has_no_atoms_volume : has_no_atoms (volume : measure ℝ) :=
⟨lebesgue_outer_singleton⟩

@[simp] lemma volume_Ico {a b : ℝ} : volume (Ico a b) = of_real (b - a) := lebesgue_outer_Ico a b

@[simp] lemma volume_Icc {a b : ℝ} : volume (Icc a b) = of_real (b - a) := lebesgue_outer_Icc a b

@[simp] lemma volume_Ioo {a b : ℝ} : volume (Ioo a b) = of_real (b - a) := lebesgue_outer_Ioo a b

@[simp] lemma volume_Ioc {a b : ℝ} : volume (Ioc a b) = of_real (b - a) := lebesgue_outer_Ioc a b

@[simp] lemma volume_singleton {a : ℝ} : volume ({a} : set ℝ) = 0 := lebesgue_outer_singleton a

@[simp] lemma volume_interval {a b : ℝ} : volume (interval a b) = of_real (abs (b - a)) :=
by rw [interval, volume_Icc, max_sub_min_eq_abs]

@[simp] lemma volume_Ioi {a : ℝ} : volume (Ioi a) = ∞ :=
top_unique $ le_of_tendsto' ennreal.tendsto_nat_nhds_top $ λ n,
calc (n : ℝ≥0∞) = volume (Ioo a (a + n)) : by simp
... ≤ volume (Ioi a) : measure_mono Ioo_subset_Ioi_self

@[simp] lemma volume_Ici {a : ℝ} : volume (Ici a) = ∞ :=
by simp [← measure_congr Ioi_ae_eq_Ici]

@[simp] lemma volume_Iio {a : ℝ} : volume (Iio a) = ∞ :=
top_unique $ le_of_tendsto' ennreal.tendsto_nat_nhds_top $ λ n,
calc (n : ℝ≥0∞) = volume (Ioo (a - n) a) : by simp
... ≤ volume (Iio a) : measure_mono Ioo_subset_Iio_self

@[simp] lemma volume_Iic {a : ℝ} : volume (Iic a) = ∞ :=
by simp [← measure_congr Iio_ae_eq_Iic]

instance locally_finite_volume : locally_finite_measure (volume : measure ℝ) :=
⟨λ x, ⟨Ioo (x - 1) (x + 1),
  mem_nhds_sets is_open_Ioo ⟨sub_lt_self _ zero_lt_one, lt_add_of_pos_right _ zero_lt_one⟩,
  by simp only [real.volume_Ioo, ennreal.of_real_lt_top]⟩⟩

/-!
### Volume of a box in `ℝⁿ`
-/

lemma volume_Icc_pi {a b : ι → ℝ} : volume (Icc a b) = ∏ i, ennreal.of_real (b i - a i) :=
begin
  rw [← pi_univ_Icc, volume_pi_pi],
  { simp only [real.volume_Icc] },
  { exact λ i, measurable_set_Icc }
end

@[simp] lemma volume_Icc_pi_to_real {a b : ι → ℝ} (h : a ≤ b) :
  (volume (Icc a b)).to_real = ∏ i, (b i - a i) :=
by simp only [volume_Icc_pi, ennreal.to_real_prod, ennreal.to_real_of_real (sub_nonneg.2 (h _))]

lemma volume_pi_Ioo {a b : ι → ℝ} :
  volume (pi univ (λ i, Ioo (a i) (b i))) = ∏ i, ennreal.of_real (b i - a i) :=
(measure_congr measure.univ_pi_Ioo_ae_eq_Icc).trans volume_Icc_pi

@[simp] lemma volume_pi_Ioo_to_real {a b : ι → ℝ} (h : a ≤ b) :
  (volume (pi univ (λ i, Ioo (a i) (b i)))).to_real = ∏ i, (b i - a i) :=
by simp only [volume_pi_Ioo, ennreal.to_real_prod, ennreal.to_real_of_real (sub_nonneg.2 (h _))]

lemma volume_pi_Ioc {a b : ι → ℝ} :
  volume (pi univ (λ i, Ioc (a i) (b i))) = ∏ i, ennreal.of_real (b i - a i) :=
(measure_congr measure.univ_pi_Ioc_ae_eq_Icc).trans volume_Icc_pi

@[simp] lemma volume_pi_Ioc_to_real {a b : ι → ℝ} (h : a ≤ b) :
  (volume (pi univ (λ i, Ioc (a i) (b i)))).to_real = ∏ i, (b i - a i) :=
by simp only [volume_pi_Ioc, ennreal.to_real_prod, ennreal.to_real_of_real (sub_nonneg.2 (h _))]

lemma volume_pi_Ico {a b : ι → ℝ} :
  volume (pi univ (λ i, Ico (a i) (b i))) = ∏ i, ennreal.of_real (b i - a i) :=
(measure_congr measure.univ_pi_Ico_ae_eq_Icc).trans volume_Icc_pi

@[simp] lemma volume_pi_Ico_to_real {a b : ι → ℝ} (h : a ≤ b) :
  (volume (pi univ (λ i, Ico (a i) (b i)))).to_real = ∏ i, (b i - a i) :=
by simp only [volume_pi_Ico, ennreal.to_real_prod, ennreal.to_real_of_real (sub_nonneg.2 (h _))]

/-!
### Images of the Lebesgue measure under translation/multiplication/...
-/

lemma map_volume_add_left (a : ℝ) : measure.map ((+) a) volume = volume :=
eq.symm $ real.measure_ext_Ioo_rat $ λ p q,
  by simp [measure.map_apply (measurable_const_add a) measurable_set_Ioo, sub_sub_sub_cancel_right]

lemma map_volume_add_right (a : ℝ) : measure.map (+ a) volume = volume :=
by simpa only [add_comm] using real.map_volume_add_left a

lemma smul_map_volume_mul_left {a : ℝ} (h : a ≠ 0) :
  ennreal.of_real (abs a) • measure.map ((*) a) volume = volume :=
begin
  refine (real.measure_ext_Ioo_rat $ λ p q, _).symm,
  cases lt_or_gt_of_ne h with h h,
  { simp only [real.volume_Ioo, measure.smul_apply, ← ennreal.of_real_mul (le_of_lt $ neg_pos.2 h),
      measure.map_apply (measurable_const_mul a) measurable_set_Ioo, neg_sub_neg,
      ← neg_mul_eq_neg_mul, preimage_const_mul_Ioo_of_neg _ _ h, abs_of_neg h, mul_sub,
      mul_div_cancel' _ (ne_of_lt h)] },
  { simp only [real.volume_Ioo, measure.smul_apply, ← ennreal.of_real_mul (le_of_lt h),
      measure.map_apply (measurable_const_mul a) measurable_set_Ioo, preimage_const_mul_Ioo _ _ h,
      abs_of_pos h, mul_sub, mul_div_cancel' _ (ne_of_gt h)] }
end

lemma map_volume_mul_left {a : ℝ} (h : a ≠ 0) :
  measure.map ((*) a) volume = ennreal.of_real (abs a⁻¹) • volume :=
by conv_rhs { rw [← real.smul_map_volume_mul_left h, smul_smul,
  ← ennreal.of_real_mul (abs_nonneg _), ← abs_mul, inv_mul_cancel h, abs_one, ennreal.of_real_one,
  one_smul] }

lemma smul_map_volume_mul_right {a : ℝ} (h : a ≠ 0) :
  ennreal.of_real (abs a) • measure.map (* a) volume = volume :=
by simpa only [mul_comm] using real.smul_map_volume_mul_left h

lemma map_volume_mul_right {a : ℝ} (h : a ≠ 0) :
  measure.map (* a) volume = ennreal.of_real (abs a⁻¹) • volume :=
by simpa only [mul_comm] using real.map_volume_mul_left h

@[simp] lemma map_volume_neg : measure.map has_neg.neg (volume : measure ℝ) = volume :=
eq.symm $ real.measure_ext_Ioo_rat $ λ p q,
  by simp [show measure.map has_neg.neg volume (Ioo (p : ℝ) q) = _,
    from measure.map_apply measurable_neg measurable_set_Ioo]

end real

open_locale topological_space

lemma filter.eventually.volume_pos_of_nhds_real {p : ℝ → Prop} {a : ℝ} (h : ∀ᶠ x in 𝓝 a, p x) :
  (0 : ℝ≥0∞) < volume {x | p x} :=
begin
  rcases h.exists_Ioo_subset with ⟨l, u, hx, hs⟩,
  refine lt_of_lt_of_le _ (measure_mono hs),
  simpa [-mem_Ioo] using hx.1.trans hx.2
end

section region_between

open_locale classical

variable {α : Type*}

/-- The region between two real-valued functions on an arbitrary set. -/
def region_between (f g : α → ℝ) (s : set α) : set (α × ℝ) :=
{p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Ioo (f p.1) (g p.1)}

lemma region_between_subset (f g : α → ℝ) (s : set α) : region_between f g s ⊆ s.prod univ :=
by simpa only [prod_univ, region_between, set.preimage, set_of_subset_set_of] using λ a, and.left

variables [measurable_space α] {μ : measure α} {f g : α → ℝ} {s : set α}

/-- The region between two measurable functions on a measurable set is measurable. -/
lemma measurable_set_region_between
  (hf : measurable f) (hg : measurable g) (hs : measurable_set s) :
  measurable_set (region_between f g s) :=
begin
  dsimp only [region_between, Ioo, mem_set_of_eq, set_of_and],
  refine measurable_set.inter _ ((measurable_set_lt (hf.comp measurable_fst) measurable_snd).inter
    (measurable_set_lt measurable_snd (hg.comp measurable_fst))),
  convert hs.prod measurable_set.univ,
  simp only [and_true, mem_univ],
end

theorem volume_region_between_eq_lintegral'
  (hf : measurable f) (hg : measurable g) (hs : measurable_set s) :
  μ.prod volume (region_between f g s) = ∫⁻ y in s, ennreal.of_real ((g - f) y) ∂μ :=
begin
  rw measure.prod_apply,
  { have h : (λ x, volume {a | x ∈ s ∧ a ∈ Ioo (f x) (g x)})
            = s.indicator (λ x, ennreal.of_real (g x - f x)),
    { funext x,
      rw indicator_apply,
      split_ifs,
      { have hx : {a | x ∈ s ∧ a ∈ Ioo (f x) (g x)} = Ioo (f x) (g x) := by simp [h, Ioo],
        simp only [hx, real.volume_Ioo, sub_zero] },
      { have hx : {a | x ∈ s ∧ a ∈ Ioo (f x) (g x)} = ∅ := by simp [h],
        simp only [hx, measure_empty] } },
    dsimp only [region_between, preimage_set_of_eq],
    rw [h, lintegral_indicator];
    simp only [hs, pi.sub_apply] },
  { exact measurable_set_region_between hf hg hs },
end

/-- The volume of the region between two almost everywhere measurable functions on a measurable set
    can be represented as a Lebesgue integral. -/
theorem volume_region_between_eq_lintegral [sigma_finite μ]
  (hf : ae_measurable f (μ.restrict s)) (hg : ae_measurable g (μ.restrict s))
  (hs : measurable_set s) :
  μ.prod volume (region_between f g s) = ∫⁻ y in s, ennreal.of_real ((g - f) y) ∂μ :=
begin
  have h₁ : (λ y, ennreal.of_real ((g - f) y))
          =ᵐ[μ.restrict s]
              λ y, ennreal.of_real ((ae_measurable.mk g hg - ae_measurable.mk f hf) y) :=
    eventually_eq.fun_comp (eventually_eq.sub hg.ae_eq_mk hf.ae_eq_mk) _,
  have h₂ : (μ.restrict s).prod volume (region_between f g s) =
    (μ.restrict s).prod volume (region_between (ae_measurable.mk f hf) (ae_measurable.mk g hg) s),
  { apply measure_congr,
    apply eventually_eq.inter, { refl },
    exact eventually_eq.inter
            (eventually_eq.comp₂ (ae_eq_comp' measurable_fst hf.ae_eq_mk
              measure.prod_fst_absolutely_continuous) _ eventually_eq.rfl)
            (eventually_eq.comp₂ eventually_eq.rfl _
              (ae_eq_comp' measurable_fst hg.ae_eq_mk measure.prod_fst_absolutely_continuous)) },
  rw [lintegral_congr_ae h₁,
      ← volume_region_between_eq_lintegral' hf.measurable_mk hg.measurable_mk hs],
  convert h₂ using 1,
  { rw measure.restrict_prod_eq_prod_univ,
    exacts [ (measure.restrict_eq_self_of_subset_of_measurable (hs.prod measurable_set.univ)
      (region_between_subset f g s)).symm, hs], },
  { rw measure.restrict_prod_eq_prod_univ,
    exacts [(measure.restrict_eq_self_of_subset_of_measurable (hs.prod measurable_set.univ)
      (region_between_subset (ae_measurable.mk f hf) (ae_measurable.mk g hg) s)).symm, hs] },
end


theorem volume_region_between_eq_integral' [sigma_finite μ]
  (f_int : integrable_on f s μ) (g_int : integrable_on g s μ)
  (hs : measurable_set s) (hfg : f ≤ᵐ[μ.restrict s] g ) :
  μ.prod volume (region_between f g s) = ennreal.of_real (∫ y in s, (g - f) y ∂μ) :=
begin
  have h : g - f =ᵐ[μ.restrict s] (λ x, nnreal.of_real (g x - f x)),
  { apply hfg.mono,
    simp only [nnreal.of_real, max, sub_nonneg, pi.sub_apply],
    intros x hx,
    split_ifs,
    refl },
  rw [volume_region_between_eq_lintegral f_int.ae_measurable g_int.ae_measurable hs,
    integral_congr_ae h, lintegral_congr_ae,
    lintegral_coe_eq_integral _ ((integrable_congr h).mp (g_int.sub f_int))],
  simpa only,
end

/-- If two functions are integrable on a measurable set, and one function is less than
    or equal to the other on that set, then the volume of the region
    between the two functions can be represented as an integral. -/
theorem volume_region_between_eq_integral [sigma_finite μ]
  (f_int : integrable_on f s μ) (g_int : integrable_on g s μ)
  (hs : measurable_set s) (hfg : ∀ x ∈ s, f x ≤ g x) :
  μ.prod volume (region_between f g s) = ennreal.of_real (∫ y in s, (g - f) y ∂μ) :=
volume_region_between_eq_integral' f_int g_int hs
  ((ae_restrict_iff' hs).mpr (eventually_of_forall hfg))

end region_between

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

theorem vitali_nonmeasurable : ¬ null_measurable_set measure_space.μ vitali :=
sorry

end vitali
-/

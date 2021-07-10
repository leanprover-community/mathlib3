/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import measure_theory.pi

/-!
# stieltjes measure on the real line and on `ℝⁿ`
-/

noncomputable theory
open classical set filter
open ennreal (of_real)
open_locale big_operators ennreal nnreal topological_space

structure stieltjes_function :=
(to_fun : ℝ → ℝ)
(mono' : monotone to_fun)
(right_continuous' : ∀ x, continuous_within_at to_fun (Ici x) x)

namespace stieltjes_function

instance : has_coe_to_fun stieltjes_function := ⟨_, to_fun⟩

variable (f : stieltjes_function)

lemma mono : monotone f := f.mono'

lemma right_continuous (x : ℝ) : continuous_within_at f (Ici x) x := f.right_continuous' x

/-!
### Preliminary definitions
-/

/-- The limit of a Stieltjes function to the left of `x` (it exists by monotonicity). The fact that
it is indeed a left limit is asserted in `tendsto_left_lim` -/
@[irreducible] def left_lim (x : ℝ) := Sup (f '' (Iio x))

lemma tendsto_left_lim (x : ℝ) : tendsto f (𝓝[Iio x] x) (𝓝 (f.left_lim x)) :=
by { rw left_lim, exact f.mono.tendsto_nhds_within_Iio x }

lemma left_lim_le {x y : ℝ} (h : x ≤ y) : f.left_lim x ≤ f y :=
begin
  apply le_of_tendsto (f.tendsto_left_lim x),
  filter_upwards [self_mem_nhds_within],
  assume z hz,
  exact (f.mono (le_of_lt hz)).trans (f.mono h)
end

lemma le_left_lim {x y : ℝ} (h : x < y) : f x ≤ f.left_lim y :=
begin
  apply ge_of_tendsto (f.tendsto_left_lim y),
  apply mem_nhds_within_Iio_iff_exists_Ioo_subset.2 ⟨x, h, _⟩,
  assume z hz,
  exact f.mono hz.1.le,
end

/-- Length of an interval. This is the largest monotonic function which correctly
  measures all intervals. -/
def length (s : set ℝ) : ℝ≥0∞ := ⨅a b (h : s ⊆ Ioc a b), of_real (f b - f a)

@[simp] lemma length_empty : f.length ∅ = 0 :=
nonpos_iff_eq_zero.1 $ infi_le_of_le 0 $ infi_le_of_le 0 $ by simp

@[simp] lemma length_Ioc (a b : ℝ) :
  f.length (Ioc a b) = of_real (f b - f a) :=
begin
  refine le_antisymm (infi_le_of_le a $ binfi_le b (subset.refl _))
    (le_infi $ λ a', le_infi $ λ b', le_infi $ λ h, ennreal.coe_le_coe.2 _),
  cases le_or_lt b a with ab ab,
  { rw real.to_nnreal_of_nonpos (sub_nonpos.2 (f.mono ab)), apply zero_le, },
  cases (Ioc_subset_Ioc_iff ab).1 h with h₁ h₂,
  exact real.to_nnreal_le_to_nnreal (sub_le_sub (f.mono h₁) (f.mono h₂))
end

lemma length_mono {s₁ s₂ : set ℝ} (h : s₁ ⊆ s₂) :
  f.length s₁ ≤ f.length s₂ :=
infi_le_infi $ λ a, infi_le_infi $ λ b, infi_le_infi2 $ λ h', ⟨subset.trans h h', le_refl _⟩

open measure_theory

/-- The Stieltjes outer measure associated to a Stieltjes function. -/
protected def outer : outer_measure ℝ :=
outer_measure.of_function f.length f.length_empty

lemma outer_le_length (s : set ℝ) : f.outer s ≤ f.length s :=
outer_measure.of_function_le _

/-- If a compact interval `[a, b]` is covered by a union of open interval `(c i, d i)`, then
`f b - f a ≤ ∑ f (d i) - f (c i)`. This is an auxiliary technical statement to prove the same
statement for half-open intervals, the point of the current statement being that one can use
compactness to reduce it to a finite sum, and argue by induction on the size of the covering set. -/
lemma length_subadditive_Icc_Ioo {a b : ℝ} {c d : ℕ → ℝ}
  (ss : Icc a b ⊆ ⋃ i, Ioo (c i) (d i)) :
  of_real (f b - f a) ≤ ∑' i, of_real (f (d i) - f (c i)) :=
begin
  suffices : ∀ (s:finset ℕ) b
    (cv : Icc a b ⊆ ⋃ i ∈ (↑s:set ℕ), Ioo (c i) (d i)),
    (of_real (f b - f a) : ℝ≥0∞) ≤ ∑ i in s, of_real (f (d i) - f (c i)),
  { rcases is_compact_Icc.elim_finite_subcover_image (λ (i : ℕ) (_ : i ∈ univ),
      @is_open_Ioo _ _ _ _ (c i) (d i)) (by simpa using ss) with ⟨s, su, hf, hs⟩,
    have e : (⋃ i ∈ (↑hf.to_finset:set ℕ), Ioo (c i) (d i)) = (⋃ i ∈ s, Ioo (c i) (d i)),
      by simp only [ext_iff, exists_prop, finset.set_bUnion_coe, mem_Union, forall_const, iff_self,
                    finite.mem_to_finset],
    rw ennreal.tsum_eq_supr_sum,
    refine le_trans _ (le_supr _ hf.to_finset),
    exact this hf.to_finset _ (by simpa only [e]) },
  clear ss b,
  refine λ s, finset.strong_induction_on s (λ s IH b cv, _),
  cases le_total b a with ab ab,
  { rw ennreal.of_real_eq_zero.2 (sub_nonpos.2 (f.mono ab)), exact zero_le _, },
  have := cv ⟨ab, le_refl _⟩, simp at this,
  rcases this with ⟨i, is, cb, bd⟩,
  rw [← finset.insert_erase is] at cv ⊢,
  rw [finset.coe_insert, bUnion_insert] at cv,
  rw [finset.sum_insert (finset.not_mem_erase _ _)],
  refine le_trans _ (add_le_add_left (IH _ (finset.erase_ssubset is) (c i) _) _),
  { refine le_trans (ennreal.of_real_le_of_real _) ennreal.of_real_add_le,
    rw sub_add_sub_cancel,
    exact sub_le_sub_right (f.mono bd.le) _ },
  { rintro x ⟨h₁, h₂⟩,
    refine (cv ⟨h₁, le_trans h₂ (le_of_lt cb)⟩).resolve_left
      (mt and.left (not_lt_of_le h₂)) }
end

@[simp] lemma outer_Ioc (a b : ℝ) :
  f.outer (Ioc a b) = of_real (f b - f a) :=
begin
  /- It suffices to show that, if `(a, b]` is covered by sets `s i`, then `f b - f a` is bounded
  by `∑ f.length (s i) + ε`. The difficulty is that `f.length` is expressed in terms of half-open
  intervals, while we would like to have a compact interval covered by open intervals to use
  compactness and finite sums, as provided by `length_subadditive_Icc_Ioo`. The trick is to use the
  right-continuity of `f`. If `a'` is close enough to `a` on its right, then `[a', b]` is still
  covered by the sets `s i` and moreover `f b - f a'` is very close to `f b - f a` (up to `ε/2`).
  Also, by definition one can cover `s i` by a half-closed interval `(p i, q i]` with `f`-length
  very close to  that of `s i` (within a suitably small `ε' i`, say). If one moves `q i` very
  slightly to the right, then the `f`-length will change very little by right continuity, and we
  will get an open interval `(p i, q' i)` covering `s i` with `f (q' i) - f (p i)` within `ε' i`
  of the `f`-length of `s i`. -/
  refine le_antisymm (by { rw ← f.length_Ioc, apply outer_le_length })
    (le_binfi $ λ s hs, ennreal.le_of_forall_pos_le_add $ λ ε εpos h, _),
  let δ := ε/2,
  have δpos : 0 < δ := nnreal.half_pos εpos,
  rcases ennreal.exists_pos_sum_of_encodable
    (ennreal.zero_lt_coe_iff.2 δpos) ℕ with ⟨ε', ε'0, hε⟩,
  obtain ⟨a', ha', aa'⟩ : ∃ a', f a' - f a < δ ∧ a < a',
  { have A : continuous_within_at (λ r, f r - f a) (Ioi a) a,
    { refine continuous_within_at.sub _ continuous_within_at_const,
      exact (f.right_continuous a).mono Ioi_subset_Ici_self },
    have B : f a - f a < δ, by rwa [sub_self],
    exact (((tendsto_order.1 A).2 _ B).and self_mem_nhds_within).exists },
  have : ∀ i, ∃ p:ℝ×ℝ, s i ⊆ Ioo p.1 p.2 ∧
                        (of_real (f p.2 - f p.1) : ℝ≥0∞) < f.length (s i) + ε' i,
  { intro i,
    have := (ennreal.lt_add_right (lt_of_le_of_lt (ennreal.le_tsum i) h)
        (ennreal.zero_lt_coe_iff.2 (ε'0 i))),
    conv at this { to_lhs, rw length },
    simp only [infi_lt_iff, exists_prop] at this,
    rcases this with ⟨p, q', spq, hq'⟩,
    have : continuous_within_at (λ r, of_real (f r - f p)) (Ioi q') q',
    { apply ennreal.continuous_of_real.continuous_at.comp_continuous_within_at,
      refine continuous_within_at.sub _ continuous_within_at_const,
      exact (f.right_continuous q').mono Ioi_subset_Ici_self },
    rcases (((tendsto_order.1 this).2 _ hq').and self_mem_nhds_within).exists with ⟨q, hq, q'q⟩,
    exact ⟨⟨p, q⟩, spq.trans (Ioc_subset_Ioo_right q'q), hq⟩ },
  choose g hg using this,
  have I_subset : Icc a' b ⊆ ⋃ i, Ioo (g i).1 (g i).2 := calc
    Icc a' b ⊆ Ioc a b : λ x hx, ⟨aa'.trans_le hx.1, hx.2⟩
    ... ⊆ ⋃ i, s i : hs
    ... ⊆ ⋃ i, Ioo (g i).1 (g i).2 : Union_subset_Union (λ i, (hg i).1),
  calc of_real (f b - f a)
      = of_real ((f b - f a') + (f a' - f a)) : by rw sub_add_sub_cancel
  ... ≤ of_real (f b - f a') + of_real (f a' - f a) : ennreal.of_real_add_le
  ... ≤ (∑' i, of_real (f (g i).2 - f (g i).1)) + of_real δ :
    add_le_add (f.length_subadditive_Icc_Ioo I_subset) (ennreal.of_real_le_of_real ha'.le)
  ... ≤ (∑' i, (f.length (s i) + ε' i)) + δ :
    add_le_add (ennreal.tsum_le_tsum (λ i, (hg i).2.le))
      (by simp only [ennreal.of_real_coe_nnreal, le_rfl])
  ... = (∑' i, f.length (s i)) + (∑' i, ε' i) + δ : by rw [ennreal.tsum_add]
  ... ≤ (∑' i, f.length (s i)) + δ + δ : add_le_add (add_le_add le_rfl hε.le) le_rfl
  ... = ∑' (i : ℕ), f.length (s i) + ε : by simp [add_assoc, ennreal.add_halves]
end

lemma measurable_set_Ioi {c : ℝ} :
  f.outer.caratheodory.measurable_set' (Ioi c) :=
begin
  apply outer_measure.of_function_caratheodory (λ t, _),
  refine le_infi (λ a, le_infi (λ b, le_infi (λ h, _))),
  refine le_trans (add_le_add
    (f.length_mono $ inter_subset_inter_left _ h)
    (f.length_mono $ diff_subset_diff_left h)) _,
  cases le_total a c with hac hac; cases le_total b c with hbc hbc,
  { simp only [Ioc_inter_Ioi, f.length_Ioc, hac, sup_eq_max, hbc, le_refl,
      Ioc_eq_empty, max_eq_right, min_eq_left, Ioc_diff_Ioi, f.length_empty, zero_add] },
  { simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_right,
      sup_eq_max, ←ennreal.of_real_add, f.mono hac, f.mono hbc, sub_nonneg, sub_add_sub_cancel,
      le_refl, max_eq_right] },
  { simp only [hbc, le_refl, Ioc_eq_empty, Ioc_inter_Ioi, min_eq_left, Ioc_diff_Ioi,
      f.length_empty, zero_add, or_true, le_sup_iff, f.length_Ioc] },
  { simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_right,
      sup_eq_max, le_refl, Ioc_eq_empty, add_zero, max_eq_left, f.length_empty] }
end

theorem outer_trim : f.outer.trim = f.outer :=
begin
  refine le_antisymm (λ s, _) (outer_measure.le_trim _),
  rw outer_measure.trim_eq_infi,
  refine le_infi (λ t, le_infi $ λ ht,
    ennreal.le_of_forall_pos_le_add $ λ ε ε0 h, _),
  rcases ennreal.exists_pos_sum_of_encodable
    (ennreal.zero_lt_coe_iff.2 ε0) ℕ with ⟨ε', ε'0, hε⟩,
  refine le_trans _ (add_le_add_left (le_of_lt hε) _),
  rw ← ennreal.tsum_add,
  choose g hg using show
    ∀ i, ∃ s, t i ⊆ s ∧ measurable_set s ∧
      f.outer s ≤ f.length (t i) + of_real (ε' i),
  { intro i,
    have := (ennreal.lt_add_right (lt_of_le_of_lt (ennreal.le_tsum i) h)
        (ennreal.zero_lt_coe_iff.2 (ε'0 i))),
    conv at this {to_lhs, rw length},
    simp only [infi_lt_iff] at this,
    rcases this with ⟨a, b, h₁, h₂⟩,
    rw ← f.outer_Ioc at h₂,
    exact ⟨_, h₁, measurable_set_Ioc, le_of_lt $ by simpa using h₂⟩ },
  simp at hg,
  apply infi_le_of_le (Union g) _,
  apply infi_le_of_le (subset.trans ht $ Union_subset_Union (λ i, (hg i).1)) _,
  apply infi_le_of_le (measurable_set.Union (λ i, (hg i).2.1)) _,
  exact le_trans (f.outer.Union _) (ennreal.tsum_le_tsum $ λ i, (hg i).2.2)
end

lemma borel_le_measurable : borel ℝ ≤ f.outer.caratheodory :=
begin
  rw borel_eq_generate_Ioi,
  refine measurable_space.generate_from_le _,
  simp [f.measurable_set_Ioi] { contextual := tt }
end

/-- The measure associated to a Stieltjes function, giving mass `f b - f a` to the
interval `(a, b]`. -/
protected def measure : measure ℝ :=
{ to_outer_measure := f.outer,
  m_Union := λ s hs, f.outer.Union_eq_of_caratheodory $
    λ i, f.borel_le_measurable _ (hs i),
  trimmed := f.outer_trim }

@[simp] lemma measure_Ioc (a b : ℝ) : f.measure (Ioc a b) = of_real (f b - f a) :=
f.outer_Ioc a b

@[simp] lemma measure_singleton (a : ℝ) : f.measure {a} = of_real (f a - f.left_lim a) :=
begin
  have T := exists_mono
  have Z := tendsto_measure_Inter,
end

#exit


/-!
### Definition of the stieltjes measure and lengths of intervals
-/

/-- stieltjes measure on the Borel sets

The outer stieltjes measure is the completion of this measure. (TODO: proof this)
-/
instance real.measure_space : measure_space ℝ :=
⟨{outer_measure := stieltjes_outer,
  m_Union := λ f hf, stieltjes_outer.Union_eq_of_caratheodory $
    λ i, borel_le_stieltjes_measurable _ (hf i),
  trimmed := stieltjes_outer_trim }⟩

@[simp] theorem stieltjes_outer_measure :
  (volume : measure ℝ).outer_measure = stieltjes_outer := rfl

end measure_theory

open measure_theory

namespace real

variables {ι : Type*} [fintype ι]

open_locale topological_space

theorem volume_val (s) : volume s = stieltjes_outer s := rfl

instance has_no_atoms_volume : has_no_atoms (volume : measure ℝ) :=
⟨stieltjes_outer_singleton⟩

@[simp] lemma volume_Ico {a b : ℝ} : volume (Ico a b) = of_real (b - a) := stieltjes_outer_Ico a b

@[simp] lemma volume_Icc {a b : ℝ} : volume (Icc a b) = of_real (b - a) := stieltjes_outer_Icc a b

@[simp] lemma volume_Ioo {a b : ℝ} : volume (Ioo a b) = of_real (b - a) := stieltjes_outer_Ioo a b

@[simp] lemma volume_Ioc {a b : ℝ} : volume (Ioc a b) = of_real (b - a) := stieltjes_outer_Ioc a b

@[simp] lemma volume_singleton {a : ℝ} : volume ({a} : set ℝ) = 0 := stieltjes_outer_singleton a

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
  is_open.mem_nhds is_open_Ioo ⟨sub_lt_self _ zero_lt_one, lt_add_of_pos_right _ zero_lt_one⟩,
  by simp only [real.volume_Ioo, ennreal.of_real_lt_top]⟩⟩

instance finite_measure_restrict_Icc (x y : ℝ) : finite_measure (volume.restrict (Icc x y)) :=
⟨by simp⟩

instance finite_measure_restrict_Ico (x y : ℝ) : finite_measure (volume.restrict (Ico x y)) :=
⟨by simp⟩

instance finite_measure_restrict_Ioc (x y : ℝ) : finite_measure (volume.restrict (Ioc x y)) :=
 ⟨by simp⟩

instance finite_measure_restrict_Ioo (x y : ℝ) : finite_measure (volume.restrict (Ioo x y)) :=
⟨by simp⟩

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
### Images of the stieltjes measure under translation/multiplication/...
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
    can be represented as a stieltjes integral. -/
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
  have h : g - f =ᵐ[μ.restrict s] (λ x, real.to_nnreal (g x - f x)),
  { apply hfg.mono,
    simp only [real.to_nnreal, max, sub_nonneg, pi.sub_apply],
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

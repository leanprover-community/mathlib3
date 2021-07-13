/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.integration

/-!

# Vector valued measures

This file defines vector valued measures, which are σ-additive functions from a set to a add monoid
`M` such that it maps the empty set and non-measurable sets to zero. In the case
that `M = ℝ`, we called the vector measure a signed measure and write `signed_measure α`.
Similarly, when `M = ℂ`, we call the measure a complex measure and write `complex_measure α`.

## Main definitions

* `vector_measure` is a vector valued, σ-additive function that maps the empty
  and non-measurable set to zero.

## Implementation notes

We require all non-measurable sets to be mapped to zero in order for the extensionality lemma
to only compare the underlying functions for measurable sets.

We use `has_sum` instead of `tsum` in the definition of vector measures in comparison to `measure`
since this provides summablity.
## Tags

vector measure, signed measure, complex measure
-/

noncomputable theory

open_locale classical big_operators nnreal ennreal

namespace measure_theory

variables {α β : Type*} [measurable_space α]

/-- A vector measure on a measurable space `α` is a σ-additive `M`-valued function (for some `M`
a add monoid) such that the empty set and non-measurable sets are mapped to zero. -/
structure vector_measure (α : Type*) [measurable_space α]
  (M : Type*) [add_comm_monoid M] [topological_space M] :=
(measure_of : set α → M)
(empty : measure_of ∅ = 0)
(not_measurable ⦃i : set α⦄ : ¬ measurable_set i → measure_of i = 0)
(m_Union ⦃f : ℕ → set α⦄ :
  (∀ i, measurable_set (f i)) → pairwise (disjoint on f) →
  has_sum (λ i, measure_of (f i)) (measure_of (⋃ i, f i)))

-- A `signed_measure` is a `ℝ`-vector measure.
notation `signed_measure ` α := vector_measure α ℝ
-- A `complex_measure` is a `ℂ`-vector_measure.
notation `complex_measure ` α := vector_measure α ℂ

open set measure_theory

namespace vector_measure

section

variables {M : Type*} [add_comm_monoid M] [topological_space M]

instance : has_coe_to_fun (vector_measure α M) :=
⟨λ _, set α → M, vector_measure.measure_of⟩

@[simp]
lemma apply (v : vector_measure α M) (i : set α) : v.measure_of i = v i := rfl

@[simp]
lemma of_empty (v : vector_measure α M) : v ∅ = 0 := v.empty

lemma of_not_measurable_set (v : vector_measure α M)
  {i : set α} (hi : ¬ measurable_set i) : v i = 0 := v.not_measurable hi

lemma has_sum_of_disjoint_Union (v : vector_measure α M) {f : ℕ → set α}
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) :
  has_sum (λ i, v (f i)) (v (⋃ i, f i)) :=
v.m_Union hf₁ hf₂

lemma of_disjoint_Union [t2_space M] (v : vector_measure α M) {f : ℕ → set α}
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) :
  v (⋃ i, f i) = ∑' i, v (f i) :=
(v.has_sum_of_disjoint_Union hf₁ hf₂).tsum_eq.symm

lemma ext_iff' (v w : vector_measure α M) :
  v = w ↔ ∀ i : set α, v i = w i :=
begin
  cases v, cases w, simpa [function.funext_iff],
end

lemma ext_iff (v w : vector_measure α M) :
  v = w ↔ ∀ i : set α, measurable_set i → v i = w i :=
begin
  split,
  { rintro rfl _ _, refl },
  { rw ext_iff',
    intros h i,
    by_cases hi : measurable_set i,
    { exact h i hi },
    { simp_rw [of_not_measurable_set _ hi] } }
end

@[ext] lemma ext {s t : vector_measure α M}
  (h : ∀ i : set α, measurable_set i → s i = t i) : s = t :=
(ext_iff s t).2 h

variables [t2_space M] {v : vector_measure α M} {f : ℕ → set α}

lemma has_sum_measure_Union [encodable β] {f : β → set α}
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) :
  has_sum (λ i, v (f i)) (v (⋃ i, f i)) :=
begin
  set g := λ i : ℕ, ⋃ (b : β) (H : b ∈ encodable.decode₂ β i), f b with hg,
  have hg₁ : ∀ i, measurable_set (g i),
  { exact λ _, measurable_set.Union (λ b, measurable_set.Union_Prop $ λ _, hf₁ b) },
  have hg₂ : pairwise (disjoint on g),
  { exact encodable.Union_decode₂_disjoint_on hf₂ },
  have := v.of_disjoint_Union hg₁ hg₂,
  rw [hg, encodable.Union_decode₂] at this,

  have hg₃ : (λ (i : β), v (f i)) = (λ i, v (g (encodable.encode i))),
  { ext, rw hg, simp only,
    congr, ext y, simp only [exists_prop, mem_Union, option.mem_def],
    split,
    { intro hy,
      refine ⟨x, (encodable.decode₂_is_partial_inv _ _).2 rfl, hy⟩ },
    { rintro ⟨b, hb₁, hb₂⟩,
      rw (encodable.decode₂_is_partial_inv _ _) at hb₁,
      rwa ← encodable.encode_injective hb₁ } },

  rw [summable.has_sum_iff, this, ← tsum_Union_decode₂],
  { exact v.of_empty },
  { rw hg₃, change summable ((λ i, v (g i)) ∘ encodable.encode),
    rw function.injective.summable_iff encodable.encode_injective,
    { exact (v.has_sum_of_disjoint_Union hg₁ hg₂).summable },
    { intros x hx,
      convert v.of_empty,
      simp only [Union_eq_empty, option.mem_def, not_exists, mem_range] at ⊢ hx,
      intros i hi,
      exact false.elim ((hx i) ((encodable.decode₂_is_partial_inv _ _).1 hi)) } }
end

lemma measure_Union [encodable β] {f : β → set α}
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) :
  v (⋃ i, f i) = ∑' i, v (f i) :=
(has_sum_measure_Union hf₁ hf₂).tsum_eq.symm

lemma of_union {A B : set α}
  (h : disjoint A B) (hA : measurable_set A) (hB : measurable_set B) :
  v (A ∪ B) = v A + v B :=
begin
  rw [union_eq_Union, measure_Union, tsum_fintype, fintype.sum_bool, cond, cond],
  exacts [λ b, bool.cases_on b hB hA, pairwise_disjoint_on_bool.2 h]
end

lemma of_diff {A B : set α} (hA : measurable_set A) (hB : measurable_set B)
  (h : A ⊆ B) : v A + v (B \ A) = v B :=
begin
  rw [← of_union disjoint_diff hA (hB.diff hA), union_diff_cancel h],
  apply_instance,
end

lemma of_diff' {M : Type*} [add_comm_group M]
  [topological_space M] [t2_space M] {v : vector_measure α M}
  {A B : set α} (hA : measurable_set A) (hB : measurable_set B)
  (h : A ⊆ B) : v (B \ A) = v B - (v A) :=
begin
  rw [← of_diff hA hB h, add_sub_cancel'],
  apply_instance,
end

lemma of_Union_nonneg {M : Type*} [topological_space M]
  [ordered_add_comm_monoid M] [order_closed_topology M]
  {v : vector_measure α M} (hf₁ : ∀ i, measurable_set (f i))
  (hf₂ : pairwise (disjoint on f)) (hf₃ : ∀ i, 0 ≤ v (f i)) :
  0 ≤ v (⋃ i, f i) :=
(v.of_disjoint_Union hf₁ hf₂).symm ▸ tsum_nonneg hf₃

lemma of_Union_nonpos {M : Type*} [topological_space M]
  [ordered_add_comm_monoid M] [order_closed_topology M]
  {v : vector_measure α M} (hf₁ : ∀ i, measurable_set (f i))
  (hf₂ : pairwise (disjoint on f)) (hf₃ : ∀ i, v (f i) ≤ 0) :
  v (⋃ i, f i) ≤ 0 :=
(v.of_disjoint_Union hf₁ hf₂).symm ▸ tsum_nonpos hf₃

lemma of_nonneg_disjoint_union_eq_zero {s : signed_measure α} {A B : set α}
  (h : disjoint A B) (hA₁ : measurable_set A) (hB₁ : measurable_set B)
  (hA₂ : 0 ≤ s A) (hB₂ : 0 ≤ s B)
  (hAB : s (A ∪ B) = 0) : s A = 0 :=
begin
  rw of_union h hA₁ hB₁ at hAB,
  linarith,
  apply_instance,
end

lemma of_nonpos_disjoint_union_eq_zero {s : signed_measure α} {A B : set α}
  (h : disjoint A B) (hA₁ : measurable_set A) (hB₁ : measurable_set B)
  (hA₂ : s A ≤ 0) (hB₂ : s B ≤ 0)
  (hAB : s (A ∪ B) = 0) : s A = 0 :=
begin
  rw of_union h hA₁ hB₁ at hAB,
  linarith,
  apply_instance,
end

lemma summable_to_real {f : α → ℝ≥0∞} (hf : ∀ a, f a ≠ ∞) (hsum : ∑' x, f x ≠ ∞) :
  summable (λ x, (f x).to_real) :=
begin
  lift f to α → ℝ≥0 using hf,
  rw ennreal.tsum_coe_ne_top_iff_summable_coe at hsum,
  simp [hsum],
end

lemma summable_measure {μ : measure α} [hμ : finite_measure μ]
  (hf₁ : ∀ (i : ℕ), measurable_set (f i))
  (hf₂ : pairwise (disjoint on f)) :
  summable (λ x, (μ (f x)).to_real) :=
begin
  apply summable_to_real,
  { intro, exact ne_of_lt (measure_lt_top _ _) },
  { rw ← measure_theory.measure_Union hf₂ hf₁,
    exact ne_of_lt (measure_lt_top _ _) }
end

end

/-- A finite measure coerced into a real function is a signed measure. -/
def of_measure (μ : measure α) [hμ : finite_measure μ] : signed_measure α :=
{ measure_of := λ i : set α, if measurable_set i then (μ.measure_of i).to_real else 0,
  empty := by simp [μ.empty],
  not_measurable := λ _ hi, if_neg hi,
  m_Union :=
  begin
    intros _ hf₁ hf₂,
    rw [μ.m_Union hf₁ hf₂, ennreal.tsum_to_real_eq, if_pos (measurable_set.Union hf₁),
        summable.has_sum_iff],
    { congr, ext n, rw if_pos (hf₁ n) },
    { refine @summable_of_nonneg_of_le _ (ennreal.to_real ∘ μ ∘ f) _ _ _ _,
      { intro, split_ifs,
        exacts [ennreal.to_real_nonneg, le_refl _] },
      { intro, split_ifs,
        exacts [le_refl _, ennreal.to_real_nonneg] },
        exact summable_measure hf₁ hf₂ },
    { intros a ha,
      apply ne_of_lt hμ.measure_univ_lt_top,
      rw [eq_top_iff, ← ha, outer_measure.measure_of_eq_coe, coe_to_outer_measure],
      exact measure_mono (set.subset_univ _) }
  end }

lemma of_measure_apply_measurable {μ : measure α} [finite_measure μ]
  {i : set α} (hi : measurable_set i) :
  of_measure μ i = (μ i).to_real :=
if_pos hi

lemma of_measure_apply_not_measurable {μ : measure α} [finite_measure μ]
  {i : set α} (hi : ¬ measurable_set i) :
  of_measure μ i = 0 :=
if_neg hi

variables {M : Type*} [add_comm_group M] [topological_space M]

/-- The zero signed measure. -/
def zero : vector_measure α M :=
⟨0, rfl, λ _ _, rfl, λ _ _ _, has_sum_zero⟩

instance : has_zero (vector_measure α M) := ⟨zero⟩
instance : inhabited (vector_measure α M) := ⟨0⟩

@[simp]
lemma zero_apply (i : set α) : (0 : vector_measure α M) i = 0 := rfl

section

variables [topological_add_group M]

/-- The negative of a vector measure is a vector measure. -/
def neg (v : vector_measure α M) : vector_measure α M :=
{ measure_of := -v,
  empty := by simp,
  not_measurable := λ _ hi, by simp [v.of_not_measurable_set hi],
  m_Union := λ f hf₁ hf₂,
    has_sum.neg $ v.has_sum_of_disjoint_Union hf₁ hf₂ }

/-- The sum of two vector measure is a vector measure. -/
def add (v w : vector_measure α M) : vector_measure α M :=
{ measure_of := v + w,
  empty := by simp,
  not_measurable := λ _ hi,
    by simp [v.of_not_measurable_set hi, w.of_not_measurable_set hi],
  m_Union := λ f hf₁ hf₂,
    has_sum.add (v.has_sum_of_disjoint_Union hf₁ hf₂)
      (w.has_sum_of_disjoint_Union hf₁ hf₂) }

instance : has_add (vector_measure α M) := ⟨add⟩
instance : has_neg (vector_measure α M) := ⟨neg⟩

@[simp]
lemma neg_apply {v : vector_measure α M} (i : set α) :
  (-v) i = - v i := rfl

@[simp]
lemma add_apply {v w : vector_measure α M} (i : set α) :
  (v + w) i = v i + w i := rfl

instance : add_comm_group (vector_measure α M) :=
{ add := (+), zero := (0),
  neg := vector_measure.neg,
  add_assoc := by { intros, ext i; simp [add_assoc] },
  zero_add := by { intros, ext i; simp },
  add_zero := by { intros, ext i; simp },
  add_comm := by { intros, ext i; simp [add_comm] },
  add_left_neg := by { intros, ext i, simp } } .

end

/-- Given two finite measures `μ, ν`, `of_sub_measure μ ν` is the signed measure
corresponding to the function `μ - ν`. -/
def of_sub_measure (μ ν : measure α) [hμ : finite_measure μ] [hν : finite_measure ν] :
  signed_measure α :=
of_measure μ + - of_measure ν

lemma of_sub_measure_apply {μ ν : measure α} [finite_measure μ] [finite_measure ν]
  {i : set α} (hi : measurable_set i) :
  of_sub_measure μ ν i = (μ i).to_real - (ν i).to_real :=
begin
  rw [of_sub_measure, add_apply, neg_apply, of_measure_apply_measurable hi,
      of_measure_apply_measurable hi, sub_eq_add_neg]
end

section

variables {R : Type*} [ring R] [module R M]
variables [topological_space R] [has_continuous_smul R M]

/-- Given a real number `r` and a signed measure `s`, `smul r s` is the signed
measure corresponding to the function `r • s`. -/
def smul
  (r : R) (v : vector_measure α M) : vector_measure α M :=
{ measure_of := r • v,
  empty := by simp,
  not_measurable := λ _ hi, by simp [v.of_not_measurable_set hi],
  m_Union := λ _ hf₁ hf₂,
    has_sum.smul (v.has_sum_of_disjoint_Union hf₁ hf₂) }

instance : has_scalar R (vector_measure α M) := ⟨smul⟩

@[simp]
lemma smul_apply {v : vector_measure α M} {r : R} (i : set α) :
  (r • v) i = r • v i := rfl

instance [topological_add_group M] : module R (vector_measure α M) :=
{ one_smul := by { intros, ext i; simp [one_smul] },
  mul_smul := by { intros, ext i; simp [mul_smul] },
  smul_add := by { intros, ext i; simp [smul_add] },
  smul_zero := by { intros, ext i; simp [smul_zero] },
  add_smul := by { intros, ext i; simp [add_smul] },
  zero_smul := by { intros, ext i; simp [zero_smul] } } .

end

end vector_measure

end measure_theory
